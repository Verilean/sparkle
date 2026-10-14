#!/usr/bin/env python3
"""The process-global depth cell under the REAL Lean language server.

WRITTEN, NOT RUN (round par/k-depth). Python standard library only; it starts
`lake serve` (the language server of the installed toolchain) in the
repository root and talks LSP over its stdin / stdout.

    scripts/shipping-coverage/cgrun.sh -n lsdepth -m 3G -t 900 -- \
      python3 scripts/shipping-coverage/ls_depth_probe.py --mode nocheck --hold-ms 8000 --trials 3
    … --mode check --hold-ms 8000 --trials 5

Requires a completed `lake build Sparkle` (otherwise the server builds the
imports itself: do NOT run next to another build). Nothing is installed.

One trial:
  1. start `lake serve`; `initialize`, `initialized`;
  2. `textDocument/didOpen` with the text of
     scripts/shipping-coverage/ls_depth_probe.lean (MODE and HOLDMS replaced);
  3. wait for the marker file .lake/build/gen/ls-depth/entered: the command
     `#ls_depth "long"` is now INSIDE the synthesis entry (depth 1), holding;
  4. `textDocument/didChange` (version 2): `def lsAnchor : Nat := 0` -> `:= 1`,
     a definition BEFORE the commands;
  5. wait until the log has a second `long@… ENTRY` line (the re-elaborated
     command) or the timeout;
  6. `shutdown`, `exit`; print the log and the verdict.

Verdict per trial (docs/parallel/K-depth-cell.md, section 5):
  REPRODUCED          the second `long` ENTRY, or a `quick` ENTRY, has depth >= 1:
                      a command of the new version started while the cancelled
                      run of the old version was still inside the entry
  SERIALISED          second ENTRY has depth 0 and its time is AFTER the first
                      run's EXIT: nothing overlapped in this trial
  INCONCLUSIVE        no second ENTRY before the timeout, or the marker never
                      appeared (the file did not elaborate: see the diagnostics)
The script exits 0 always; the last line is `LSDEPTH SUMMARY …`.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SRC = os.path.join(ROOT, "scripts", "shipping-coverage", "ls_depth_probe.lean")
OUT = os.path.join(ROOT, ".lake", "build", "gen", "ls-depth")
LOG = os.path.join(OUT, "log.txt")
MARK = os.path.join(OUT, "entered")
URI = "file://" + SRC


class Server:
    def __init__(self):
        self.p = subprocess.Popen(["lake", "serve"], cwd=ROOT, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.msgs = []
        self.lock = threading.Lock()
        self.next_id = 1
        threading.Thread(target=self._read, daemon=True).start()
        threading.Thread(target=self._drain_err, daemon=True).start()

    def _drain_err(self):
        for _ in iter(self.p.stderr.readline, b""):
            pass

    def _read(self):
        f = self.p.stdout
        while True:
            length = None
            while True:
                line = f.readline()
                if not line:
                    return
                line = line.strip()
                if not line:
                    break
                if line.lower().startswith(b"content-length:"):
                    length = int(line.split(b":")[1])
            if length is None:
                continue
            body = f.read(length)
            try:
                msg = json.loads(body.decode("utf-8"))
            except ValueError:
                continue
            with self.lock:
                self.msgs.append(msg)
            # a request FROM the server (it has an id and a method): answer null
            if "id" in msg and "method" in msg:
                self._send({"jsonrpc": "2.0", "id": msg["id"], "result": None})

    def _send(self, obj):
        data = json.dumps(obj).encode("utf-8")
        try:
            self.p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data)
            self.p.stdin.flush()
        except (BrokenPipeError, OSError):
            pass

    def request(self, method, params):
        i = self.next_id
        self.next_id += 1
        self._send({"jsonrpc": "2.0", "id": i, "method": method, "params": params})
        return i

    def notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def wait_response(self, i, timeout):
        end = time.time() + timeout
        while time.time() < end:
            with self.lock:
                for m in self.msgs:
                    if m.get("id") == i and "method" not in m:
                        return m
            time.sleep(0.05)
        return None

    def diagnostics(self):
        out = []
        with self.lock:
            for m in self.msgs:
                if m.get("method") == "textDocument/publishDiagnostics":
                    p = m.get("params", {})
                    for d in p.get("diagnostics", []):
                        out.append((p.get("version"), d.get("severity"),
                                    str(d.get("message", "")).replace("\n", " ")[:200]))
        return out

    def stop(self):
        i = self.request("shutdown", None)
        self.wait_response(i, 5)
        self.notify("exit", None)
        try:
            self.p.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.p.kill()


def read_log():
    try:
        with open(LOG, encoding="utf-8") as f:
            return [l.rstrip("\n") for l in f if l.strip()]
    except OSError:
        return []


def parse(line):
    m = re.match(r"^(\S+)@(\d+) (\S+) t=(\d+)(?: depth=(\d+))?", line)
    if not m:
        return None
    return {"tag": m.group(1), "run": m.group(1) + "@" + m.group(2), "ev": m.group(3),
            "t": int(m.group(4)), "depth": None if m.group(5) is None else int(m.group(5))}


def wait_for(pred, timeout):
    end = time.time() + timeout
    while time.time() < end:
        if pred():
            return True
        time.sleep(0.05)
    return False


def trial(n, mode, hold_ms, timeout):
    os.makedirs(OUT, exist_ok=True)
    for p in (LOG, MARK):
        if os.path.exists(p):
            os.remove(p)
    with open(SRC, encoding="utf-8") as f:
        text1 = f.read().replace(" MODE HOLDMS ", " %s %d " % (mode, hold_ms)).replace(" MODE 0 ", " %s 0 " % mode)
    text2 = text1.replace("def lsAnchor : Nat := 0", "def lsAnchor : Nat := 1")
    if text2 == text1 or " MODE " in text1:
        print("LSDEPTH trial %d: INCONCLUSIVE the text substitutions did not apply" % n)
        return "INCONCLUSIVE"
    print("LSDEPTH trial %d: START lake serve (mode=%s hold=%d ms)" % (n, mode, hold_ms), flush=True)
    s = Server()
    try:
        i = s.request("initialize", {"processId": os.getpid(), "rootUri": "file://" + ROOT,
                                     "capabilities": {}})
        if s.wait_response(i, 60) is None:
            print("LSDEPTH trial %d: INCONCLUSIVE no answer to initialize" % n)
            return "INCONCLUSIVE"
        s.notify("initialized", {})
        print("LSDEPTH trial %d: START didOpen (version 1)" % n, flush=True)
        s.notify("textDocument/didOpen", {"textDocument": {
            "uri": URI, "languageId": "lean4", "version": 1, "text": text1}})
        if not wait_for(lambda: os.path.exists(MARK), timeout):
            print("LSDEPTH trial %d: INCONCLUSIVE the long command never reached its hold; diagnostics: %s"
                  % (n, s.diagnostics()[:6]))
            return "INCONCLUSIVE"
        time.sleep(0.3)
        print("LSDEPTH trial %d: START didChange (version 2: lsAnchor 0 -> 1) while the long command holds" % n,
              flush=True)
        s.notify("textDocument/didChange", {
            "textDocument": {"uri": URI, "version": 2},
            "contentChanges": [{"text": text2}]})

        def second_entry():
            evs = [parse(l) for l in read_log()]
            return len([e for e in evs if e and e["tag"] == "long" and e["ev"] == "ENTRY"]) >= 2

        got = wait_for(second_entry, timeout)
        # give the quick command of the new version a moment as well
        time.sleep(1.0)
    finally:
        s.stop()
    lines = read_log()
    for l in lines:
        print("LSDEPTH trial %d log: %s" % (n, l))
    for d in s.diagnostics()[:12]:
        print("LSDEPTH trial %d diagnostic: version=%s severity=%s %s" % ((n,) + d))
    evs = [e for e in (parse(l) for l in lines) if e]
    entries = [e for e in evs if e["ev"] == "ENTRY"]
    longs = [e for e in entries if e["tag"] == "long"]
    if not got or len(longs) < 2:
        print("LSDEPTH trial %d: INCONCLUSIVE no second ENTRY of the long command within %d s" % (n, timeout))
        return "INCONCLUSIVE"
    first = longs[0]
    later = [e for e in entries if e["t"] > first["t"]]
    nonzero = [e for e in later if e["depth"] and e["depth"] >= 1]
    exits = [e for e in evs if e["ev"] == "EXIT" and e["run"] == first["run"]]
    exit_t = exits[0]["t"] if exits else None
    if nonzero:
        print("LSDEPTH trial %d: REPRODUCED %s entered at depth %d (first run's EXIT: %s)"
              % (n, nonzero[0]["run"], nonzero[0]["depth"], exit_t))
        return "REPRODUCED"
    if exit_t is not None and exit_t <= longs[1]["t"]:
        print("LSDEPTH trial %d: SERIALISED the old run's EXIT (t=%d) is before the new ENTRY (t=%d), depth 0"
              % (n, exit_t, longs[1]["t"]))
        return "SERIALISED"
    print("LSDEPTH trial %d: INCONCLUSIVE depth 0 at the new ENTRY but no earlier EXIT of the old run in the log"
          % n)
    return "INCONCLUSIVE"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["nocheck", "check"], default="nocheck")
    ap.add_argument("--hold-ms", type=int, default=8000)
    ap.add_argument("--trials", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=180)
    a = ap.parse_args()
    res = []
    for n in range(1, a.trials + 1):
        try:
            res.append(trial(n, a.mode, a.hold_ms, a.timeout))
        except Exception as e:  # recorded, never fatal
            print("LSDEPTH trial %d: INCONCLUSIVE script error: %r" % (n, e))
            res.append("INCONCLUSIVE")
    print("LSDEPTH SUMMARY mode=%s hold=%d ms: reproduced=%d serialised=%d inconclusive=%d of %d"
          % (a.mode, a.hold_ms, res.count("REPRODUCED"), res.count("SERIALISED"),
             res.count("INCONCLUSIVE"), len(res)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
