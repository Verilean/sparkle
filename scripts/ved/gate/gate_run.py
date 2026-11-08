#!/usr/bin/env python3
"""VED release gate, compile stage: per-file and per-row compile measurement.

Runs inside a kjob Pod at the repo root of the commit being measured (main or
the candidate), under `kjob lake env`, so `lake` and `lean` are on PATH:

    kjob lake env python3 -I gate_run.py --inv INVENTORY.tsv --out OUT [--cold]

Denominator: every row of the fixed inventory (327).  A row whose file is not
in this checkout is `absent`; a row whose command can not be located is
`not-located`.  Neither is dropped.

Stages (all outputs under OUT, nothing in the source tree):
  build   `lake build` of the union of the files' imports.  With --cold the
          job-local .lake/build is removed first (cold); the same build is
          then repeated (warm, no-op).  Wall and peak RSS for each.
  file    each original file: `lean FILE` (its own compile, imports built).
          Wall, peak RSS, exit, error count.  Peak memory is per FILE only.
  probe   a copy of each file in which every inventory command is wrapped as
              #eval IO.println "@@VEDGATE BEGIN R<n>"
              set_option profiler true in set_option profiler.threshold 0 in <command>
              #eval IO.println "@@VEDGATE END R<n>"
          One compile gives each row's printed SV (stdout between the markers)
          and its profiler categories (elaboration, type checking = kernel,
          compilation, ...).  Files written by #writeDesign/#writeVerilogDesign
          are copied out after the compile.  Time not attributed to a profiler
          category is not split further (reported as the file total only).

Output: OUT/rows.tsv, OUT/files.tsv, OUT/build.tsv, OUT/sv/R<n>.sv, logs.
"""
import argparse
import csv
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u0_gen import scan_source  # noqa: E402  (same scanner as U0)

BEGIN = "@@VEDGATE BEGIN R"
END = "@@VEDGATE END R"
PROF = re.compile(r"(?:^|\binfo: )([A-Za-z][A-Za-z .]*?) took ([0-9.]+)(ms|s)\b")
WRITE_CMDS = {"#writeDesign": 1, "#writeVerilogDesign": 1}  # index of the SV path argument


def timed(cmd, log, cwd=None):
    t0 = time.monotonic()
    with open(log, "w") as fh:
        p = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT, cwd=cwd)
        _, status, ru = os.wait4(p.pid, 0)
    wall = time.monotonic() - t0
    return os.waitstatus_to_exitcode(status), round(wall, 2), ru.ru_maxrss  # KiB


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def imports_of(text):
    return re.findall(r"(?m)^\s*(?:public\s+)?import\s+(\S+)", text)


def str_args(args):
    return re.findall(r'"((?:[^"\\]|\\.)*)"', args or "")


def probe_text(text, rows_here):
    """Insert the markers and the profiler prefix; returns (text, located rows)."""
    lines = text.splitlines()
    ins_before, ins_after, prefix, located = {}, {}, {}, {}
    for r in rows_here:
        sc = scan_source(text, int(r["line"]), r["command"], r["top"])
        if sc["cmd_index"] is None:
            continue
        i, j = sc["cmd_index"], sc["end_index"]
        located[r["row"]] = sc
        ins_before.setdefault(i, []).append(f'#eval IO.println "{BEGIN}{r["row"]}"')
        prefix[i] = True
        ins_after.setdefault(j, []).append(f'#eval IO.println "{END}{r["row"]}"')
    out = []
    for k, ln in enumerate(lines + [""]):
        out += ins_after.get(k, [])
        if k == len(lines):
            break
        out += ins_before.get(k, [])
        if prefix.get(k):
            ind = ln[: len(ln) - len(ln.lstrip())]
            ln = ind + "set_option profiler true in set_option profiler.threshold 0 in " + ln.lstrip()
        out.append(ln)
    return "\n".join(out) + "\n", located


def split_probe(stdout):
    """row -> (lines between the markers)"""
    seg, cur = {}, None
    for ln in stdout.splitlines():
        if ln.startswith(BEGIN):
            cur = ln[len(BEGIN):].strip(); seg[cur] = []; continue
        if ln.startswith(END):
            cur = None; continue
        if cur is not None:
            seg[cur].append(ln)
    return seg


def prof_of(lines):
    cats = {}
    for ln in lines:
        m = PROF.search(ln)
        if m:
            v = float(m.group(2)) / (1000.0 if m.group(3) == "ms" else 1.0)
            cats[m.group(1).strip()] = round(cats.get(m.group(1).strip(), 0.0) + v, 4)
    return cats


def sv_of(lines):
    keep = []
    for ln in lines:
        if PROF.search(ln) or re.search(r":\d+:\d+: (info|warning|error)", ln):
            continue
        if ln.startswith("-- ") and "successfully generated" in ln:
            continue
        keep.append(ln)
    s = "\n".join(keep).strip("\n")
    return s + "\n" if s else ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inv", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--cold", action="store_true")
    ap.add_argument("--files", default="", help="smoke only: comma-separated files (not a gate result)")
    a = ap.parse_args()
    out = a.out
    for d in ("logs/file", "logs/probe", "probe", "sv"):
        os.makedirs(os.path.join(out, d), exist_ok=True)
    with open(a.inv) as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    for i, r in enumerate(rows, 1):
        r["row"] = str(i)
    head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    meta = {"head": head, "rows": len(rows), "node": os.uname().nodename, "cold": a.cold,
            "cpus": os.cpu_count(), "inventory_sha256": sha(a.inv)}
    if a.files:
        keep = set(a.files.split(","))
        rows = [r for r in rows if r["file"] in keep]
        meta["smoke_subset"] = sorted(keep)
    files = sorted({r["file"] for r in rows})
    present = [f for f in files if os.path.isfile(f)]
    texts = {f: open(f).read() for f in present}

    # ---- build stage
    mods = sorted({m for f in present for m in imports_of(texts[f])})
    with open(os.path.join(out, "imports.txt"), "w") as fh:
        fh.write("\n".join(mods) + "\n")
    btab = []
    if a.cold:
        shutil.rmtree(".lake/build", ignore_errors=True)
    for phase in ("cold" if a.cold else "first", "warm"):
        rc, wall, peak = timed(["lake", "build", *mods], os.path.join(out, f"logs/build-{phase}.log"))
        btab.append({"phase": phase, "exit": rc, "wall_s": wall, "peak_kib": peak, "modules": len(mods)})
        print(f"GATEBUILD {phase} exit={rc} wall={wall}s peak={peak}KiB", flush=True)

    # ---- file + probe stages
    ftab, rtab = [], []
    by_file = {}
    for r in rows:
        by_file.setdefault(r["file"], []).append(r)
    for f in files:
        rs = by_file[f]
        if f not in texts:
            for r in rs:
                rtab.append({"row": r["row"], "file": f, "command": r["command"], "top": r["top"], "status": "absent"})
            ftab.append({"file": f, "status": "absent"})
            continue
        key = f.replace("/", "__")
        rc, wall, peak = timed(["lean", f], os.path.join(out, f"logs/file/{key}.log"))
        flog = open(os.path.join(out, f"logs/file/{key}.log")).read()
        ptxt, located = probe_text(texts[f], rs)
        ppath = os.path.join(out, "probe", f)
        os.makedirs(os.path.dirname(ppath), exist_ok=True)
        with open(ppath, "w") as fh:
            fh.write(ptxt)
        for r in rs:  # stale outputs of write commands must not be credited
            if r["command"] in WRITE_CMDS:
                sa = str_args(r.get("args"))
                if len(sa) > WRITE_CMDS[r["command"]] - 1 and os.path.isfile(sa[0]):
                    os.remove(sa[0])
        prc, pwall, ppeak = timed(["lean", ppath], os.path.join(out, f"logs/probe/{key}.log"))
        plog = open(os.path.join(out, f"logs/probe/{key}.log")).read()
        ftab.append({"file": f, "status": "ok" if rc == 0 else "error", "exit": rc, "wall_s": wall,
                     "peak_kib": peak, "errors": len(re.findall(r": error(?:\([^)\s]*\))?:", flog)),
                     "probe_exit": prc, "probe_wall_s": pwall, "probe_peak_kib": ppeak, "rows": len(rs)})
        seg = split_probe(plog)
        for r in rs:
            rec = {"row": r["row"], "file": f, "command": r["command"], "top": r["top"]}
            if r["row"] not in located:
                rec["status"] = "not-located"; rtab.append(rec); continue
            lines = seg.get(r["row"])
            if lines is None:
                rec["status"] = "no-markers"; rtab.append(rec); continue
            errs = [ln for ln in lines if re.search(r": error(?:\([^)\s]*\))?:", ln)]
            cats = prof_of(lines)
            rec["prof"] = json.dumps(cats, sort_keys=True)
            rec["elab_s"] = cats.get("elaboration", "")
            rec["kernel_s"] = cats.get("type checking", "")
            if r["command"] in WRITE_CMDS:
                sa = str_args(r.get("args"))
                src = sa[0] if sa else ""
                sv = open(src).read() if src and os.path.isfile(src) else ""
            else:
                sv = sv_of(lines)
            if sv:
                p = os.path.join(out, "sv", f"R{r['row']}.sv")
                with open(p, "w") as fh:
                    fh.write(sv)
                rec["sv_sha256"] = sha(p)
                rec["sv_lines"] = sv.count("\n")
            rec["status"] = "error" if errs else ("ok" if sv else "no-sv")
            rec["errors"] = len(errs)
            rtab.append(rec)
        print(f"GATEFILE {f} exit={rc} wall={wall}s peak={peak}KiB probe_exit={prc} rows={len(rs)}", flush=True)

    def dump(name, tab, cols):
        with open(os.path.join(out, name), "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", extrasaction="ignore")
            w.writeheader()
            for t in tab:
                w.writerow(t)
    dump("build.tsv", btab, ["phase", "exit", "wall_s", "peak_kib", "modules"])
    dump("files.tsv", ftab, ["file", "status", "exit", "wall_s", "peak_kib", "errors", "probe_exit",
                             "probe_wall_s", "probe_peak_kib", "rows"])
    rtab.sort(key=lambda t: int(t["row"]))
    dump("rows.tsv", rtab, ["row", "file", "command", "top", "status", "errors", "elab_s", "kernel_s",
                            "prof", "sv_lines", "sv_sha256"])
    meta["status_counts"] = {}
    for t in rtab:
        meta["status_counts"][t["status"]] = meta["status_counts"].get(t["status"], 0) + 1
    with open(os.path.join(out, "meta.json"), "w") as fh:
        json.dump(meta, fh, indent=1)
    print("GATEDONE " + json.dumps(meta["status_counts"], sort_keys=True), flush=True)
    return 0 if len(rtab) == len(rows) and not a.files else 3


if __name__ == "__main__":
    sys.exit(main())
