#!/usr/bin/env python3
"""U0 runner: run generated cases in isolation and assemble the result tables.

Reviewer change request 2026-11-08, P1-3.  Design:
docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md (section 3).

Usage (repo root of the worktree being measured; OUT outside the tree):
  u0_run.py --out OUT case ROW SETTING [SV_GROUP]
  u0_run.py --out OUT list ROWS.txt          # lines "ROW SETTING [SV_GROUP]"
  u0_run.py --out OUT smoke-file FILE        # an existing deep test file as-is
  u0_run.py --out OUT smoke-split FILE       # one variant per #verify_elab_deep
  (internal) u0_run.py _exec DIR -- CMD...   # one isolated process tree

Environment
  U0_LEAN          the per-case command (default "kjob lake env lean"), split by shlex
  U0_TMO           wall-clock limit per case in seconds (default 1800)
  U0_GRACE         seconds between SIGTERM and SIGKILL of the case's group (default 10)
  U0_RLIMIT_AS_KB  optional RLIMIT_AS per case (default 0 = off).  It is NOT a
                   memory limit substitute: the outer limit is the Pod's -m.
  U0_GEN_PY        the generator/classifier (default: u0_gen.py next to this file)
  U0_INV_COMMIT / U0_INV_BLOB   inventory pin passed to the generator
  REDO=1           always start a new attempt (the old one is kept, never mixed)

(a) environment: every SPARKLE_* variable is removed, then the case's
    explicit settings (case.env) and SPARKLE_DEEP_TRACE=<case>/stages.log are
    set; the effective SPARKLE_* set and the names cleared are recorded.
(b) run identity: src SHA + dirty-tree hash + toolchain + inventory pin +
    harness hash + runner settings (= run_id), and per case the case-file hash
    and effective settings.  Reuse is decided BEFORE anything is written into
    an attempt: an attempt is reused only when its identity is identical and
    it finished; otherwise a new attempt-NNN directory is used.  Result tables
    are rebuilt per run_id from the latest finished attempt of each case, so
    rows of other SHAs/settings are never mixed in and REDO never double-counts.
(c) each case runs in a new session (process group) under a helper process
    that is a child subreaper; on timeout the whole group gets SIGTERM, then
    SIGKILL; strays (group members, re-parented descendants) are killed and
    reaping is verified.  A signal is recorded as signal_<n>; an exit status
    >= 128 from a wrapper as exit_<n>(signal_unknown); never "oom" from SIGKILL
    alone (memory evidence = cgroup oom_kill counter or allocator text).
    peak_rss_kb = RUSAGE_CHILDREN ru_maxrss of the helper: the largest single
    reaped descendant (not the wrapper, not a sum); cgroup memory.peak is
    recorded when the kernel allows a per-case reset.
(d) a generator failure, a missing run.txt and a classifier failure are rows
    with invocation=harness-error; the run continues; the final line is
    `U0 SUMMARY ... COMPLETE|INCOMPLETE` and the exit status is 3 when
    incomplete.
"""
import ctypes
import glob
import hashlib
import json
import os
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.environ.get("U0_GEN_PY", os.path.join(HERE, "u0_gen.py"))
CLEAR_PREFIX = "SPARKLE_"


def sha256_bytes(*parts):
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else p.encode())
        h.update(b"\0")
    return h.hexdigest()


def git(repo, *args):
    return subprocess.run(["git", *args], cwd=repo, capture_output=True, check=True).stdout


# ------------------------------------------------------------ isolation

PR_SET_CHILD_SUBREAPER = 36


def set_subreaper():
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        return libc.prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) == 0
    except Exception:
        return False


def proc_table():
    """pid -> (ppid, pgid) for every live process."""
    out = {}
    for p in glob.glob("/proc/[0-9]*/stat"):
        try:
            s = open(p).read()
        except OSError:
            continue
        rest = s[s.rfind(")") + 2:].split()
        if len(rest) < 3 or rest[0] == "Z":
            continue
        out[int(p.split("/")[2])] = (int(rest[1]), int(rest[2]))
    return out


def tree_of(me, pgid):
    """Live processes in group `pgid` or descending from `me`."""
    tab = proc_table()
    kids = {}
    for pid, (pp, _) in tab.items():
        kids.setdefault(pp, []).append(pid)
    desc, st = set(), [me]
    while st:
        for c in kids.get(st.pop(), []):
            if c not in desc:
                desc.add(c); st.append(c)
    return sorted({pid for pid, (_, g) in tab.items() if g == pgid} | desc)


def reap_all():
    n = 0
    while True:
        try:
            pid, _ = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return n
        if pid == 0:
            return n
        n += 1


def cgroup_dir():
    try:
        for ln in open("/proc/self/cgroup"):
            if ln.startswith("0::"):
                return "/sys/fs/cgroup" + ln.strip()[3:]
    except OSError:
        pass
    return None


def oom_kills(cg):
    try:
        for ln in open(os.path.join(cg, "memory.events")):
            k, v = ln.split()
            if k == "oom_kill":
                return int(v)
    except (OSError, TypeError, ValueError):
        pass
    return None


def exec_case(d, cmd, tmo, grace, rlimit_kb):
    sub = set_subreaper()
    me = os.getpid()
    cg = cgroup_dir()
    oom0 = oom_kills(cg)
    peak_fd = None
    try:
        peak_fd = os.open(os.path.join(cg, "memory.peak"), os.O_RDWR)
        os.write(peak_fd, b"reset\n")       # per-fd reset (Linux >= 6.12)
    except (OSError, TypeError):
        if peak_fd is not None:
            os.close(peak_fd)
        peak_fd = None

    def pre():
        if rlimit_kb:
            resource.setrlimit(resource.RLIMIT_AS, (rlimit_kb * 1024, rlimit_kb * 1024))
    t0 = time.monotonic()
    timed_out, how = False, ""
    harness_error = ""
    with open(os.path.join(d, "stdout.txt"), "w") as fo, open(os.path.join(d, "stderr.txt"), "w") as fe:
        try:
            p = subprocess.Popen(cmd, stdout=fo, stderr=fe, stdin=subprocess.DEVNULL,
                                 start_new_session=True, preexec_fn=pre)
        except OSError as e:
            p = None
            harness_error = f"runner could not start: {e}"
        rc = ""
        if p is not None:
            pgid = p.pid
            try:
                rc = p.wait(timeout=tmo)
            except subprocess.TimeoutExpired:
                timed_out, how = True, "TERM"
                try:
                    os.killpg(pgid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    rc = p.wait(timeout=grace)
                except subprocess.TimeoutExpired:
                    how = "KILL"
                    try:
                        os.killpg(pgid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    rc = p.wait()
            # strays: anything left in the group or re-parented to us
            strays = [x for x in tree_of(me, pgid) if x != me]
            for x in strays:
                try:
                    os.kill(x, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            left = []
            for _ in range(100):
                reap_all()
                left = [x for x in tree_of(me, pgid) if x != me]
                if not left:
                    break
                time.sleep(0.05)
            reaped = "yes" if not left else "no:" + ",".join(map(str, left))
        else:
            strays, reaped = [], "n/a"
    wall = time.monotonic() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    if timed_out:
        term = f"timeout({how})"
    elif rc == "":
        term = "not-started"
    elif rc < 0:
        term = f"signal_{-rc}"
    elif rc >= 128:
        term = f"exit_{rc}(signal_unknown)"
    else:
        term = f"exit_{rc}"
    err = open(os.path.join(d, "stderr.txt"), errors="replace").read()
    out = open(os.path.join(d, "stdout.txt"), errors="replace").read()
    ev = []
    oom1 = oom_kills(cg)
    if oom0 is not None and oom1 is not None and oom1 > oom0:
        ev.append(f"cgroup_oom_kill+{oom1 - oom0}")
    if re.search(r"out of memory|std::bad_alloc|Cannot allocate memory", err + out):
        ev.append("allocator_text")
    cg_peak = "unavailable"
    if peak_fd is not None:
        try:
            os.lseek(peak_fd, 0, os.SEEK_SET)
            cg_peak = str(int(os.read(peak_fd, 64).decode().strip()) // 1024)
        except (OSError, ValueError):
            pass
        os.close(peak_fd)
    fields = [("rc", rc), ("term", term), ("timeout", "yes" if timed_out else "no"),
              ("wall_s", f"{wall:.1f}"), ("peak_rss_kb", ru.ru_maxrss),
              ("peak_rss_source", "rusage_children_maxrss(largest single reaped descendant)"
               + ("" if sub else ";no-subreaper")),
              ("cgroup_peak_kb", cg_peak), ("mem_evidence", ";".join(ev)), ("reaped", reaped),
              ("stray_killed", len(strays)), ("time_limit_s", tmo), ("rlimit_as_kb", rlimit_kb or "off"),
              ("harness_error", harness_error), ("cmd", " ".join(cmd))]
    with open(os.path.join(d, "run.txt"), "w") as f:
        for k, v in fields:
            f.write(f"{k}={v}\n")


# ------------------------------------------------------------ driver

class Runner:
    def __init__(self, repo, out):
        self.repo = os.path.realpath(repo)
        self.out = os.path.realpath(out)
        if self.out == self.repo or self.out.startswith(self.repo + os.sep):
            sys.exit("OUT must be outside the source tree")
        os.makedirs(os.path.join(self.out, "cases"), exist_ok=True)
        self.lean = shlex.split(os.environ.get("U0_LEAN", "kjob lake env lean"))
        self.tmo = int(os.environ.get("U0_TMO", "1800"))
        self.grace = int(os.environ.get("U0_GRACE", "10"))
        self.rlimit = int(os.environ.get("U0_RLIMIT_AS_KB", "0"))
        self.redo = bool(os.environ.get("REDO"))
        self.inv = []
        if os.environ.get("U0_INV_COMMIT"):
            self.inv += ["--commit", os.environ["U0_INV_COMMIT"]]
        if os.environ.get("U0_INV_BLOB"):
            self.inv += ["--blob", os.environ["U0_INV_BLOB"]]
        sha = git(self.repo, "rev-parse", "HEAD").decode().strip()
        dirty = sha256_bytes(git(self.repo, "status", "--porcelain=v1", "--untracked-files=all"),
                             git(self.repo, "diff", "HEAD", "--binary"))
        tc_path = os.path.join(self.repo, "lean-toolchain")
        toolchain = open(tc_path).read().strip() if os.path.exists(tc_path) else "missing"
        hh = sha256_bytes(open(GEN, "rb").read(), open(os.path.abspath(__file__), "rb").read())
        self.gid = {"src_sha": sha, "src_dirty_hash": dirty, "toolchain": toolchain,
                    "inv": " ".join(self.inv) or "default-pin", "harness_hash": hh,
                    "lean_cmd": " ".join(self.lean), "tmo": self.tmo, "grace": self.grace,
                    "rlimit_as_kb": self.rlimit}
        self.run_id = sha256_bytes(json.dumps(self.gid, sort_keys=True))[:16]
        self.stats = {"requested": 0, "ran": 0, "reused": 0, "not_run": 0, "harness_error": 0}
        self.keys = []
        self.last_gen_err = ""
        hdr = subprocess.run([sys.executable, "-I", GEN, "header"], capture_output=True, text=True)
        self.header = hdr.stdout.rstrip("\n").split("\t") if hdr.returncode == 0 else None
        if self.header is None:
            sys.exit(f"harness-error: generator header failed: {hdr.stderr.strip()}")

    def gen_cmd(self, *args):
        return [sys.executable, "-I", GEN, "--repo", self.repo, *self.inv, *args]

    def child_env(self, case_env_path, d):
        env = {k: v for k, v in os.environ.items() if not k.startswith(CLEAR_PREFIX)}
        cleared = sorted(k for k in os.environ if k.startswith(CLEAR_PREFIX))
        if case_env_path and os.path.exists(case_env_path):
            for ln in open(case_env_path):
                k, _, v = ln.rstrip("\n").partition("=")
                if k:
                    env[k] = v
        env["SPARKLE_DEEP_TRACE"] = os.path.join(d, "stages.log")
        eff = sorted(f"{k}={'<case>/stages.log' if k == 'SPARKLE_DEEP_TRACE' else v}"
                     for k, v in env.items() if k.startswith(CLEAR_PREFIX))
        return env, eff, cleared

    def attempts(self, root):
        return sorted(glob.glob(os.path.join(root, "attempt-[0-9][0-9][0-9]")))

    def new_attempt(self, root):
        n = len(self.attempts(root)) + 1
        while True:
            d = os.path.join(root, f"attempt-{n:03d}")
            try:
                os.makedirs(d)
                return d
            except FileExistsError:
                n += 1

    def error_row(self, row, setting, reason, attempt="", kind="row"):
        r = subprocess.run(self.gen_cmd("error-row", "--row", str(row), "--setting", setting,
                                        "--reason", reason, "--attempt", attempt, "--run-id", self.run_id),
                           capture_output=True, text=True)
        line = r.stdout.rstrip("\n")
        if r.returncode != 0 or len(line.split("\t")) != len(self.header):
            vals = {c: "" for c in self.header}
            vals.update(row=str(row), setting=setting, invocation="harness-error",
                        harness_error=reason, run_id=self.run_id, attempt=attempt,
                        strict_counted="no", deep_run_record="none")
            line = "\t".join(vals[c] for c in self.header)
        return line

    def is_harness_error(self, line, kind):
        hdr = self.ASIS_COLUMNS if kind == "smoke-asis" else self.header
        r = dict(zip(hdr, line.split("\t")))
        return r.get("invocation") == "harness-error" or bool(r.get("harness_error"))

    def finish(self, d, line, kind):
        with open(os.path.join(d, "row.tsv"), "w") as f:
            f.write(line + "\n")
        with open(os.path.join(d, "done"), "w") as f:
            f.write(kind + "\n")
        if self.is_harness_error(line, kind):
            self.stats["harness_error"] += 1
            with open(os.path.join(self.out, "harness_errors.log"), "a") as f:
                f.write(f"{self.run_id}\t{d}\t{line[:300]}\n")

    def run_one(self, key, staging, kind, sv_group="", row="", setting="", direct_file=None):
        """`staging` holds the generated case (or None when gen failed)."""
        root = os.path.join(self.out, "cases", key)
        self.keys.append((key, kind))
        self.stats["requested"] += 1
        files = sorted(os.listdir(staging)) if staging else []
        blobs = [f.encode() + b"=" + open(os.path.join(staging, f), "rb").read() for f in files]
        if direct_file:
            blobs.append(b"direct=" + open(direct_file, "rb").read())
        case_hash = sha256_bytes(*blobs)
        env, eff, cleared = self.child_env(os.path.join(staging, "case.env") if staging else None, "<case>")
        ident = dict(self.gid, run_id=self.run_id, key=key, kind=kind, case_hash=case_hash,
                     effective_env=eff, lean_options="see meta.json")
        cmp_keys = sorted(k for k in ident if k not in ("attempt",))
        cmp = {k: ident[k] for k in cmp_keys}
        # reuse check BEFORE writing anything into an attempt directory
        if not self.redo:
            for a in reversed(self.attempts(root)):
                try:
                    old = json.load(open(os.path.join(a, "identity.json")))
                except (OSError, ValueError):
                    continue
                if {k: old.get(k) for k in cmp_keys} == cmp and os.path.exists(os.path.join(a, "done")):
                    self.stats["reused"] += 1
                    print(f"reuse {key} {os.path.basename(a)}")
                    if staging:
                        shutil.rmtree(staging, ignore_errors=True)
                    if self.is_harness_error(open(os.path.join(a, "row.tsv")).read().rstrip("\n"), kind):
                        self.stats["harness_error"] += 1
                    return
        d = self.new_attempt(root)
        for f in files:
            shutil.move(os.path.join(staging, f), os.path.join(d, f))
        if staging:
            shutil.rmtree(staging, ignore_errors=True)
        ident["attempt"] = os.path.basename(d)
        ident["cleared_env"] = cleared
        with open(os.path.join(d, "identity.json"), "w") as f:
            json.dump(ident, f, indent=1, sort_keys=True)
        try:
            if staging is None and not direct_file:
                line = self.error_row(row, setting, f"generator failed: {self.last_gen_err}", ident["attempt"])
                self.finish(d, line, kind)
                return
            meta = json.load(open(os.path.join(d, "meta.json"))) if os.path.exists(os.path.join(d, "meta.json")) else {}
            target = direct_file or os.path.join(d, "Case.lean")
            if direct_file or meta.get("run"):
                env, _, _ = self.child_env(os.path.join(d, "case.env"), d)
                h = subprocess.run([sys.executable, "-I", os.path.abspath(__file__), "_exec", d,
                                    "--tmo", str(self.tmo), "--grace", str(self.grace),
                                    "--rlimit", str(self.rlimit), "--", *self.lean, target],
                                   env=env, cwd=self.repo, capture_output=True, text=True)
                if h.returncode != 0:
                    with open(os.path.join(d, "exec.err"), "w") as f:
                        f.write(h.stdout + h.stderr)
                self.stats["ran"] += 1
            else:
                self.stats["not_run"] += 1
            if kind == "smoke-asis":
                line = self.asis_row(key, d, direct_file)
            else:
                c = subprocess.run(self.gen_cmd("classify", d, "--sv-group", sv_group),
                                   capture_output=True, text=True)
                line = c.stdout.rstrip("\n")
                if c.returncode != 0 or "\n" in line or len(line.split("\t")) != len(self.header):
                    line = self.error_row(row or key, setting or "-",
                                          f"classifier failed (rc={c.returncode}): {c.stderr.strip()[-200:]}",
                                          ident["attempt"])
            self.finish(d, line, kind)
            r = dict(zip(self.header, line.split("\t"))) if kind != "smoke-asis" else {}
            print(f"{key} {ident['attempt']} invocation={r.get('invocation', '-')} "
                  f"term={r.get('term', '-')} strict_counted={r.get('strict_counted', '-')}")
        except Exception as e:  # the run continues; the case is a harness-error row
            self.finish(d, self.error_row(row or key, setting or "-", f"runner exception: {e!r}",
                                          ident["attempt"]), kind)

    ASIS_COLUMNS = ["key", "file", "run_id", "attempt", "src_sha", "rc", "term", "timeout", "wall_s",
                    "peak_rss_kb", "reaped", "mem_evidence", "n_proven_msgs_observation", "n_errors",
                    "n_skipped", "invocation", "harness_error", "stdout_ref"]

    def asis_row(self, key, d, f):
        run = {}
        if os.path.exists(os.path.join(d, "run.txt")):
            for ln in open(os.path.join(d, "run.txt")):
                k, _, v = ln.rstrip("\n").partition("=")
                run[k] = v
        text = ""
        for n in ("stdout.txt", "stderr.txt"):
            p = os.path.join(d, n)
            if os.path.exists(p):
                text += open(p, errors="replace").read()
        he = run.get("harness_error", "") if run else "run.txt missing"
        vals = [key, os.path.relpath(f, self.repo), self.run_id, os.path.basename(d), self.gid["src_sha"],
                run.get("rc", ""), run.get("term", ""), run.get("timeout", ""), run.get("wall_s", ""),
                run.get("peak_rss_kb", ""), run.get("reaped", ""), run.get("mem_evidence", ""),
                str(len(re.findall(r"#verify_elab_deep \S+: PROVEN", text))),
                str(len(re.findall(r": error:", text))),
                str(len(re.findall(r"SKIPPED|replay skipped", text))),
                "harness-error" if he else "smoke-asis", he, os.path.join(d, "stdout.txt")]
        return "\t".join(v.replace("\t", " ") for v in vals)

    # -------- case kinds
    def case(self, row, setting, sv_group=""):
        key = f"R{int(row):03d}_{setting}" if str(row).isdigit() else f"Rbad_{row}_{setting}"
        staging = os.path.join(self.out, "cases", key, ".staging")
        shutil.rmtree(staging, ignore_errors=True)
        g = subprocess.run(self.gen_cmd("gen", "--row", str(row), "--setting", setting, "--dir", staging),
                           capture_output=True, text=True)
        if g.returncode != 0:
            self.last_gen_err = (g.stderr.strip() or f"rc={g.returncode}")[-200:]
            shutil.rmtree(staging, ignore_errors=True)
            staging = None
        self.run_one(key, staging, "row", sv_group, row, setting)

    def smoke_split(self, f):
        tmp = os.path.join(self.out, "cases", ".split-staging")
        shutil.rmtree(tmp, ignore_errors=True)
        g = subprocess.run(self.gen_cmd("smoke-split", os.path.join(self.repo, f), "--out", tmp),
                           capture_output=True, text=True)
        if g.returncode != 0:
            self.last_gen_err = g.stderr.strip()[-200:]
            self.run_one(f"S_{os.path.basename(f)}_gen", None, "smoke-split", row=f"smoke:{f}", setting="as-in-file")
            return
        for d in g.stdout.split():
            self.run_one(os.path.basename(d), d, "smoke-split")
        shutil.rmtree(tmp, ignore_errors=True)

    def smoke_file(self, f):
        path = os.path.realpath(os.path.join(self.repo, f))
        stem = os.path.splitext(os.path.basename(f))[0]
        staging = os.path.join(self.out, "cases", f"A_{stem}", ".staging")
        shutil.rmtree(staging, ignore_errors=True)
        os.makedirs(staging)
        open(os.path.join(staging, "case.env"), "w").close()
        with open(os.path.join(staging, "meta.json"), "w") as fo:
            json.dump({"kind": "smoke-asis", "file": f, "run": True}, fo)
        self.run_one(f"A_{stem}", staging, "smoke-asis", direct_file=path)

    # -------- tables
    def rebuild(self):
        rdir = os.path.join(self.out, "results", self.run_id)
        os.makedirs(rdir, exist_ok=True)
        tables = {"row": [], "smoke-split": [], "smoke-asis": []}
        for root in sorted(glob.glob(os.path.join(self.out, "cases", "*"))):
            best = None
            for a in self.attempts(root):
                try:
                    idn = json.load(open(os.path.join(a, "identity.json")))
                except (OSError, ValueError):
                    continue
                if idn.get("run_id") == self.run_id and os.path.exists(os.path.join(a, "done")):
                    best = (a, idn)
            if best:
                tables[best[1]["kind"]].append(open(os.path.join(best[0], "row.tsv")).read().rstrip("\n"))
        names = {"row": "results.tsv", "smoke-split": "results_smoke_split.tsv",
                 "smoke-asis": "results_smoke_asis.tsv"}
        for k, rows in tables.items():
            hdr = self.ASIS_COLUMNS if k == "smoke-asis" else self.header
            with open(os.path.join(rdir, names[k]), "w") as f:
                f.write("\t".join(hdr) + "\n")
                for r in rows:
                    f.write(r + "\n")
        with open(os.path.join(rdir, "identity.json"), "w") as f:
            json.dump(dict(self.gid, run_id=self.run_id), f, indent=1, sort_keys=True)
        with open(os.path.join(self.out, "CURRENT_RUN_ID"), "w") as f:
            f.write(self.run_id + "\n")
        return rdir, {k: len(v) for k, v in tables.items()}

    def summary(self):
        rdir, counts = self.rebuild()
        missing = []
        for key, _ in self.keys:
            ok = False
            for a in self.attempts(os.path.join(self.out, "cases", key)):
                try:
                    idn = json.load(open(os.path.join(a, "identity.json")))
                except (OSError, ValueError):
                    continue
                ok = ok or (idn.get("run_id") == self.run_id and os.path.exists(os.path.join(a, "done")))
            if not ok:
                missing.append(key)
        s = self.stats
        complete = s["harness_error"] == 0 and not missing
        line = (f"U0 SUMMARY run_id={self.run_id} src_sha={self.gid['src_sha'][:12]} requested={s['requested']} "
                f"ran={s['ran']} reused={s['reused']} not_run_unsupported={s['not_run']} "
                f"harness_error={s['harness_error']} missing={len(missing)} "
                f"tables={counts} {'COMPLETE' if complete else 'INCOMPLETE'}")
        with open(os.path.join(rdir, "summary.txt"), "a") as f:
            f.write(line + "\n")
        print(f"results: {rdir}")
        print(line)
        return 0 if complete else 3


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "_exec":
        d = argv[1]
        i = argv.index("--")
        opts = dict(zip(argv[2:i:2], argv[3:i:2]))
        exec_case(d, argv[i + 1:], int(opts["--tmo"]), int(opts["--grace"]), int(opts["--rlimit"]))
        return 0
    repo, out = ".", None
    while argv and argv[0].startswith("--"):
        if argv[0] == "--repo":
            repo = argv[1]
        elif argv[0] == "--out":
            out = argv[1]
        else:
            sys.exit(f"unknown option {argv[0]}")
        argv = argv[2:]
    if not out or not argv:
        sys.exit(__doc__)
    r = Runner(repo, out)
    mode = argv[0]
    if mode == "case":
        r.case(argv[1], argv[2], argv[3] if len(argv) > 3 else "")
    elif mode == "list":
        for ln in open(argv[1]):
            parts = ln.split()
            if not parts:
                continue
            if len(parts) < 2:
                r.stats["requested"] += 1
                r.stats["harness_error"] += 1
                print(f"harness-error: malformed list line {ln.strip()!r}")
                continue
            r.case(parts[0], parts[1], parts[2] if len(parts) > 2 else "")
    elif mode == "smoke-file":
        r.smoke_file(argv[1])
    elif mode == "smoke-split":
        r.smoke_split(argv[1])
    else:
        sys.exit(f"unknown mode {mode}")
    return r.summary()


if __name__ == "__main__":
    sys.exit(main())
