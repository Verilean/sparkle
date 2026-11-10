#!/usr/bin/env python3
"""VED circuit-size runner (MEASUREMENT ONLY, never for main).  Wraps the U0 runner
(u0_run.py: per-case isolation, timeout, run identity, reuse only on identical identity,
harness-error rows) with the size generator/classifier (size_gen.py).

Usage (repo root of the tree being measured; OUT outside the tree):
  size_run.py --out OUT case ROW
  size_run.py --out OUT list ROWS.txt           # lines "ROW" (or "ROW size")
  size_run.py compare A B [--out DIR]           # A, B: result directories (see below)

Environment (U0_*/U1_* names as in the U1 runner; the size ones below)
  SIZE_LEAN  per-case lean command (default "kjob lake env lean")   SIZE_TMO  seconds (1800)
  SIZE_GRACE (10)  SIZE_RLIMIT_AS_KB (0)  SIZE_INV_COMMIT / SIZE_INV_BLOB  inventory pin
  SIZE_YOSYS      yosys command prefix (default
                  "nix shell github:NixOS/nixpkgs/<pinned rev>#yosys -c yosys"; the runner appends
                  "-q -s SCRIPT -l LOG")
  SIZE_YOSYS_TMO  per yosys flow timeout, seconds (600)      REDO=1  new attempt for every case

Outputs under OUT/results/<run_id>/: results.tsv (one record per inventory row, 327), summary.txt.

compare A B: A and B are result directories of two runs (a directory holding results.tsv, or an
OUT root with CURRENT_RUN_ID).  Writes compare.tsv and compare.txt.  Every row and section (ir = returned IR,
opt = optimised IR, g / f = yosys flows) is classified identical / different / not-comparable / incomplete.
IR counts are compared as returned whatever the SV says (identical SV can come from different raw IR).
A row enters the formal comparison only when sv_origin_check=same on BOTH sides (the SV the size numbers come from is
then what the original command emitted in that attempt); otherwise its sections are not-comparable (origin differ /
not-checked) or incomplete (field missing) and the exit status is 2.  The comparison of the re-synthesised artifacts of
such rows is only an OBSERVATION (obs_* columns, "OBSERVATION" line), never part of the exit status.
The backend statement "SV identical => yosys numbers identical" holds only for the same backend (non-empty,
equal yosys version, command, top, flow script, input files) with both flows ended normally; a row whose SV
and backend are identical but whose yosys numbers differ is a VIOLATION.  Exit status: 0 only when every
row is comparable and there is no violation; 1 = violation; 2 = some row not-comparable or incomplete
(unsupported rows unmeasured on both sides count as incomplete: "violations 0" is never a pass on its own).
"""
import csv
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
for k in ("LEAN", "TMO", "GRACE", "RLIMIT_AS_KB", "INV_COMMIT", "INV_BLOB"):
    if os.environ.get("SIZE_" + k) and not os.environ.get("U0_" + k):
        os.environ["U0_" + k] = os.environ["SIZE_" + k]
import u0_run  # noqa: E402

SIZE_GEN = os.path.join(HERE, "size_gen.py")
u0_run.GEN = os.environ.get("SIZE_GEN_PY", SIZE_GEN)
import size_gen  # noqa: E402

STATEMENT = "SV identical => size identical (same backend)"
IR_CMP = ["ir_modules", "ir_regs", "ir_mems", "ir_insts", "ir_stmts", "ir_wires", "ir_regbits", "ir_membits",
          "opt_regs", "opt_mems", "opt_insts", "opt_stmts", "opt_wires", "opt_regbits"]
YS_CMP = ["g_cells", "g_dff", "f_cells", "f_lut", "f_ff", "f_bram"]
NUM_CMP = IR_CMP + YS_CMP


def sha(*paths):
    return u0_run.sha256_bytes(*[open(p, "rb").read() for p in paths])


class SizeRunner(u0_run.Runner):
    def __init__(self, repo, out):
        super().__init__(repo, out)
        hh = sha(*[os.path.join(HERE, n) for n in ("u0_gen.py", "u0_run.py", "u1_gen.py", "size_gen.py", "size_run.py")])
        self.gid["harness_hash"] = hh
        self.gid["harness"] = "size"
        # everything that changes a size number is part of the run identity
        self.gid["yosys_cmd"] = " ".join(size_gen.yosys_cmd())
        self.gid["yosys_tmo"] = size_gen.yosys_tmo()
        self.run_id = u0_run.sha256_bytes(json.dumps(self.gid, sort_keys=True))[:16]

    def summary(self):
        rdir, counts = self.rebuild()
        with open(os.path.join(rdir, "results.tsv")) as f:
            recs = list(csv.DictReader(f, delimiter="\t"))
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
        head = (f"SIZE SUMMARY run_id={self.run_id} src_sha={self.gid['src_sha'][:12]} requested={s['requested']} "
                f"ran={s['ran']} reused={s['reused']} not_run_unsupported={s['not_run']} "
                f"harness_error={s['harness_error']} missing={len(missing)} "
                f"{'COMPLETE' if complete else 'INCOMPLETE'}")
        body = [f"records={len(recs)} (not a coverage claim: only the rows requested)",
                "yosys: " + self.gid["yosys_cmd"] + f" (timeout {self.gid['yosys_tmo']} s per flow)"]
        for col in ("invocation", "size_status", "sv_origin_check", "g_status", "f_status"):
            cnt = {}
            for r in recs:
                cnt[r[col]] = cnt.get(r[col], 0) + 1
            body.append(f"{col}: " + " ".join(f"{k or '(empty)'}={v}" for k, v in sorted(cnt.items())))
        with open(os.path.join(rdir, "summary.txt"), "w") as f:
            f.write("\n".join([head] + body) + "\n")
        print(f"results: {rdir}")
        print("\n".join([head] + body))
        return 0 if complete else 3


# ------------------------------------------------------------------ compare

def results_path(d):
    if os.path.exists(os.path.join(d, "results.tsv")):
        return os.path.join(d, "results.tsv")
    cur = os.path.join(d, "CURRENT_RUN_ID")
    if os.path.exists(cur):
        rid = open(cur).read().strip()
        p = os.path.join(d, "results", rid, "results.tsv")
        if os.path.exists(p):
            return p
    cand = sorted(glob.glob(os.path.join(d, "results", "*", "results.tsv")))
    if len(cand) == 1:
        return cand[0]
    sys.exit(f"compare: no results.tsv (or unique run) under {d}")


def load(d):
    with open(results_path(d)) as f:
        return list(csv.DictReader(f, delimiter="\t"))


def usable(r):
    return bool(r) and r.get("size_status") == "ok" and bool(r.get("sv_identity"))


def delta(a, b):
    try:
        return str(int(b) - int(a))
    except ValueError:
        return ""


# classes of a section of a row (IR, optimised IR, generic flow, fpga flow) and of the row (worst section)
IDENTICAL, DIFFERENT, NOT_COMPARABLE, INCOMPLETE = "identical", "different", "not-comparable", "incomplete"
ORDER = [IDENTICAL, DIFFERENT, NOT_COMPARABLE, INCOMPLETE]
SECTIONS = {
    "ir": ([c for c in IR_CMP if c.startswith("ir_")], None),
    "opt": ([c for c in IR_CMP if c.startswith("opt_")], None),
    "g": (["g_cells", "g_dff"], "g"),
    "f": (["f_cells", "f_lut", "f_ff", "f_bram"], "f"),
}


def backend_id(r, pre):
    """What a yosys number depends on besides the SV text: version, command, top, flow script, input files.
    Empty string when any part is missing (then nothing may be derived from it)."""
    parts = [r.get("ys_version", ""), r.get("ys_cmd", ""), r.get("sv_top", "") or r.get("top", ""),
             r.get(pre + "_script", ""), r.get("ys_files", "")]
    return "|".join(parts) if all(parts) else ""


def origin_gate(a, b):
    """The formal comparison is of the artifact the ORIGINAL command emitted: both sides must have
    sv_origin_check=same.  -> None, or (class, reason): not-comparable for differ / not-checked, incomplete when the
    field is missing."""
    for side, r in (("A", a), ("B", b)):
        o = r.get("sv_origin_check", "")
        if o == "same":
            continue
        if o in ("differ", "not-checked"):
            return NOT_COMPARABLE, f"{side}: sv_origin_check={o} ({r.get('sv_origin_reason', '')[:80]})"
        return INCOMPLETE, f"{side}: sv_origin_check missing"
    return None


def classify_section(sec, a, b, origin=True):
    """-> (class, reason).  IR sections (ir/opt) are compared as returned, independent of the SV and the backend.
    Flows are compared only with a non-empty, equal backend identity on both sides, both flows ended normally and
    every required number present.  With `origin` (the formal comparison) both sides must also have
    sv_origin_check=same; `origin=False` is the OBSERVATION of the re-synthesised artifacts, which never decides
    the exit status."""
    cols, pre = SECTIONS[sec]
    for side, r in (("A", a), ("B", b)):
        if not r:
            return INCOMPLETE, f"{side}: no record"
        if r.get("size_status") != "ok":
            return INCOMPLETE, f"{side}: size_status={r.get('size_status') or '(empty)'}"
    g = origin_gate(a, b) if origin else None
    if g:
        return g
    for side, r in (("A", a), ("B", b)):
        if pre and r.get(pre + "_status") != "ok":
            return INCOMPLETE, f"{side}: {pre}_status={r.get(pre + '_status') or '(empty)'}"
        miss = [c for c in cols if r.get(c, "") == ""]
        if miss:
            return INCOMPLETE, f"{side}: missing {','.join(miss)}"
    if pre:
        ba, bb = backend_id(a, pre), backend_id(b, pre)
        if not ba or not bb:
            return NOT_COMPARABLE, "backend identity empty on " + "/".join(s for s, x in (("A", ba), ("B", bb)) if not x)
        if ba != bb:
            return NOT_COMPARABLE, "backend differs (version/cmd/top/script/files)"
    same = all(a[c] == b[c] for c in cols)
    return (IDENTICAL if same else DIFFERENT), ""


def compare_rows(ra, rb):
    """-> (list of dict rows, summary dict).  Each row and section is classified identical / different /
    not-comparable / incomplete; nothing unmeasured or not comparable counts as a pass."""
    def index(rs):
        d, dup = {}, set()
        for r in rs:
            if r["row"] in d:
                dup.add(r["row"])
            d.setdefault(r["row"], r)
        return d, dup
    (ia, da), (ib, db) = index(ra), index(rb)
    rows = sorted(set(ia) | set(ib), key=lambda x: int(x) if x.isdigit() else 10 ** 9)
    out = []
    S = {"rows": len(rows), "sv_identical": 0, "sv_differs": 0, "sv_n_a": 0, "violations": 0,
         "ir_differs_same_sv": 0, "opt_differs_same_sv": 0, "duplicate_rows": 0,
         "row_class": {c: 0 for c in ORDER}, "section_class": {s: {c: 0 for c in ORDER} for s in SECTIONS},
         "incomplete_unsupported_both": 0, "origin_differ": 0, "origin_not_checked": 0,
         "obs_class": {s: {c: 0 for c in ORDER} for s in SECTIONS}, "obs_row_class": {c: 0 for c in ORDER}}
    for row in rows:
        a, b = ia.get(row, {}), ib.get(row, {})
        base = a or b
        rec = {"row": row, "file": base.get("file", ""), "command": base.get("command", ""),
               "top": base.get("top", ""), "status_A": a.get("size_status", "absent"),
               "status_B": b.get("size_status", "absent")}
        dup = row in da or row in db
        if dup:
            S["duplicate_rows"] += 1
        # the re-synthesised SVs against each other: an OBSERVATION; the formal sv_identical needs origin=same on both sides
        obs_same = a["sv_identity"] == b["sv_identity"] if usable(a) and usable(b) else None
        rec["obs_sv_identical"] = "n/a" if obs_same is None else "yes" if obs_same else "no"
        same = obs_same if obs_same is not None and origin_gate(a, b) is None else None
        rec["sv_identical"] = "n/a" if same is None else "yes" if same else "no"
        S["sv_identical" if same else "sv_differs" if same is False else "sv_n_a"] += 1
        for c in ("sv_sha256", "sv_modules", "sv_origin_check"):
            rec[c + "_A"], rec[c + "_B"] = a.get(c, ""), b.get(c, "")
        for sd in (a, b):
            if sd.get("sv_origin_check") == "differ":
                S["origin_differ"] += 1
            elif sd and sd.get("size_status") == "ok" and sd.get("sv_origin_check") != "same":
                S["origin_not_checked"] += 1
        viol, reasons, classes, obs = [], [], {}, {}
        for sec, (cols, pre) in SECTIONS.items():
            cls, why = (NOT_COMPARABLE, "duplicate row in an input") if dup else classify_section(sec, a, b)
            classes[sec] = cls
            rec["class_" + sec] = cls
            obs[sec] = (NOT_COMPARABLE if dup else classify_section(sec, a, b, origin=False)[0])
            rec["obs_class_" + sec] = obs[sec]
            S["obs_class"][sec][obs[sec]] += 1
            if why:
                reasons.append(f"{sec}: {why}")
            S["section_class"][sec][cls] += 1
            ok = cls in (IDENTICAL, DIFFERENT)
            for c in cols:
                va, vb = a.get(c, ""), b.get(c, "")
                rec[c + "_A"], rec[c + "_B"] = va, vb
                rec[c + "_delta"] = delta(va, vb) if ok else ""
                if ok and same is True and pre and va != vb:
                    viol.append(c)          # identical SV, same backend, other yosys numbers
            if same is True and sec in ("ir", "opt") and cls == DIFFERENT:
                S[sec + "_differs_same_sv"] += 1
        worst = max(classes.values(), key=ORDER.index)
        rec["class"] = worst
        rec["obs_class"] = max(obs.values(), key=ORDER.index)
        S["obs_row_class"][rec["obs_class"]] += 1
        rec["reasons"] = "; ".join(reasons)[:400]
        if worst == INCOMPLETE and a.get("size_status") == "not-run" and b.get("size_status") == "not-run":
            S["incomplete_unsupported_both"] += 1
        S["row_class"][worst] += 1
        for c in ("g_status", "f_status"):
            rec[c + "_A"], rec[c + "_B"] = a.get(c, ""), b.get(c, "")
        rec["violation"] = ",".join(viol)
        if viol:
            S["violations"] += 1
        out.append(rec)
    return out, S


COMPARE_COLUMNS = (["row", "file", "command", "top", "status_A", "status_B", "sv_identical",
                    "sv_sha256_A", "sv_sha256_B", "sv_modules_A", "sv_modules_B",
                    "sv_origin_check_A", "sv_origin_check_B", "class", "class_ir", "class_opt", "class_g", "class_f",
                    "reasons", "obs_sv_identical", "obs_class", "obs_class_ir", "obs_class_opt", "obs_class_g", "obs_class_f"]
                   + [f"{c}_{s}" for cols, _ in SECTIONS.values() for c in cols for s in ("A", "B", "delta")]
                   + ["g_status_A", "g_status_B", "f_status_A", "f_status_B", "violation"])


def backend_check(ra, rb):
    """Informational: do the flows of the comparable rows share one backend?  Per row and flow the identity (non-empty
    yosys version, command, top, script, files) must be present and equal on both sides; a version that is
    blank on a side or swapped between rows is a difference.  -> (same, notes)."""
    ib = {r["row"]: r for r in rb}
    notes = []
    for pre in ("g", "f"):
        bad = [r["row"] for r in ra if r["row"] in ib and r.get(pre + "_status") == "ok" and ib[r["row"]].get(pre + "_status") == "ok"
               and (not backend_id(r, pre) or backend_id(r, pre) != backend_id(ib[r["row"]], pre))]
        if bad:
            notes.append(f"{pre}: backend identity empty or different in rows {','.join(bad[:20])}")
    for name, rs in (("A", ra), ("B", rb)):
        vs = {r.get("ys_version", "") for r in rs if r.get("ys_files")}
        if "" in vs or len(vs) > 1:
            notes.append(f"{name}: yosys versions {sorted(vs)} (blank or several)")
    return not notes, notes


def cmd_compare(a_dir, b_dir, out):
    ra, rb = load(a_dir), load(b_dir)
    rows, S = compare_rows(ra, rb)
    same_backend, notes = backend_check(ra, rb)
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "compare.tsv"), "w") as f:
        f.write("\t".join(COMPARE_COLUMNS) + "\n")
        for r in rows:
            f.write("\t".join(str(r.get(c, "")).replace("\t", " ") for c in COMPARE_COLUMNS) + "\n")
    srcs = lambda rs: sorted({r.get("src_sha", "")[:12] for r in rs})
    rc = S["row_class"]
    nonpass = rc[NOT_COMPARABLE] + rc[INCOMPLETE]
    status = 1 if S["violations"] else 2 if nonpass else 0
    lines = [f"SIZE COMPARE A={a_dir} (src {srcs(ra)}) B={b_dir} (src {srcs(rb)})",
             f"statement: {STATEMENT}",
             "yosys numbers are compared per row and flow only when the backend identity (version, command, top, flow "
             "script, input files) is non-empty and equal on both sides, both flows ended normally and every number is "
             "present; IR counts (ir_*, opt_*) are compared as returned, independently of the SV",
             f"backend check (informational): {'consistent' if same_backend else 'NOT CONSISTENT -- ' + '; '.join(notes)}",
             f"rows={S['rows']} (duplicate rows in an input: {S['duplicate_rows']}) "
             f"sv_identical={S['sv_identical']} sv_differs={S['sv_differs']} sv_n/a={S['sv_n_a']}",
             "row classes: " + " ".join(f"{c}={rc[c]}" for c in ORDER)
             + f" (incomplete of which unsupported/not-run on both sides: {S['incomplete_unsupported_both']})"]
    for sec in SECTIONS:
        lines.append(f"  {sec}: " + " ".join(f"{c}={S['section_class'][sec][c]}" for c in ORDER))
    lines += [f"VIOLATIONS (identical SV, same backend, other yosys numbers): {S['violations']}"
              + (" -- rows: " + ",".join(r["row"] for r in rows if r["violation"]) if S["violations"] else ""),
              f"identical SV but returned IR (ir_*) differs: {S['ir_differs_same_sv']}; optimised IR (opt_*) differs: "
              f"{S['opt_differs_same_sv']} (reported, not a violation)",
              f"sv_origin_check: differ={S['origin_differ']} not-same(not-checked/other, measured sides)={S['origin_not_checked']}"
              " -- a row enters the formal comparison only when BOTH sides are origin=same (else not-comparable / incomplete)",
              "OBSERVATION (re-synthesised artifacts compared without the origin condition; never decides the exit status; "
              "columns obs_*): row classes " + " ".join(f"{c}={S['obs_row_class'][c]}" for c in ORDER),
              "deltas (B - A) are filled for every comparable section; no tolerance is applied "
              "(acceptance thresholds are the user's decision)",
              ("RESULT: every row comparable (exit 0)" if status == 0 else
               f"RESULT: NOT A PASS -- violations={S['violations']} not-comparable={rc[NOT_COMPARABLE]} "
               f"incomplete={rc[INCOMPLETE]}; unmeasured or not-comparable rows are never a pass "
               f"(exit {status}: 1 = violation, 2 = not-comparable or incomplete)")]
    with open(os.path.join(out, "compare.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"written: {out}/compare.tsv compare.txt")
    return status


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "_exec":
        return u0_run.main()
    if argv and argv[0] == "compare":
        rest, out = argv[1:], None
        if "--out" in rest:
            i = rest.index("--out")
            out = rest[i + 1]
            rest = rest[:i] + rest[i + 2:]
        if len(rest) != 2:
            sys.exit(__doc__)
        out = out or os.path.join(os.path.dirname(os.environ.get("KJOB_REPORT_PATH", os.path.join(os.getcwd(), "x"))),
                                  "size-compare")
        return cmd_compare(rest[0], rest[1], os.path.realpath(out))
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
    r = SizeRunner(repo, out)
    if argv[0] == "case":
        r.case(argv[1], size_gen.SETTING)
    elif argv[0] == "list":
        for ln in open(argv[1]):
            parts = ln.split()
            if not parts:
                continue
            if len(parts) > 2 or (len(parts) == 2 and parts[1] != size_gen.SETTING):
                r.stats["requested"] += 1
                r.stats["harness_error"] += 1
                print(f"harness-error: malformed list line {ln.strip()!r}")
                continue
            r.case(parts[0], size_gen.SETTING)
    else:
        sys.exit(f"unknown mode {argv[0]}")
    return r.summary()


if __name__ == "__main__":
    sys.exit(main())
