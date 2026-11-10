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
OUT root with CURRENT_RUN_ID).  Writes compare.tsv and compare.txt: per row whether the SV is
identical, the IR counts and yosys numbers of both sides, and deltas ONLY where the SV differs.
The comparison statement is: "SV identical => size identical (same backend)": a row whose SV is
identical but whose numbers differ is reported as a VIOLATION (backend or harness not the same);
"same backend" is checked (yosys version and flow scripts equal on both sides) and reported.
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
        for col in ("invocation", "size_status", "g_status", "f_status"):
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


def compare_rows(ra, rb):
    """-> (list of dict rows, summary dict)."""
    ia, ib = {r["row"]: r for r in ra}, {r["row"]: r for r in rb}
    rows = sorted(set(ia) | set(ib), key=lambda x: int(x) if x.isdigit() else 10 ** 9)
    out = []
    S = {"rows": len(rows), "sv_identical": 0, "sv_differs": 0, "not_comparable": 0, "violations": 0,
         "numbers_missing_identical": 0}
    for row in rows:
        a, b = ia.get(row, {}), ib.get(row, {})
        base = a or b
        rec = {"row": row, "file": base.get("file", ""), "command": base.get("command", ""),
               "top": base.get("top", ""), "status_A": a.get("size_status", "absent"),
               "status_B": b.get("size_status", "absent")}
        if usable(a) and usable(b):
            same = a["sv_identity"] == b["sv_identity"]
            rec["sv_identical"] = "yes" if same else "no"
        else:
            same = None
            rec["sv_identical"] = "n/a"
            S["not_comparable"] += 1
        rec["sv_sha256_A"], rec["sv_sha256_B"] = a.get("sv_sha256", ""), b.get("sv_sha256", "")
        rec["sv_modules_A"], rec["sv_modules_B"] = a.get("sv_modules", ""), b.get("sv_modules", "")
        viol = []
        for c in NUM_CMP:
            va, vb = a.get(c, ""), b.get(c, "")
            rec[c + "_A"], rec[c + "_B"] = va, vb
            rec[c + "_delta"] = delta(va, vb) if same is False else ""
            if same is True and va != vb:
                # identical SV must give identical numbers; a blank on one side (yosys timeout / error)
                # is not a number difference but it is not a confirmation either
                if va == "" or vb == "":
                    S["numbers_missing_identical"] += 1
                else:
                    viol.append(c)
        for c in ("g_status", "f_status"):
            rec[c + "_A"], rec[c + "_B"] = a.get(c, ""), b.get(c, "")
        rec["violation"] = ",".join(viol)
        if same is True:
            S["sv_identical"] += 1
        elif same is False:
            S["sv_differs"] += 1
        if viol:
            S["violations"] += 1
        out.append(rec)
    return out, S


COMPARE_COLUMNS = (["row", "file", "command", "top", "status_A", "status_B", "sv_identical",
                    "sv_sha256_A", "sv_sha256_B", "sv_modules_A", "sv_modules_B"]
                   + [f"{c}_{s}" for c in NUM_CMP for s in ("A", "B", "delta")]
                   + ["g_status_A", "g_status_B", "f_status_A", "f_status_B", "violation"])


def backend_check(ra, rb):
    """Same backend: one yosys version, and per row (both sides usable) the same flow scripts
    (file names, top, options), yosys command and timeout."""
    notes, same = [], True
    for col in ("ys_version", "ys_cmd", "ys_timeout_s"):
        va, vb = {r[col] for r in ra if r.get(col) and r.get("ys_files")}, {r[col] for r in rb if r.get(col) and r.get("ys_files")}
        if va != vb:
            same = False
            notes.append(f"{col}: A={sorted(va)} B={sorted(vb)}")
    ib = {r["row"]: r for r in rb}
    diff = [r["row"] for r in ra if r["row"] in ib and usable(r) and usable(ib[r["row"]])
            and (r["g_script"], r["f_script"]) != (ib[r["row"]]["g_script"], ib[r["row"]]["f_script"])]
    if diff:
        same = False
        notes.append(f"flow scripts differ in rows {','.join(diff[:20])}")
    return same, notes


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
    lines = [f"SIZE COMPARE A={a_dir} (src {srcs(ra)}) B={b_dir} (src {srcs(rb)})",
             f"statement: {STATEMENT}",
             f"same backend (yosys version, flow scripts, yosys command and timeout equal on both sides): "
             f"{'yes' if same_backend else 'NO'}" + ("" if same_backend else " -- " + "; ".join(notes)),
             f"rows={S['rows']} sv_identical={S['sv_identical']} sv_differs={S['sv_differs']} "
             f"not_comparable(no usable record on a side)={S['not_comparable']}",
             f"VIOLATIONS of the statement (identical SV, differing numbers): {S['violations']}"
             + (" -- rows: " + ",".join(r['row'] for r in rows if r['violation']) if S["violations"] else ""),
             f"identical-SV rows whose yosys number is missing on a side (timeout/error): {S['numbers_missing_identical']}",
             "deltas (B - A) are filled only for rows whose SV differs; no tolerance is applied "
             "(acceptance thresholds are the user's decision)"]
    with open(os.path.join(out, "compare.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"written: {out}/compare.tsv compare.txt")
    return 1 if S["violations"] else 0


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
