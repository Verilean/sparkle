#!/usr/bin/env python3
"""U1 measurement runner (MEASUREMENT ONLY, never for main).

Reuses the U0 runner (u0_run.py: per-case isolation in its own session under a
subreaper helper, SPARKLE_* cleared, rlimit, timeout + TERM/KILL, run identity,
attempts, reuse only on identical identity, harness-error rows, COMPLETE /
INCOMPLETE) with the U1 generator/classifier (u1_gen.py).  A row is run once
per route; the route is the case's "setting": `u1`, `u1_deep`, `u1_deep_ns`.

Usage (repo root of the worktree being measured; OUT outside the tree):
  u1_run.py --out OUT case ROW ROUTE
  u1_run.py --out OUT list ROWS.txt          # lines "ROW ROUTE"
  u1_run.py --out OUT merge SHARD_OUT...     # merge finished shards (same run_id) into OUT
Environment (U1_* are copied to the U0_* names the shared runner reads, unless
the U0_ name is already set):
  U1_LEAN   per-case command (default "kjob lake env lean")   U1_TMO  seconds (1800)
  U1_GRACE  TERM->KILL grace (10)    U1_RLIMIT_AS_KB  RLIMIT_AS per case (0 = off)
  U1_INV_COMMIT / U1_INV_BLOB   inventory pin    REDO=1  new attempt for every case

Outputs under OUT/results/<run_id>/: results.tsv (one record per row AND route),
union.tsv (one line per row: both routes side by side + union verdict),
summary.txt (per-route strict counts over 327, the union row count, the first-cause
cross table).  The denominators are never mixed: per-route counts are over that
route's 327 records; the union is over the 327 distinct rows.
"""
import csv
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
for k in ("LEAN", "TMO", "GRACE", "RLIMIT_AS_KB", "INV_COMMIT", "INV_BLOB"):
    if os.environ.get("U1_" + k) and not os.environ.get("U0_" + k):
        os.environ["U0_" + k] = os.environ["U1_" + k]
import u0_run  # noqa: E402

U1_GEN = os.path.join(HERE, "u1_gen.py")
u0_run.GEN = os.environ.get("U1_GEN_PY", U1_GEN)
import u1_gen  # noqa: E402

UNION_COLUMNS = (["row", "file", "line", "command", "top"]
                 + [f"{rt}_strict" for rt in u1_gen.ROUTES]
                 + ["union_std_strict", "union_strict", "union_strict_routes"]
                 + [f"{rt}_first_cause" for rt in u1_gen.ROUTES]
                 + [f"{rt}_status" for rt in u1_gen.ROUTES]
                 + [f"{rt}_prep_status" for rt in u1_gen.DEEP_ROUTES] + ["invocation"])


def sha(*paths):
    return u0_run.sha256_bytes(*[open(p, "rb").read() for p in paths])


STD_ROUTES = ("u1", "u1_deep")


def union_rows(records):
    """records: list of dict (results.tsv rows).  One union line per distinct row;
    a row strict in several routes counts once."""
    by = {}
    for r in records:
        by.setdefault(r["row"], {})[r["setting"]] = r
    out = []
    for row in sorted(by, key=lambda x: int(x) if x.isdigit() else 10 ** 9):
        recs = {rt: by[row].get(rt, {}) for rt in u1_gen.ROUTES}
        ok = [rt for rt in u1_gen.ROUTES if recs[rt].get("strict_counted") == "yes"]
        base = next((recs[rt] for rt in u1_gen.ROUTES if recs[rt]), {})
        u = {"row": row, "file": base.get("file", ""), "line": base.get("line", ""),
             "command": base.get("command", ""), "top": base.get("top", ""),
             # standard routes only (u1, u1_deep in the original scope)
             "union_std_strict": "yes" if any(rt in STD_ROUTES for rt in ok) else "no",
             # also the namespace-assisted route (reviewer ruling 2026-11-10)
             "union_strict": "yes" if ok else "no", "union_strict_routes": ",".join(ok),
             "invocation": base.get("invocation", "")}
        for rt in u1_gen.ROUTES:
            a = recs[rt]
            u[f"{rt}_strict"] = "yes" if rt in ok else ("no" if a else "missing")
            u[f"{rt}_first_cause"] = a.get("first_cause", "")
            u[f"{rt}_status"] = a.get("u1_status", "")
        for rt in u1_gen.DEEP_ROUTES:
            u[f"{rt}_prep_status"] = recs[rt].get("prep_status", "")
        out.append(u)
    return out


def summary_lines(records, union):
    lines = []
    routes = {}
    for r in records:
        routes.setdefault(r["setting"], []).append(r)
    for route in sorted(routes):
        rs = routes[route]
        n = len(rs)
        s = sum(1 for r in rs if r["strict_counted"] == "yes")
        lines.append(f"route {route}: records={n} strict_counted_yes={s}")
    std = sum(1 for u in union if u["union_std_strict"] == "yes")
    allr = sum(1 for u in union if u["union_strict"] == "yes")
    lines.append(f"union (standard routes u1, u1_deep): distinct_rows={len(union)} returned_IR_strict_rows={std}")
    lines.append(f"union (incl. namespace-assisted u1_deep_ns): distinct_rows={len(union)} "
                 f"returned_IR_strict_rows_incl_namespace_assisted={allr} "
                 f"strict_in_several_routes={sum(1 for u in union if u['union_strict_routes'].count(',') >= 1)}")
    lines.append("  (not: main's ordinary command succeeds as is / production route / release; "
                 "u1_deep refusals caused by the name lookup stay recorded)")
    lines.append("first_cause cross table (records):")
    causes = sorted({r["first_cause"] for r in records})
    lines.append("  " + "\t".join(["cause"] + sorted(routes)))
    for c in causes:
        lines.append("  " + "\t".join([c or "(empty)"] + [str(sum(1 for r in routes[k] if r["first_cause"] == c))
                                                          for k in sorted(routes)]))
    return lines


class U1Runner(u0_run.Runner):
    def __init__(self, repo, out):
        super().__init__(repo, out)
        hh = sha(*[os.path.join(HERE, n) for n in ("u0_gen.py", "u0_run.py", "u1_gen.py", "u1_run.py")])
        self.gid["harness_hash"] = hh
        self.gid["harness"] = "u1"
        self.run_id = u0_run.sha256_bytes(json.dumps(self.gid, sort_keys=True))[:16]

    def rebuild(self):
        rdir, counts = super().rebuild()
        with open(os.path.join(rdir, "results.tsv")) as f:
            recs = list(csv.DictReader(f, delimiter="\t"))
        self.records = recs
        self.union = union_rows(recs)
        with open(os.path.join(rdir, "union.tsv"), "w") as f:
            f.write("\t".join(UNION_COLUMNS) + "\n")
            for u in self.union:
                f.write("\t".join(u[c] for c in UNION_COLUMNS) + "\n")
        return rdir, counts

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
        head = (f"U1 SUMMARY run_id={self.run_id} src_sha={self.gid['src_sha'][:12]} requested={s['requested']} "
                f"ran={s['ran']} reused={s['reused']} not_run_unsupported={s['not_run']} "
                f"harness_error={s['harness_error']} missing={len(missing)} "
                f"{'COMPLETE' if complete else 'INCOMPLETE'}")
        body = summary_lines(self.records, self.union)
        with open(os.path.join(rdir, "summary.txt"), "w") as f:
            f.write("\n".join([head] + body) + "\n")
        print(f"results: {rdir}")
        print("\n".join([head] + body))
        return 0 if complete else 3


def merge(out, shards):
    """Concatenate the CURRENT run's results.tsv of finished shard directories (all
    must share one run_id-independent header) into OUT/merged/ and recompute the union."""
    recs, hdr, ids = [], None, set()
    for sd in shards:
        rid = open(os.path.join(sd, "CURRENT_RUN_ID")).read().strip()
        ids.add(rid)
        with open(os.path.join(sd, "results", rid, "results.tsv")) as f:
            rd = csv.DictReader(f, delimiter="\t")
            hdr = rd.fieldnames
            recs += list(rd)
    seen = set()
    for r in recs:
        k = (r["row"], r["setting"])
        if k in seen:
            sys.exit(f"merge: duplicate record {k}")
        seen.add(k)
    mdir = os.path.join(out, "merged")
    os.makedirs(mdir, exist_ok=True)
    with open(os.path.join(mdir, "results.tsv"), "w") as f:
        f.write("\t".join(hdr) + "\n")
        for r in recs:
            f.write("\t".join(r[c] for c in hdr) + "\n")
    union = union_rows(recs)
    with open(os.path.join(mdir, "union.tsv"), "w") as f:
        f.write("\t".join(UNION_COLUMNS) + "\n")
        for u in union:
            f.write("\t".join(u[c] for c in UNION_COLUMNS) + "\n")
    lines = [f"U1 MERGE shards={len(shards)} shard_run_ids={sorted(ids)} records={len(recs)}"] + \
        summary_lines(recs, union)
    with open(os.path.join(mdir, "summary.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "_exec":
        return u0_run.main()
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
    if argv[0] == "merge":
        return merge(os.path.realpath(out), argv[1:])
    r = U1Runner(repo, out)
    if argv[0] == "case":
        r.case(argv[1], argv[2])
    elif argv[0] == "list":
        for ln in open(argv[1]):
            parts = ln.split()
            if not parts:
                continue
            if len(parts) < 2 or parts[1] not in u1_gen.ROUTES:
                r.stats["requested"] += 1
                r.stats["harness_error"] += 1
                print(f"harness-error: malformed list line {ln.strip()!r}")
                continue
            r.case(parts[0], parts[1])
    else:
        sys.exit(f"unknown mode {argv[0]}")
    return r.summary()


if __name__ == "__main__":
    sys.exit(main())
