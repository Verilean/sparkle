#!/usr/bin/env python3
"""Derive docs/research/data/coverage-327.tsv from an approved same-SHA ledger directory.

Usage: python3 -I scripts/research/ledger_to_tsv.py LEDGER_DIR OUT.tsv

LEDGER_DIR holds ledger.tsv (one line per command row) as written by the measurement ledger
generator (see docs/research/appendix/C-Reproduction.md). Absolute paths of the measurement
host (stdout/stderr references) are dropped. The mapping is:

  kind     = class (real-ip | regression)
  status   = strict if current_status == strict; unmeasured if current_routes_ran is empty;
             refused otherwise
  route    = sel_route (strict: the first strict route; else the first route that ran)
  conditions = sel_expected_stmt (the statement kind the route expected), or "-"
  blockers = current_first_causes (route:first-blocker for every route)
  provenance = baseline-strict | approved-earlier-sha | measured-only (strict rows only)
"""
import csv
import sys

COLS = ["row", "kind", "file", "line", "command", "declaration", "status", "route",
        "strict_routes", "conditions", "blockers", "outcome", "wall_s", "peak_rss_mb",
        "provenance"]


def main(ledger_dir, out):
    with open(ledger_dir.rstrip("/") + "/ledger.tsv", newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    rows.sort(key=lambda r: int(r["row"]))
    with open(out, "w", newline="") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(COLS)
        for r in rows:
            if r["current_status"] == "strict":
                status = "strict"
            elif not r["current_routes_ran"]:
                status = "unmeasured"
            else:
                status = "refused"
            if status != "strict":
                prov = ""
            elif r["baseline_d331ff24"] == "strict":
                prov = "baseline-strict"
            elif r["history_approved"]:
                prov = "approved-earlier-sha"
            else:
                prov = "measured-only"
            rss = r["sel_peak_rss_kb"]
            rss_mb = str(round(int(rss) / 1024)) if rss else ""
            w.writerow([
                int(r["row"]), r["class"], r["file"], r["line"], r["command"],
                r["decl_current"] or "", status, "" if status == "unmeasured" else r["sel_route"],
                r["current_routes"] if status == "strict" else "",
                r["sel_expected_stmt"] or "-", r["current_first_causes"],
                r["sel_term"], r["sel_wall_s"], rss_mb, prov])


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
