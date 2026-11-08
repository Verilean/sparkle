#!/usr/bin/env python3
"""VED release gate, proof stage: merge U0 case rows from several job directories.

    python3 -I gate_u0_merge.py --header RESULTS.tsv --inv INVENTORY.tsv --out OUT.tsv \
        [--settings default,shared] DIR...

Each DIR is a `ved_u0` directory (cases/R<row>_<setting>/attempt-*/row.tsv with
a `done` marker).  For every (row, setting) of the fixed inventory exactly one
record is written; the newest finished attempt wins and the source directory
is recorded.  A (row, setting) with no finished case is written as `missing`
so the 327-row denominator never shrinks.  RESULTS.tsv only supplies the
column header (any U0 results.tsv of the same harness version).
"""
import argparse
import csv
import glob
import os


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--header", required=True)
    ap.add_argument("--inv", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--settings", default="default,shared")
    ap.add_argument("dirs", nargs="+")
    a = ap.parse_args()
    hdr = open(a.header).readline().rstrip("\n").split("\t")
    inv = list(csv.DictReader(open(a.inv), delimiter="\t"))
    settings = a.settings.split(",")
    got = {}
    for d in a.dirs:
        for done in glob.glob(os.path.join(d, "cases", "*", "attempt-*", "done")):
            att = os.path.dirname(done)
            for line in open(os.path.join(att, "row.tsv")):
                rec = dict(zip(hdr, line.rstrip("\n").split("\t")))
                key = (rec["row"], rec["setting"])
                stamp = os.path.getmtime(done)
                if key not in got or stamp > got[key][0]:
                    got[key] = (stamp, rec, att)
    cols = hdr + ["source"]
    n_missing = 0
    with open(a.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", extrasaction="ignore")
        w.writeheader()
        for i, r in enumerate(inv, 1):
            for s in settings:
                k = (str(i), s)
                if k in got:
                    rec = dict(got[k][1]); rec["source"] = got[k][2]
                else:
                    n_missing += 1
                    rec = {"row": str(i), "file": r["file"], "command": r["command"],
                           "top": r["top"], "setting": s, "harness_error": "missing", "source": ""}
                w.writerow(rec)
    print(f"GATEU0MERGE rows={len(inv)} settings={settings} records={len(inv) * len(settings)} "
          f"found={len(inv) * len(settings) - n_missing} missing={n_missing}")


if __name__ == "__main__":
    main()
