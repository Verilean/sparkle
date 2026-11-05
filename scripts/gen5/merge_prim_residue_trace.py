#!/usr/bin/env python3
"""Merge the per-driver raw rows of PrimResidueTrace (main43, M1..M4, Sig).
usage: merge_prim_residue_trace.py REPORT_PATH   (reads REPORT_PATH.trkeys.TAG / .trstopped.TAG / .trrec.TAG / .trroots.TAG)
Output: (1) per stage the corpus residue (keys, recursors, proof binders, other non-Type-0, rest) and the stopped set (distinct, not in Dyn);
(2) per stage for the Signal roots the same; (3) the direct parents of every recursor at the stages 0..5 (corpus and Signal roots, number of roots);
(4) the last project definition (Sparkle / Tools / Tests) on each recursor chain; (5) example chains."""
import sys, glob, collections
rp = sys.argv[1]
tags = sorted(p.rsplit(".trkeys.", 1)[1] for p in glob.glob(rp + ".trkeys.*"))
print("drivers:", tags)
def rows(kind, t):
    return [l.rstrip("\n").split("\t") for l in open(f"{rp}.{kind}.{t}")]
def group(name):  # corpus / sig
    return ["Sig"] if name == "sig" else [t for t in tags if t != "Sig"]
def cat(kind, dyn):
    if kind == "rec": return "recursor"
    if dyn == "fits": return "fits Dyn"
    w = dyn[4:]
    if w.startswith("proof binder"): return "proof binder"
    if w.startswith("constant not in") or w.startswith("no declaration"): return "other"
    return "outside Type 0 (binder/result/family)"
STAGES = {0: "none", 1: "Signal defns", 2: "+BitVec defns", 3: "+Decidable/Nat defns", 4: "+instDecidableEq family (Decidable/decEq/decLe/decLt/decide)", 5: "+all Init/Std/Lean defns"}
project = ("Sparkle", "Tools", "Tests")
for gname in ["corpus", "sig"]:
    print(f"\n==================== {gname} ====================")
    ts = group(gname)
    keys = collections.defaultdict(dict); stopped = collections.defaultdict(dict)
    for t in ts:
        for st, n, kind, lv, c, dyn in rows("trkeys", t): keys[int(st)][(n, lv)] = (kind, dyn)
        for st, n, lv, c, dyn in rows("trstopped", t): stopped[int(st)][(n, lv)] = dyn
    print("stage | residue keys | recursors | proof binder | outside Type 0 | other | fits Dyn | stopped distinct | stopped not in Dyn | recursor keys")
    for st in range(6):
        cc = collections.Counter(cat(k, d) for (k, d) in keys[st].values())
        nd = sum(1 for d in stopped[st].values() if d != "fits")
        recs = sorted(f"{n}{lv}" for (n, lv), (k, d) in keys[st].items() if k == "rec")
        print(f"{st} {STAGES[st]} | {len(keys[st])} | {cc['recursor']} | {cc['proof binder']} | {cc['outside Type 0 (binder/result/family)']} | {cc['other']} | {cc['fits Dyn']} | {len(stopped[st])} | {nd} | {recs}")
    for st in range(6):
        no = sorted((n + lv, d) for (n, lv), d in stopped[st].items() if d != "fits")
        if no: print(f"  stage {st} stopped, not in Dyn ({len(no)}):", no)
    # recursors by direct parent
    print("\n-- direct parents of each recursor (number of roots) --")
    for st in range(6):
        par = collections.defaultdict(collections.Counter)
        lastproj = collections.Counter(); ex = {}
        for t in ts:
            for s, r, rec, p, ch in rows("trrec", t):
                if int(s) != st: continue
                par[rec][p] += 1
                elems = ch.split(" > ")
                pj = [e for e in elems[:-1] if e.split(".")[0] in project]
                lastproj[pj[-1] if pj else "(none)"] += 1
                ex.setdefault((rec, p), ch)
        print(f"stage {st} ({STAGES[st]}): {len(par)} recursor keys")
        for rec in sorted(par): print(f"   {rec}: " + "; ".join(f"{p} x{c}" for p, c in par[rec].most_common()))
        if par:
            print("   last project definition on the chain (chains):", dict(lastproj.most_common(8)))
            if st in (0, 1, 5):
                for (rec, p), ch in sorted(ex.items())[:40]: print(f"   chain {ch}")
