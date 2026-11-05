#!/usr/bin/env python3
"""Merge the raw rows of PrimResidueCmp (main43, M1..M4, Sig) and tabulate the carrier comparison (issue sparkle-ledger-dd4-final Q-A (ii)).
usage: merge_prim_residue_cmp.py REPORT_PATH
reads REPORT_PATH.cmpkeys.TAG / .cmpstopped.TAG / .cmprec.TAG. Profile fields: need sym nEra resEra arity nTy Rclass Tclass.
Prints, per group (corpus = main43+M1..M4 union, sig = the three Signal roots) and stage: residue keys and how many each option can give a row TYPE for
(base Dyn / U1 = Dyn.{1} / Uany / P = Prop erased / U1+P / Uany+P), the stopped set with its obligation classes, and the recursor-major classes."""
import sys, glob, collections
rp = sys.argv[1]
tags = sorted(p.rsplit(".cmpkeys.", 1)[1] for p in glob.glob(rp + ".cmpkeys.*"))
def rows(kind, t): return [l.rstrip("\n").split("\t") for l in open(f"{rp}.{kind}.{t}")]
def group(g): return ["Sig"] if g == "sig" else [t for t in tags if t != "Sig"]
STAGES = {0: "none", 1: "Signal", 2: "+BitVec", 3: "+Decidable/Nat", 4: "+instDecidableEq", 5: "+all Init/Std/Lean"}
def pf(p):  # profile fields -> dict
    need, sym, nEra, resEra, ar, nTy, rc, tc = p
    return dict(need=int(need), sym=sym == "true", era=int(nEra) + (1 if resEra == "true" else 0), arity=int(ar), nTy=int(nTy), R=rc, T=tc)
def opts(f):
    if f["sym"]: return set()
    s = set()
    if f["need"] == 0 and f["era"] == 0: s.add("base")
    if f["need"] <= 1 and f["era"] == 0: s.add("U1")
    if f["era"] == 0: s.add("Uany")
    if f["need"] == 0: s.add("P")
    if f["need"] <= 1: s.add("U1+P")
    s.add("Uany+P")
    return s
O = ["base", "U1", "Uany", "P", "U1+P", "Uany+P"]
for g in ["corpus", "sig"]:
    ts = group(g)
    print(f"\n==================== {g} ====================")
    keys = collections.defaultdict(dict); stopped = collections.defaultdict(dict); rec = collections.defaultdict(set)
    for t in ts:
        for r in rows("cmpkeys", t):
            st, n, kind, lv, c = r[:5]; keys[int(st)][(n, lv)] = (kind, pf(r[5:]))
        for r in rows("cmpstopped", t):
            st, n, lv, c, dyn = r[:5]; stopped[int(st)][(n, lv)] = (dyn, pf(r[5:]))
        for r in rows("cmprec", t):
            st, node, rn, cls = r; rec[int(st)].add((node, rn, cls))
    print("stage | residue | rec | " + " | ".join(O) + " | max need | keys with sym")
    for st in range(6):
        ks = keys[st]
        cnt = collections.Counter()
        for (n, lv), (kind, f) in ks.items():
            for o in opts(f): cnt[o] += 1
        mx = max((f["need"] for k, f in ks.values()), default=0)
        print(f"{st} {STAGES[st]} | {len(ks)} | {sum(1 for k,f in ks.values() if k=='rec')} | " + " | ".join(str(cnt[o]) for o in O) + f" | {mx} | {sum(1 for k,f in ks.values() if f['sym'])}")
    print("\n-- residue keys NOT typable by base Dyn, by kind and by the smallest option that types them (stage 0, 2, 5) --")
    for st in (0, 2, 5):
        c = collections.Counter(); ex = collections.defaultdict(list)
        for (n, lv), (kind, f) in keys[st].items():
            o = opts(f)
            if "base" in o: continue
            best = "U1" if "U1" in o else "P" if "P" in o else "U1+P" if "U1+P" in o else "Uany" if "Uany" in o else "Uany+P" if "Uany+P" in o else "none"
            c[(kind, best)] += 1; ex[(kind, best)].append(n + lv)
        print(f"stage {st}:")
        for k in sorted(c): print(f"   {k}: {c[k]}  e.g. {ex[k][:6]}")
    print("\n-- stopped set: obligation classes (stage 2, 5) --")
    for st in (1, 2, 3, 5):
        sp = stopped[st]
        print(f"stage {st} ({STAGES[st]}): stopped distinct {len(sp)}")
        cr = collections.Counter(f["R"] for d, f in sp.values()); ct = collections.Counter(f["T"] for d, f in sp.values())
        print("   RowTypedAtV class:", dict(sorted(cr.items())), " RowTeleEvAt class:", dict(sorted(ct.items())))
        cj = collections.Counter((f["R"], f["T"]) for d, f in sp.values())
        print("   (R,T):", dict(sorted(cj.items())))
        fit = sum(1 for d, f in sp.values() if d == "fits")
        print(f"   fits Dyn(Type 0): {fit}; not: {len(sp)-fit}; of which typable by U1 {sum(1 for d,f in sp.values() if d!='fits' and 'U1' in opts(f))}, P {sum(1 for d,f in sp.values() if d!='fits' and 'P' in opts(f))}, U1+P {sum(1 for d,f in sp.values() if d!='fits' and 'U1+P' in opts(f))}")
        ar = collections.Counter(f["arity"] for d, f in sp.values()); print("   arity histogram:", dict(sorted(ar.items())))
        print("   max need:", max((f['need'] for d, f in sp.values()), default=0), " with era:", sum(1 for d, f in sp.values() if f['era']))
    print("\n-- recursor occurrences by major class (distinct (node, rec, class)) --")
    for st in (0, 1, 2, 3, 5):
        c = collections.Counter(cls for node, rn, cls in rec[st]); nodes = len({node for node, rn, cls in rec[st]})
        byrec = collections.defaultdict(collections.Counter)
        for node, rn, cls in rec[st]: byrec[rn][cls] += 1
        print(f"stage {st}: occurrences {sum(c.values())} in {nodes} nodes: {dict(c)}")
        if st in (0, 2, 5):
            for rn in sorted(byrec): print(f"     {rn}: {dict(byrec[rn])}")
