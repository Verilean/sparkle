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

# ---- row obligations (RowTypedAtV / RowTeleEvAt) of the rows that a stop set needs, joined with the PTcorpus row status ----
import os
here = os.path.dirname(os.path.abspath(__file__))
def tsv(p): return [l.rstrip("\n").split("\t") for l in open(os.path.join(here, p)) if l.strip()]
pt_keys = {(r[0], r[2]) for r in tsv("ptcorpus_keys.tsv")}
pt_missing = {(r[0], r[2]) for r in tsv("ptcorpus_missing.tsv")}
pt_closure = {(r[0], r[2]) for r in tsv("ptcorpus_closure.tsv")}
has_row = (pt_keys - pt_missing) | pt_closure
PAID_R = {"R0", "R1", "R2"}; PAID_T = {"T0", "T1"}
def paid_r(r, t):
    """RowTypedAtV: shape of an existing lemma. R0 = rowTypedAtV_nullary_const, R1 with no dependent binder = rowTypedAtV_closedPi (ClosedPi needs every body closed), R2 = rowTypedAtV_depFirst."""
    return r in ("R0", "R2") or (r == "R1" and t != "T3")
def tally(items, title):
    """items: list of (R, T)."""
    cr = collections.Counter(r for r, t in items); ct = collections.Counter(t for r, t in items)
    pr = sum(1 for r, t in items if paid_r(r, t)); pt = sum(c for k, c in ct.items() if k in PAID_T)
    r1d = sum(1 for r, t in items if r == "R1" and t == "T3")
    n = len(items)
    print(f"   {title}: {n} rows | RowTypedAtV: shape of an existing lemma {pr} (R0/R1 closed Pi/R2), closed codomain but dependent binders R1d {r1d}, R3a {cr['R3a']}, R0x/R1x {cr['R0x']+cr['R1x']}, R3 {cr['R3']} | RowTeleEvAt: shape of an existing lemma {pt} (T0/T1), T2 {ct['T2']}, T3 {ct['T3']}")
print("\n==================== row obligations ====================")
for g in ["sig", "corpus"]:
    ts = group(g)
    keys = collections.defaultdict(dict); stopped = collections.defaultdict(dict)
    for t in ts:
        for r in rows("cmpkeys", t):
            keys[int(r[0])][(r[1], r[3])] = (r[2], pf(r[5:]))
        for r in rows("cmpstopped", t):
            stopped[int(r[0])][(r[1], r[2])] = (r[4], pf(r[5:]))
    for st in (0, 1, 2, 3, 5):
        print(f"{g} stage {st} ({STAGES[st]}):")
        ctor_rows = [(f["R"], f["T"]) for (n, lv), (k, f) in keys[st].items() if k == "ctor" and (n, lv) in has_row]
        ctor_norow = [n + lv for (n, lv), (k, f) in keys[st].items() if k == "ctor" and (n, lv) not in has_row]
        tally(ctor_rows, "residue constructor rows (PTcorpus has the row)")
        print(f"   residue constructors WITHOUT a PTcorpus row: {len(ctor_norow)}")
        if st:
            sp = [(f["R"], f["T"]) for d, f in stopped[st].values() if d == "fits"]
            tally(sp, "stopped definitions that fit Dyn (a new row each)")
            print(f"   stopped definitions that do NOT fit Dyn (no row possible without U/P): {sum(1 for d,f in stopped[st].values() if d!='fits')}")
            tally(ctor_rows + sp, "TOTAL rows to type")

# ---- per option: what happens to the residue keys of each stage (join with the PTcorpus row status and the reason a row is missing) ----
miss_reason = {(r[0], r[2]): r[3] for r in tsv("ptcorpus_missing.tsv")}
def reason_class(rs):
    if rs.startswith("recursor"): return "rec"
    if rs.startswith("constant not in the import closure"): return "decl"
    return "type"
print("\n==================== residue keys per option ====================")
print("status per key: ROW = PTcorpus has the row (same under every option) | DECL = corpus declaration outside the import closure of Tools (orthogonal to every option) |")
print("NEW = type-blocked key whose declared type fits the option's Dyn (a row can be generated) | REC+ = recursor whose type fits the option but whose motive is a function into a Sort (needs a type-valued term rule too) | BLOCKED = still does not fit")
for g in ["sig", "corpus"]:
    ts = group(g)
    keys = collections.defaultdict(dict)
    for t in ts:
        for r in rows("cmpkeys", t): keys[int(r[0])][(r[1], r[3])] = (r[2], pf(r[5:]))
    for st in (0, 1, 2, 3, 5):
        ks = keys[st]
        base = collections.Counter()
        for (n, lv), (kind, f) in ks.items():
            if (n, lv) in has_row: base["ROW"] += 1; continue
            rc = reason_class(miss_reason.get((n, lv), "type"))
            if rc == "decl": base["DECL"] += 1; continue
            # keys without row because of the type
            base["typeblocked"] += 1
        print(f"{g} stage {st} ({STAGES[st]}): residue {len(ks)} = ROW {base['ROW']} + DECL {base['DECL']} + type-blocked {base['typeblocked']}")
        for o in ["U1", "Uany", "P", "U1+P", "Uany+P"]:
            c = collections.Counter()
            for (n, lv), (kind, f) in ks.items():
                if (n, lv) in has_row: continue
                if reason_class(miss_reason.get((n, lv), "type")) == "decl": continue
                fits = o in opts(f)
                if kind == "rec": c["REC+" if fits else "BLOCKED(rec)"] += 1
                else: c["NEW" if fits else "BLOCKED"] += 1
            print(f"      option {o:7}: NEW {c['NEW']}, REC+ {c['REC+']}, BLOCKED(non-rec) {c['BLOCKED']}, BLOCKED(rec) {c['BLOCKED(rec)']}")

# ---- the type formers that the DECLARED TYPES of the stopped definitions need (not reached by the traversal: the traversal enters bodies only) ----
print("\n==================== type closure of the stopped definitions ====================")
for g in ["sig", "corpus"]:
    ts = group(g)
    for st in (1, 2, 3, 5):
        clos = {}; resid = {}
        for t in ts:
            for r in rows("cmpclos", t):
                if int(r[0]) == st: clos[(r[1], r[3])] = (r[2], r[4])
            for r in rows("cmpkeys", t):
                if int(r[0]) == st: resid[(r[1], r[3])] = r[2]
        extra = {k: v for k, v in clos.items() if k not in resid}
        er = collections.Counter(("row" if k in has_row else ("decl" if reason_class(miss_reason.get(k, "type")) == "decl" else "no row (type)")) for k in extra)
        kinds = collections.Counter(v[0] for v in extra.values())
        print(f"{g} stage {st}: type-closure keys {len(clos)} (already in the residue {len(clos)-len(extra)}), EXTRA {len(extra)}: kinds {dict(kinds)}; PTcorpus: {dict(er)}")
        if len(extra) <= 20:
            print("     extra:", sorted(n + lv for (n, lv) in extra))
        else:
            print("     extra (first 25):", sorted(n + lv for (n, lv) in extra)[:25])
