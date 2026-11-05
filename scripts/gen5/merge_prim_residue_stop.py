#!/usr/bin/env python3
"""Merge the per-driver raw rows of PrimResidueStop (main43, M1..M4, Sig) and classify the residue keys with the PTcorpus tables.
usage: merge_prim_residue_stop.py REPORT_PATH [REPO_ROOT]   (reads REPORT_PATH.stopkey.TAG / .stoppedrows.TAG / .stoproots.TAG / .stopreach.TAG)
Output: for mode nostop / stop: residue keys by kind, by PTcorpus status (row / no row by reason / outside the K1 list), recursor names,
per-root statistics, the three Signal roots, and the stopped primitives with the Dyn (Type 0) verdict."""
import sys, glob, os, collections
rp = sys.argv[1]; repo = sys.argv[2] if len(sys.argv) > 2 else "."
def tsv(f): return [l.rstrip("\n").split("\t") for l in open(os.path.join(repo, "scripts/gen5", f))]
rows = {(r[0], r[2]) for r in tsv("ptcorpus_keys.tsv")} | {(r[0], r[2]) for r in tsv("ptcorpus_closure.tsv")}
miss = {(r[0], r[2]): r[3] for r in tsv("ptcorpus_missing.tsv")}
def short(w):
    for a, b in [("binder above", "binder above Type 0"), ("constant not in", "corpus declaration"), ("inductive family", "family not Type 0"),
                 ("proof binder", "proof binder"), ("recursor", "recursor"), ("result type", "result above Type 0")]:
        if w.startswith(a): return b
    return w
tags = sorted(p.rsplit(".stopkey.", 1)[1] for p in glob.glob(rp + ".stopkey.*"))
print("drivers:", tags)
keys = {"nostop": {}, "stop": {}}
for t in tags:
    if t == "Sig": continue
    for l in open(f"{rp}.stopkey.{t}"):
        m, n, kind, lv, c = l.rstrip("\n").split("\t"); keys[m][(n, lv)] = kind
def classify(n, lv):
    if (n, lv) in rows: return "has a row"
    if (n, lv) in miss: return "no row: " + short(miss[(n, lv)])
    return "outside K1 list"
def report(title, ks):
    print(f"\n== {title}: {len(ks)} residue keys")
    bykind = collections.Counter(ks.values())
    print("  by kind:", dict(sorted(bykind.items())))
    cl = collections.Counter(classify(n, lv) for (n, lv) in ks)
    for k, v in sorted(cl.items()): print(f"  {k}: {v}")
    recs = sorted(n for (n, lv), k in ks.items() if k == "rec")
    print(f"  recursors ({len(recs)}):", recs)
for mode in ["nostop", "stop"]:
    report(f"corpus, {mode} (drivers {[t for t in tags if t != 'Sig']})", keys[mode])
print("\n== difference of the corpus residue (nostop minus stop): keys that disappear")
gone = {k: v for k, v in keys["nostop"].items() if k not in keys["stop"]}
new = [k for k in keys["stop"] if k not in keys["nostop"]]
print("  disappear:", len(gone), "; appear (must be 0):", len(new))
cl = collections.Counter(classify(n, lv) for (n, lv) in gone); print("  by status:", dict(sorted(cl.items())))
print("  by kind:", dict(collections.Counter(gone.values())))
# per root
pr = {"nostop": collections.defaultdict(set), "stop": collections.defaultdict(set)}
roots = {}
for t in tags:
    for l in open(f"{rp}.stopreach.{t}"):
        m, r, n, kind, lv, closed = l.rstrip("\n").split("\t"); pr[m][(t if t == "Sig" else "C", r)].add((n, lv, kind))
    for l in open(f"{rp}.stoproots.{t}"):
        m, r, mod, cnt, st = l.rstrip("\n").split("\t"); roots[(m, t if t == "Sig" else "C", r)] = (mod, int(cnt), int(st))
corp = {r for (g, r) in pr["nostop"] if g == "C"}
mods = {roots[("nostop", "C", r)][0] for r in corp}
print(f"\n== per root (corpus): {len(corp)} root names, {len(mods)} modules")
for mode in ["nostop", "stop"]:
    nrec = [sum(1 for k in pr[mode][("C", r)] if k[2] == "rec") for r in corp]
    nnorow = [sum(1 for k in pr[mode][("C", r)] if classify(k[0], k[1]).startswith("no row")) for r in corp]
    tot = [len(pr[mode][("C", r)]) for r in corp]
    print(f"  {mode}: residue keys per root max {max(tot)} sum {sum(tot)}; roots reaching >=1 recursor {sum(1 for x in nrec if x)}; roots with >=1 key without a row {sum(1 for x in nnorow if x)}; max keys without a row {max(nnorow)}")
    sn = [roots[(mode, "C", r)][2] for r in corp]
    print(f"      roots that stop at >=1 Signal primitive: {sum(1 for x in sn if x)}")
print("\n== the three Signal roots (Tests.SignalLoopTest)")
for r in sorted(r for (g, r) in pr["nostop"] if g == "Sig"):
    for mode in ["nostop", "stop"]:
        ks = pr[mode][("Sig", r)]
        c = collections.Counter(classify(n, lv) for (n, lv, k) in ks)
        recs = sorted({n for (n, lv, k) in ks if k == "rec"})
        print(f"  {r.split('.')[-1]} {mode}: reached {len(ks)}; " + "; ".join(f"{a} {b}" for a, b in sorted(c.items())) + f"; recursors {recs}")
        no = sorted(f"{n}{lv}" for (n, lv, k) in ks if classify(n, lv).startswith("no row"))
        print(f"      without a row: {no}")
print("\n== stopped primitives (distinct (name, ls); roots = how many roots stop there) and Dyn (Type 0) verdict")
agg = collections.defaultdict(lambda: [0, ""])
for t in tags:
    for l in open(f"{rp}.stoppedrows.{t}"):
        n, lv, c, v = l.rstrip("\n").split("\t"); agg[(n, lv)][0] += int(c); agg[(n, lv)][1] = v
for (n, lv), (c, v) in sorted(agg.items()): print(f"  {n} {lv}: roots {c}: {v}")
print(f"  total {len(agg)}; fit Dyn: {sum(1 for x in agg.values() if x[1]=='fits')}; do not fit: {sum(1 for x in agg.values() if x[1]!='fits')}")
