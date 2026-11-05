#!/usr/bin/env python3
"""Merge the per-driver raw rows of PrimResidueKey (main43, M1..M4) into the whole-corpus count.
usage: merge_prim_residue_key.py REPORT_PATH [REPO_ROOT]   (reads REPORT_PATH.key.TAG / .roots.TAG)"""
import sys, glob, re, os, collections
rp = sys.argv[1]; repo = sys.argv[2] if len(sys.argv) > 2 else "."
tags = sorted(p.rsplit(".key.", 1)[1] for p in glob.glob(rp + ".key.*"))
keys = {}; roots = {}
for t in tags:
    for l in open(f"{rp}.key.{t}"):
        n, kind, lv, _, _ = l.rstrip("\n").split("\t")
        keys[(n, lv)] = kind
    for l in open(f"{rp}.roots.{t}"):
        r, m, left, kind = l.rstrip("\n").split("\t")
        roots[(r, m)] = kind; assert left == "0"
expected = set()
for f in glob.glob(os.path.join(repo, "Tests/*/*.lean")):
    if any(re.match(r"#machine_endpoint", l) for l in open(f)):
        expected.add(os.path.splitext(os.path.relpath(f, repo))[0].replace("/", "."))
mods = {m for (_, m) in roots}
rnames = {r for (r, _) in roots}
names = collections.defaultdict(set)
for (n, lv), kind in keys.items(): names[n].add(lv)
print("drivers:", tags)
nsrc = sum(1 for k in roots.values() if k == "source")
print(f"count: {len(rnames)} distinct root names ({len(roots)} (root, module) pairs: {nsrc} source, {len(roots)-nsrc} sound-only), {len(mods & expected)}/{len(expected)} modules with roots (#machine_endpoint modules); {len(mods - expected)} other modules with roots (transitive imports)")
print("missing modules:", sorted(expected - mods))
print(f"residue rows: Name-only {len(names)}; Name x List Level {len(keys)}; extra {len(keys)-len(names)}")
for k in ["ctor", "rec", "induct", "quot", "axiom", "opaque"]:
    nk = sum(1 for n in names if next(keys[(n, lv)] for lv in names[n]) == k)
    kk = sum(1 for v in keys.values() if v == k)
    print(f"  {k}: names {nk}, keys {kk}")
multi = sorted(((len(s), n) for n, s in names.items() if len(s) > 1), key=lambda x: (-x[0], x[1]))
print(f"names with >1 distinct ls: {len(multi)} of {len(names)}")
for c, n in multi: print(f"  {n} {c}")
