#!/usr/bin/env python3
"""Count B4 (hdisjD) violations in emitted Verilog.

usage: b4_shared_desc.py OUT_DIR   (OUT_DIR = pass-1 outputs of scripts/shipping-coverage/run.sh)

Per file: modules and the module names each instantiates.  For a module P and two
of its instances of DIFFERENT modules A != B, B4 fails when
  A is in desc*(B), or B is in desc*(A), or desc*(A) & desc*(B) != {}
where desc*(X) = X and every module reachable from X.  (Same module called twice
is not a violation: B4 is premised on different callee or memKey; the Verilog
name stands for the callee, so different memKeys of one callee are not seen.)
Reported with and without memory modules (names starting SparkleMem_).
"""
import os, re, sys
INST = re.compile(r'^\s*([A-Za-z_][A-Za-z0-9_$]*)\s+(?:#\(.*?\)\s*)?([A-Za-z_][A-Za-z0-9_$]*)\s*\(\s*\.')
KW = {'module','input','output','inout','wire','reg','assign','always','if','else','function','task','case','for','initial','localparam','parameter'}
def parse(path):
    mods = {}; cur = None
    for line in open(path, errors='replace'):
        s = line.strip()
        m = re.match(r'^module\s+([A-Za-z_][A-Za-z0-9_$]*)', s)
        if m: cur = m.group(1); mods.setdefault(cur, set()); continue
        if s.startswith('endmodule'): cur = None; continue
        if cur:
            i = INST.match(line)
            if i and i.group(1) not in KW: mods[cur].add(i.group(1))
    return mods
def desc(mods, x, memo):
    if x in memo: return memo[x]
    memo[x] = {x}; r = {x}
    for c in mods.get(x, ()): r |= desc(mods, c, memo)
    memo[x] = r; return r
def violations(mods, skipmem):
    memo = {}; out = []
    def keep(n): return not (skipmem and n.startswith('SparkleMem_'))
    for p, kids in mods.items():
        ks = sorted(k for k in kids if keep(k))
        for i in range(len(ks)):
            for j in range(i + 1, len(ks)):
                a, b = ks[i], ks[j]
                da = {n for n in desc(mods, a, memo) if keep(n)}
                db = {n for n in desc(mods, b, memo) if keep(n)}
                sh = da & db
                if sh: out.append((p, a, b, sorted(sh)))
    return out
d = sys.argv[1]
files = sorted(f for f in os.listdir(d))
withv = hier = 0; hit = {False: [], True: []}
for f in files:
    mods = parse(os.path.join(d, f))
    if not mods: continue
    withv += 1
    if any(mods.values()): hier += 1
    for sk in (False, True):
        v = violations(mods, sk)
        if v: hit[sk].append((f, v))
print(f"files {len(files)}; with Verilog {withv}; with at least one instance {hier}")
for sk in (False, True):
    print(f"== B4 violated ({'memory modules excluded' if sk else 'all modules'}): {len(hit[sk])} files")
    for f, v in hit[sk]:
        print(f"  {f}: {len(v)} pairs; e.g. {v[0][0]}: {v[0][1]} / {v[0][2]} share {v[0][3][:4]}")
