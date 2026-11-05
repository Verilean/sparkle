#!/usr/bin/env python3
"""D.D-4 res3: aggregate the log_*.txt of scripts/gen5/iota_probe_batch.sh.  usage: iota_probe_agg.py PROBEDIR"""
import glob, re, sys, collections
d = sys.argv[1]
tot = collections.Counter(); failed = []; stuck = collections.Counter(); fb = collections.Counter()
for f in sorted(glob.glob(f"{d}/log_*.txt")):
    t = open(f).read()
    m = re.search(r"roots (\d+)\.\.(\d+).*FINISHED within fuel: (\d+); FAILED \(out of fuel, no partial result\): (\d+); finished roots with a stuck recursor site: (\d+)", t)
    if not m: print("NOPARSE", f); continue
    a, b, fi, fa, sr = map(int, m.groups())
    tot["roots"] += b - a; tot["finished"] += fi; tot["failed"] += fa; tot["finished_with_stuck"] += sr
    m = re.search(r"failed roots: \[(.*?)\]\n", t)
    if m and m.group(1).strip(): failed += [x.strip() for x in m.group(1).split(",")]
    m = re.search(r"steps (\d+), Nat-literal accelerations (\d+), iota fired (\d+) by \[(.*?)\]\n", t)
    tot["steps"] += int(m.group(1)); tot["natAccel"] += int(m.group(2)); tot["iotaFired"] += int(m.group(3))
    for k, v in re.findall(r"\(\"?([\w.]+)\"?, (\d+)\)", m.group(4)): fb[k] += int(v)
    m = re.search(r"stuck recursor sites by major shape: \[(.*?)\]\n", t)
    for k, v in re.findall(r"\(\"?([\w:\-]+)\"?, (\d+)\)", m.group(1)): stuck[k] += int(v)
print(dict(tot)); print("fired by", dict(fb)); print("stuck", dict(stuck)); print("failed", len(failed))
for x in failed: print(" ", x)
