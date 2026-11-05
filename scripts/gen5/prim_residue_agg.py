#!/usr/bin/env python3
"""D.D-4 res2: aggregate the per-file outputs of scripts/gen5/prim_residue_dyn.sh.
usage: prim_residue_agg.py RAWROOT CLOSURE_MODULES_FILE   (RAWROOT holds out*/ directories)"""
import glob, os, sys, collections, json

root, closure_file = sys.argv[1], sys.argv[2]
closure = set(l.strip() for l in open(closure_file) if l.strip())
USER_PREFIX = ("Tests.", "Examples", "IP.", "Tools.Test", "<local>")

status = {}
for sf in glob.glob(f"{root}/out*/status.tsv"):
    for l in open(sf):
        f, rc, secs, nout, nerr = l.rstrip("\n").split("\t")
        status[f] = (int(rc), int(secs), int(nout), int(nerr))

def tag(f): return f.replace("/", "_")[:-5]
roots = {}            # name -> dict(routes:set, files:set, residue:set)
consts = {}           # name -> (kind, arity, module)
partial = collections.Counter(); full = collections.Counter()
recsites = collections.Counter()
prof_status = collections.Counter()
missing = collections.Counter()
file_roots = collections.defaultdict(set)
for f, (rc, secs, nout, nerr) in status.items():
    t = tag(f)
    if rc != 0 and not os.environ.get("AGG_ALL"): continue   # only files whose standalone run succeeded (rc 0) count as successful compiles
    d = glob.glob(f"{root}/out*/raw/{t}")
    base = None
    for b in glob.glob(f"{root}/out*/raw/{t}.roots"):
        base = b[:-6]
    if base is None: continue
    for l in list(open(base + ".roots"))[1:]:
        p = l.rstrip("\n").split("\t")
        if len(p) < 7: continue
        name, routes, mod, unf, nres, nrec, res = p[0], p[1].split(","), p[2], int(p[3]), int(p[4]), int(p[5]), p[6].split()
        r = roots.setdefault(name, dict(routes=set(), files=set(), residue=set(), unfolded=0))
        r["routes"].update(routes); r["files"].add(f); r["residue"].update(res); r["unfolded"] = max(r["unfolded"], unf)
        file_roots[f].add(name)
    for l in list(open(base + ".consts"))[1:]:
        p = l.rstrip("\n").split("\t")
        if len(p) < 6: continue
        consts[p[0]] = (p[1], int(p[2]), p[3])
        partial[p[0]] = max(partial[p[0]], int(p[4])); full[p[0]] = max(full[p[0]], int(p[5]))
    if os.path.exists(base + ".recsites"):
        for l in list(open(base + ".recsites"))[1:]:
            p = l.rstrip("\n").split("\t")
            if len(p) >= 3: recsites[(p[0], p[1], p[2])] += 1
    if os.path.exists(base + ".prof"):
        for l in list(open(base + ".prof"))[1:]:
            p = l.rstrip("\n").split("\t")
            if len(p) == 3: prof_status[p[2]] += 1
    if os.path.exists(base + ".missing"):
        for l in open(base + ".missing"):
            if l.strip(): missing[(f, l.strip())] += 1

def modof(f): return f[:-5].replace("/", ".")
out = {}
out["files_total"] = len(status)
out["files_rc0"] = sum(1 for v in status.values() if v[0] == 0)
out["files_failed"] = sorted((f, v[0], v[3]) for f, v in status.items() if v[0] != 0)
out["files_in_closure"] = sum(1 for f in status if modof(f) in closure)
out["files_outside_closure"] = sum(1 for f in status if modof(f) not in closure)
out["roots"] = len(roots)
rc = collections.Counter()
for n, r in roots.items():
    for x in r["routes"]: rc[x] += 1
out["roots_by_route_tag"] = dict(rc)
fe = {"S0", "mixed", "machine"}
out["roots_certified_fe"] = sum(1 for r in roots.values() if r["routes"] & fe)
out["roots_legacy_only"] = sorted(n for n, r in roots.items() if "legacy" in r["routes"] and not (r["routes"] & fe))
out["roots_memo_only"] = sorted(n for n, r in roots.items() if "memo" in r["routes"] and not (r["routes"] & (fe | {"legacy"})))
out["roots_marker_only"] = sum(1 for r in roots.values() if not (r["routes"] & (fe | {"legacy", "memo"})))
kinds = collections.Counter(v[0] for v in consts.values())
out["consts"] = len(consts); out["consts_by_kind"] = dict(kinds)
lib = sum(1 for v in consts.values() if not v[2].startswith(USER_PREFIX)); out["consts_lib"] = lib; out["consts_user"] = len(consts) - lib
out["recursors"] = sorted(n for n, v in consts.items() if v[0] == "recursor")
# roots needing each constant
need = collections.Counter()
for r in roots.values():
    for c in r["residue"]: need[c] += 1
out["roots_without_recursor"] = sum(1 for r in roots.values() if not any(consts.get(c, ("",))[0] == "recursor" for c in r["residue"]))
out["recursor_root_counts"] = {c: need[c] for c in out["recursors"]}
out["partial_consts"] = {c: partial[c] for c in partial if partial[c] > 0}
out["recsites_total"] = sum(recsites.values())
mj = collections.Counter()
for (rn, lv, m), k in recsites.items(): mj[m] += k
out["recsites_major"] = dict(mj)
out["prof_status"] = dict(prof_status)
out["missing_names"] = sorted(set(f"{f}: {n}" for (f, n) in missing))[:200]
suffix = "_all" if os.environ.get("AGG_ALL") else ""
def union(rs): 
    u = set()
    for r in rs: u |= r["residue"]
    return u
cert = [r for r in roots.values() if r["routes"] & fe]
leg = [r for r in roots.values() if "legacy" in r["routes"] and not (r["routes"] & fe)]
inc = [r for r in roots.values() if any(modof(f) in closure for f in r["files"])]
def kc(u):
    c = collections.Counter(consts.get(x, ("?",))[0] for x in u); return dict(c)
out["residue_certified_roots"] = (len(union(cert)), kc(union(cert)))
out["residue_legacy_only_roots"] = (len(union(leg)), kc(union(leg)))
out["residue_closure_roots"] = (len(union(inc)), kc(union(inc)))
out["residue_all"] = (len(union(roots.values())), kc(union(roots.values())))
out["only_legacy"] = sorted(union(leg) - union(cert))
out["only_outside_closure"] = sorted(union(roots.values()) - union(inc))
out["roots_per_residue_size"] = [min(len(r["residue"]) for r in roots.values() if r["residue"]), sorted(len(r["residue"]) for r in roots.values())[len(roots)//2], max(len(r["residue"]) for r in roots.values())]
json.dump(out, open(f"{root}/agg{suffix}.json", "w"), indent=1, ensure_ascii=False, default=list)
# per-const table for the report
with open(f"{root}/agg_consts{suffix}.tsv", "w") as w:
    w.write("name\tkind\tarity\tmodule\troots\tpartial\tfull\n")
    for c, v in sorted(consts.items(), key=lambda kv: (-need[kv[0]], kv[0])):
        w.write(f"{c}\t{v[0]}\t{v[1]}\t{v[2]}\t{need[c]}\t{partial[c]}\t{full[c]}\n")
with open(f"{root}/agg_roots{suffix}.tsv", "w") as w:
    w.write("root\troutes\tfiles\tresidue\n")
    for n, r in sorted(roots.items()):
        w.write(f"{n}\t{','.join(sorted(r['routes']))}\t{len(r['files'])}\t{len(r['residue'])}\n")
for k, v in out.items():
    s = json.dumps(v, ensure_ascii=False, default=list)
    print(k, ":", s if len(s) < 400 else s[:400] + "…")
