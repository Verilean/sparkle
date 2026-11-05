#!/usr/bin/env python3
"""Merge the per-driver raw rows of RowTypedKAudit (main43, M1..M4) into the whole-corpus audit count (a META AUDIT, not a proof).
usage: merge_row_typed_audit.py REPORT_PATH   (reads REPORT_PATH.audit.TAG; if REPORT_PATH.key.TAG from PrimResidueKey exist, cross-checks the key set)
row: name \\t kind \\t lsKey \\t arity \\t const \\t spine \\t sort \\t binders"""
import sys, glob, collections
rp = sys.argv[1]
tags = sorted(p.rsplit(".audit.", 1)[1] for p in glob.glob(rp + ".audit.*"))
rows = {}; conflict = 0
for t in tags:
    for l in open(f"{rp}.audit.{t}"):
        if not l.strip(): continue
        f = l.rstrip("\n").split("\t")
        k = (f[0], f[2])
        if k in rows and rows[k] != f: conflict += 1
        rows[k] = f
print("drivers:", tags)
print(f"audited keys (union): {len(rows)}; keys whose rows differ between drivers: {conflict}")
for col, name in [(1, "kind"), (3, "arity"), (4, "const inferType vs instantiateLevelParams"), (5, "spine (all prefixes) inferType vs instForall"), (6, "sort of declared type")]:
    c = collections.Counter(r[col] for r in rows.values())
    print(f"{name}: " + ", ".join(f"{k} {v}" for k, v in sorted(c.items())))
term = [r for r in rows.values() if r[1] != "induct"]
tyk = [r for r in rows.values() if r[1] == "induct"]
print(f"term keys (OblRowTypedK; ctor/rec/quot/axiom/opaque): {len(term)}; type-former keys (induct, `tys` rows): {len(tyk)}")
ct = collections.Counter(r[6] for r in term)
print("term keys, sort of declared type: " + ", ".join(f"{k} {v}" for k, v in sorted(ct.items())))
mism = [k for k, r in rows.items() if "mismatch" in (r[4], r[5]) or r[3] != "ok"]
print(f"keys with arity != ok or any mismatch: {len(mism)}", mism[:5])
keyfiles = glob.glob(rp + ".key.*")
if keyfiles:
    exp = set()
    for p in keyfiles:
        for l in open(p):
            f = l.split("\t"); exp.add((f[0], f[2]))
    print(f"cross-check against PrimResidueKey key rows: {len(exp)} keys; only in audit {len(set(rows)-exp)}; only in residue {len(exp-set(rows))}")
# --- D.D-4 Rows: classification of the term keys (columns 8 = shape nullary/nondep/dep, 6 = sort class of the declared type)
def cls(r):
    if r[6] == "Prop": return "Prop"
    if r[6] == "Type0": return "Type0/" + r[8]
    return "den=none (higher)"
cc = collections.Counter(cls(r) for r in term)
print("term keys by class: " + ", ".join(f"{k} {v}" for k, v in sorted(cc.items())))
proved = {"Nat.zero", "Bool.false", "Bool.true", "PUnit.unit", "Sparkle.Core.Domain.ActiveEdge.rising", "Sparkle.IR.Type.ResetKind.synchronous"}
shape = {"Nat.succ", "Int.ofNat", "Int.negSucc", "Sparkle.Core.Domain.DomainConfig.mk"}
t0 = [r for r in term if r[6] == "Type0"]
print("Type0 nullary keys: " + ", ".join(sorted(r[0] for r in t0 if r[8] == "nullary")))
print("Type0 nondep keys: " + ", ".join(sorted(r[0] for r in t0 if r[8] == "nondep")))
pn = sorted(r[0] for r in t0 if r[8] == "nullary" and r[0] not in proved)
sn = sorted(r[0] for r in t0 if r[8] == "nondep" and r[0] not in shape)
print(f"proved-set keys missing from the Type0 nullary class: {sorted(proved - {r[0] for r in t0 if r[8]=='nullary'})}; nullary not proved: {pn}")
print(f"shape-set keys missing from the Type0 nondep class: {sorted(shape - {r[0] for r in t0 if r[8]=='nondep'})}; nondep without a shape proof: {sn}")
print(f"proved {len([r for r in t0 if r[8]=='nullary' and r[0] in proved])}; bridge-waiting {len([r for r in t0 if r[8]!='nullary'])} (nondep {len([r for r in t0 if r[8]=='nondep'])}, dep {len([r for r in t0 if r[8]=='dep'])}); den=none/Prop {len(term)-len(t0)}")
print("dependent Type0 keys: " + ", ".join(sorted(r[0] for r in t0 if r[8] == "dep")))
