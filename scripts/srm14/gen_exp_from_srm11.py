#!/usr/bin/env python3
# Derives the expected FULL statements Exp_<thm>_computed of Tests/Compiler/Srm14AuditTest.lean (between the EXPSTMT markers)
# from the ORIGINAL SRM11 statements ONLY (reads Tests/Compiler/Srm11ParentTest.lean; never reads SRM14 sources), by an explicit substitution/deletion list.
import re
SUBST = {'topshareM_svBoundsH': 'rkOf gM 4', 'topshareM_designSVH_noB': 'rkOf gM 4',
         'topshareQ_svBoundsH': 'rkOf gQ 3', 'topshareQ_designSVH_noB': 'rkOf gQ 3'}   # rk := ...
DELETE = ['rk', 'hrkmem', 'hrT', 'hrW', 'hrW3', 'hrP', 'hrQ', 'hrL']                   # binders deleted (one line each in the SRM11 file)
print('SUBSTITUTION (rk :=):', SUBST); print('DELETED BINDERS:', DELETE)
src = open('Tests/Compiler/Srm11ParentTest.lean').read()
out = []
for name, rkv in SUBST.items():
    m = re.search(r'^theorem ' + name + r'\b(.*?) :=', src, re.S | re.M)
    sig = m.group(1)
    i = sig.rindex(') :\n')
    binders, concl = sig[:i + 1], sig[i + 4:].strip()
    lines = binders.split('\n'); kept = []
    for l in lines:
        d = re.match(r'\s*\((\w+) :', l)
        if d and d.group(1) in DELETE:
            print('delete from', name, ':', l.strip()); continue
        kept.append(l)
    concl = re.sub(r'\brk\b', '(' + rkv + ')', concl)
    out.append(f"def Exp_{name}_computed : Prop :=\n  ∀{chr(10).join(kept)},\n    {concl}\n")
f = 'Tests/Compiler/Srm14AuditTest.lean'
txt = open(f).read(); a = '-- BEGIN EXPSTMT\n'; b = '-- END EXPSTMT\n'
open(f, 'w').write(txt[:txt.index(a) + len(a)] + '\n'.join(out) + txt[txt.index(b):])
