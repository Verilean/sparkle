#!/usr/bin/env python3
# Regenerates the hand-copied FULL expected statements (as `def Exp_<thm> : Prop := ∀ binders, concl`) between the markers of Tests/Compiler/Srm14AuditTest.lean
# from the signatures in Tests/Compiler/Srm14RankTest.lean (text copy, no proof terms).
import re,sys
rt=open('Tests/Compiler/Srm14RankTest.lean').read()
out=[]
for m in re.finditer(r'theorem (\w+)(.*?) :=\n',rt,re.S):
    name,sig=m.group(1),m.group(2)
    i=sig.rindex(' :\n')
    binders,concl=sig[:i],sig[i+3:].strip()
    out.append(f"def Exp_{name} : Prop :=\n  ∀{binders},\n    {concl}\n")
txt=open('Tests/Compiler/Srm14AuditTest.lean').read()
a='-- BEGIN EXPSTMT\n'; b='-- END EXPSTMT\n'
pre=txt[:txt.index(a)+len(a)]; post=txt[txt.index(b):]
open('Tests/Compiler/Srm14AuditTest.lean','w').write(pre+'\n'.join(out)+post)
