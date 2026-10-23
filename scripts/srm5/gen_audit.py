#!/usr/bin/env python3
# SRM5: regenerate the EXPECTED block of Tests/Compiler/Srm5AuditTest.lean and scripts/srm5/PREMISES.txt from the S5PREM/S5DATA/S5HYPS lines of a build log of that test.
# usage: python3 scripts/srm5/gen_audit.py <build-log>
import re,sys
log=open(sys.argv[1]).read().split('\n')
rows=[];hyps=[]
for l in log:
    m=re.search(r'(S5(?:PREM|DATA)\|.*)$',l)
    if m: rows.append(m.group(1))
    m=re.search(r'S5HYPS\|([^|]+)\|(.*)$',l)
    if m: hyps.append((m.group(1),[x.strip() for x in m.group(2).split(',') if x.strip()]))
open('scripts/srm5/PREMISES.txt','w').write('\n'.join(rows)+'\n')
blk='-- BEGIN EXPECTED\ndef expectedPrem : List (Name × List String) :=\n  ['+',\n   '.join('(`%s, [%s])'%(t,', '.join('"%s"'%h for h in hs)) for t,hs in hyps)+']\n-- END EXPECTED'
p='Tests/Compiler/Srm5AuditTest.lean'
s=open(p).read()
i=s.index('-- BEGIN EXPECTED'); j=s.index('-- END EXPECTED')+len('-- END EXPECTED')
open(p,'w').write(s[:i]+blk+s[j:])
print(len(rows),'rows',len(hyps),'theorems')
