#!/usr/bin/env python3
# SRM22 G1: regenerate scripts/srm22/INVENTORY.txt from the S22INV/S22CONCL/S22DEF/S22DEFB lines of a build log of Tests.Compiler.Srm21InventoryTest.
# usage (repo root):  ./.cluster/qbuild.sh build Tests.Compiler.Srm21InventoryTest > LOG 2>&1;  python3 scripts/srm22/gen_inventory.py LOG
import re,sys
out=[]
for l in open(sys.argv[1]).read().split('\n'):
    m=re.search(r'(S22(?:INV|CONCL|DEF|DEFB|LOC)\|.*)$',l)
    if m: out.append(m.group(1))
open('scripts/srm22/INVENTORY.txt','w').write('\n'.join(out)+'\n')
print(len(out),'lines')
