#!/usr/bin/env python3
# SRM21 G1: regenerate scripts/srm21/INVENTORY.txt from the S21INV/S21CONCL/S21DEF/S21DEFB lines of a build log of Tests.Compiler.Srm21InventoryTest.
# usage (repo root):  ./.cluster/qbuild.sh build Tests.Compiler.Srm21InventoryTest > LOG 2>&1;  python3 scripts/srm21/gen_inventory.py LOG
import re,sys
out=[]
for l in open(sys.argv[1]).read().split('\n'):
    m=re.search(r'(S21(?:INV|CONCL|DEF|DEFB)\|.*)$',l)
    if m: out.append(m.group(1))
open('scripts/srm21/INVENTORY.txt','w').write('\n'.join(out)+'\n')
print(len(out),'lines')
