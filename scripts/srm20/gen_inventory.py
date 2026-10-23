#!/usr/bin/env python3
# SRM20 G1: regenerate scripts/srm20/INVENTORY.txt from the S20INV/S20CONCL/S20DEF/S20DEFB lines of a build log of Tests.Compiler.Srm20InventoryTest.
# usage (repo root):  ./.cluster/qbuild.sh build Tests.Compiler.Srm20InventoryTest > LOG 2>&1;  python3 scripts/srm20/gen_inventory.py LOG
import re,sys
out=[]
for l in open(sys.argv[1]).read().split('\n'):
    m=re.search(r'(S20(?:INV|CONCL|DEF|DEFB)\|.*)$',l)
    if m: out.append(m.group(1))
open('scripts/srm20/INVENTORY.txt','w').write('\n'.join(out)+'\n')
print(len(out),'lines')
