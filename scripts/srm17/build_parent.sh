#!/bin/sh
# regenerates Tests/Compiler/Srm17ParentTest.lean
{ cat scripts/srm17/header_parent.txt scripts/srm16/opens_parent.txt scripts/srm17/body_parent.txt
  python3 scripts/srm17/gen_parent.py
  echo; echo "end Tests.Compiler.SharedLeafMemKidIfaceTest"; echo
  for d in topshareM topshareQ; do for t in modP hIUraw hIU hAg hRd; do echo "#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.${d}_$t"; done; done
  for b in topshareM_svBoundsH topshareQ_svBoundsH topshareM_designSVH topshareQ_designSVH; do echo "#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.${b}_viaResetSrc"; done
} > Tests/Compiler/Srm17ParentTest.lean
