#!/bin/sh
# regenerates Tests/Compiler/Srm16ParentTest.lean
{ cat scripts/srm16/header_parent.txt scripts/srm16/opens_parent.txt scripts/srm16/hO_parent.txt
  python3 scripts/srm16/gen_parent.py
  echo; echo "end Tests.Compiler.SharedLeafMemKidIfaceTest"; echo
  for t in topshareM_hO topshareQ_hO; do echo "#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.$t"; done
  for b in topshareM_svBoundsH topshareQ_svBoundsH topshareM_designSVH topshareQ_designSVH; do for v in viaResetO viaResetState; do echo "#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.${b}_$v"; done; done
} > Tests/Compiler/Srm16ParentTest.lean
