#!/bin/sh
# regenerates Tests/Compiler/Srm18ParentTest.lean
{ cat scripts/srm18/header_parent.txt scripts/srm16/opens_parent.txt
  echo "open Tools.ShippingSrm18Start"
  cat scripts/srm18/body_parent.txt
  python3 scripts/srm18/gen_parent.py
  echo; echo "end Tests.Compiler.SharedLeafMemKidIfaceTest"; echo
  for d in topshareM topshareQ; do echo "#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.${d}_hsk_not_forced"; done
  for b in topshareM_svBoundsH topshareQ_svBoundsH topshareM_designSVH topshareQ_designSVH; do echo "#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.${b}_viaStartNk"; done
  echo "#print axioms Tools.ShippingSrm18Start.bumpedStart_spec"
  echo "#print axioms Tools.ShippingSrm18Start.runModuleTG_kids_congr"
} > Tests/Compiler/Srm18ParentTest.lean
