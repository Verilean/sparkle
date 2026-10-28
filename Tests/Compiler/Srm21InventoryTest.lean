import Tests.Compiler.Srm20BridgeTest
import Tests.Compiler.Srm12CorrTest
import Tools.ShippingSrm17Ran
import Tools.ShippingSrm16Reset
import Tests.Compiler.Srm9ComposedTest
import Tests.Compiler.Srm4ComposedTest
import Tests.Compiler.Srm4ComposedQTest
import Tools.ShippingComposedGW
import Tools.ShippingShipsFree
import Tools.ShippingMachineShipsDepth
set_option autoImplicit false
-- BUILT (unit SRM21): dev runs see STATUS/REPORT.
-- SCOPE: G1 INVENTORY ONLY (no theorem).  It prints, for each listed constant, the machine-generated lines
--   S21INV|<const>|<i>|<binderInfo>|<name>|<type>   (binders of the TYPE; `S21CONCL|<const>|<conclusion>`)  and, for definitions,
--   S21DEF|<const>|<body after its lambda binders>.
-- Regenerate scripts/srm20/INVENTORY.txt with `python3 scripts/srm20/gen_inventory.py LOG` after building this module.
section
open Lean Elab Command Meta
namespace Tests.Compiler.Srm21InventoryTest

def thms : List Name :=
  [``Tools.ShippingHierStateG.runKS_instFree,
   ``Tools.ShippingHierStateG.runModuleTG_instFree,
   ``Tools.ShippingHierStateG.evalAssignsKG_instFree,
   ``Tools.ShippingHierStateG.runKS_succ,
   ``Tools.ShippingSrm3Iface.core_kids_facts_ranAM,
   ``Tools.ShippingSrm17Ran.ran_modP,
   ``Tools.ShippingSrm12Corr.ran_designCorr,
   ``Tools.ShippingSrm12Corr.modCorr_of_run,
   ``Tests.Compiler.Srm12CorrTest.topshareQ_corr,
   ``Tests.Compiler.Srm12CorrTest.topshareQ_inst_ranks,
   ``Tests.Compiler.Srm12CorrTest.gQ_names,
   ``Tests.Compiler.Srm7RankTest.gQ_top,
   ``Tests.Compiler.Srm7RankTest.gQ_wrapP,
   ``Tests.Compiler.Srm7RankTest.gQ_wrapQ,
   ``Tests.Compiler.Srm7RankTest.gQ_leaf,
   ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_underComposedG,
   ``Tools.ShippingMachineLinked.stmtOuts_eq]

def defs : List Name :=
  [``Tools.ShippingHierStateG.KState,
   ``Tools.ShippingHierStateG.KStep,
   ``Tools.ShippingHierStateG.KT,
   ``Tools.ShippingHierStateG.KSn,
   ``Tools.ShippingHierStateG.succKS,
   ``Tools.ShippingHierStateG.flatKS,
   ``Tools.ShippingHierStateG.runKS,
   ``Tools.ShippingHierStateG.runModuleTG,
   ``Tools.ShippingHierStateG.stepModuleTG,
   ``Tools.ShippingHierStateG.evalAssignsKG,
   ``Tools.ShippingHierStateG.stOf,
   ``Tools.ShippingHierStateG.memsOf,
   ``Tools.ShippingHierStateG.instFree,
   ``Tools.ShippingMachineShipsDepth.ResetNk,
   ``Tools.ShippingMachineDepth.ResetN,
   ``Tools.ShippingMachineLinked.childMap,
   ``Sparkle.IR.Machine.moduleByName,
   ``Tools.ShippingSrm12Corr.ModCorr,
   ``Tools.ShippingSrm7Rank.rkOf,
   ``Tools.ShippingSrm16Reset.resetKids,
   ``Tests.Compiler.Srm7RankTest.gQ,
   ``Tests.Compiler.Srm9ComposedTest.TqBnd,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.QDepthLift]

def one (s : String) : String := s.replace "\n" " "

def dumpThm (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs concl => do
    let mut i : Nat := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let bi := match d.binderInfo with
        | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst" | .default => "explicit"
      logInfo m!"S21INV|{n}|{i}|{bi}|{d.userName}|{one ((← ppExpr d.type).pretty 100000)}"
      i := i + 1
    logInfo m!"S21CONCL|{n}|{one ((← ppExpr concl).pretty 100000)}"

def dumpDef (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  match ci.value? with
  | none => logInfo m!"S21DEF|{n}|(no value: {ci.isInductive})"
  | some v =>
    lambdaTelescope v fun xs b => do
      logInfo m!"S21DEF|{n}|binders={xs.size}|{one ((← ppExpr b).pretty 100000)}"
      forallTelescope ci.type fun ys _ => do
        let mut i : Nat := 0
        for y in ys do
          let d ← y.fvarId!.getDecl
          logInfo m!"S21DEFB|{n}|{i}|{d.userName}|{one ((← ppExpr d.type).pretty 100000)}"
          i := i + 1

run_meta do
  for n in thms do dumpThm n
  for n in defs do dumpDef n

end Tests.Compiler.Srm21InventoryTest
end
