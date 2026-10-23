import Tests.Compiler.Srm19EndToEndTest
import Tests.Compiler.Srm9ComposedTest
import Tests.Compiler.Srm4ComposedTest
import Tests.Compiler.Srm4ComposedQTest
import Tools.ShippingComposedGW
import Tools.ShippingShipsFree
import Tools.ShippingMachineShipsDepth
set_option autoImplicit false
-- UNBUILT (unit SRM20) until a run is recorded in STATUS-SRM20.md.
-- SCOPE: G1 INVENTORY ONLY (no theorem).  It prints, for each listed constant, the machine-generated lines
--   S20INV|<const>|<i>|<binderInfo>|<name>|<type>   (binders of the TYPE; `S20CONCL|<const>|<conclusion>`)  and, for definitions,
--   S20DEF|<const>|<body after its lambda binders>.
-- Regenerate scripts/srm20/INVENTORY.txt with `python3 scripts/srm20/gen_inventory.py LOG` after building this module.
section
open Lean Elab Command Meta
namespace Tests.Compiler.Srm20InventoryTest

def thms : List Name :=
  [``Tools.ShippingMachineShipsDepth.composedG_of_NW,
   ``Tools.ShippingMachineShipsHier.composedG_of_T,
   ``Tools.ShippingMachineShipsHier.composedG_of_Tmem,
   ``Tools.ShippingComposedGW.composedGW_of_T,
   ``Tools.ShippingComposedGW.ComposedGW.toG,
   ``Tools.ShippingShipsFree.machine_ships_hierC_at_free,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_composedNW,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_composedNW,
   ``Tests.Compiler.Srm9ComposedTest.topshareM_composed_binder,
   ``Tests.Compiler.Srm9ComposedTest.topshareQ_composed_binder,
   ``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free,
   ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_endToEnd,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_endToEnd]

def defs : List Name :=
  [``Tools.ShippingMachineShipsHier.ComposedG,
   ``Tools.ShippingComposedGW.ComposedGW,
   ``Tools.ShippingMachineDepthRun.ComposedNW,
   ``Tools.ShippingMachineShipsDepth.ResetNk,
   ``Tools.ShippingMachineDepth.ResetN,
   ``Tools.ShippingHierStateG.KT,
   ``Tools.ShippingHierStateG.KSn,
   ``Tests.Compiler.Srm9ComposedTest.TmBnd,
   ``Tests.Compiler.Srm9ComposedTest.TqBnd]

def one (s : String) : String := s.replace "\n" " "

def dumpThm (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs concl => do
    let mut i : Nat := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let bi := match d.binderInfo with
        | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst" | .default => "explicit"
      logInfo m!"S20INV|{n}|{i}|{bi}|{d.userName}|{one ((← ppExpr d.type).pretty 100000)}"
      i := i + 1
    logInfo m!"S20CONCL|{n}|{one ((← ppExpr concl).pretty 100000)}"

def dumpDef (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  match ci.value? with
  | none => logInfo m!"S20DEF|{n}|(no value: {ci.isInductive})"
  | some v =>
    lambdaTelescope v fun xs b => do
      logInfo m!"S20DEF|{n}|binders={xs.size}|{one ((← ppExpr b).pretty 100000)}"
      forallTelescope ci.type fun ys _ => do
        let mut i : Nat := 0
        for y in ys do
          let d ← y.fvarId!.getDecl
          logInfo m!"S20DEFB|{n}|{i}|{d.userName}|{one ((← ppExpr d.type).pretty 100000)}"
          i := i + 1

run_meta do
  for n in thms do dumpThm n
  for n in defs do dumpDef n

end Tests.Compiler.Srm20InventoryTest
end
