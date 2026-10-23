import Tests.Compiler.Srm21LiftTest
import Tests.Compiler.Srm19EndToEndTest
import Tests.Compiler.Srm9ComposedTest
import Tools.ShippingShipsFree
import Tools.ShippingNoPortsTypedI
import Tools.ShippingSatInputs
import Tools.ShippingLeafInputWidths
import Tools.ShippingNonzeroInitWidths
import Tools.ShippingOptSoundness
import Tools.ShippingOptimizePorts
import Tools.ShippingWidthTables
import Tools.ShippingLeafSat
import Tools.ShippingTextTyped
import Tools.ShippingModuleNames
import Tools.ShippingSrm13Supply
import Tools.ShippingInputWiresRun
import Tools.ShippingWireNamesRun
import Tools.ShippingSrm4Core1
import Tools.ShippingOutsExtractedParts
import Tools.ShippingMachineDepthRun
import Tools.ShippingHierOptRunHNoRst
import Tools.ShippingMachineShipsS
import Tools.ShippingSeqOptSoundness
import Tools.ShippingHierOpen
set_option autoImplicit false
-- BUILT (unit SRM22): dev run i1 (exit 0); the final-SHA rebuild in REPORT-SRM22.md is the only final evidence.
-- SCOPE: W1 INVENTORY ONLY (no theorem).  For each listed constant it prints the machine-generated lines
--   S22INV|<const>|<i>|<binderInfo>|<name>|<type>   (binders of the TYPE), `S22CONCL|<const>|<conclusion>`, `S22LOC|<const>|<module>:<line>`
-- and, for definitions, S22DEF|<const>|<body after its lambda binders> and S22DEFB|<const>|<i>|<name>|<type>.
-- Regenerate scripts/srm22/INVENTORY.txt with `python3 scripts/srm22/gen_inventory.py LOG` after building this module.
section
open Lean Elab Command Meta
namespace Tests.Compiler.Srm22InventoryTest

/-- the binder-bearing statements of the two sides -/
def binderThms : List Name :=
  [``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_underComposedG,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_underComposedG,
   ``Tests.Compiler.Srm21LiftTest.topshareQ_svBoundsH_underComposedG',
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_endToEnd,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_endToEnd,
   ``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free,
   ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free,
   ``Tools.ShippingShipsFree.machine_ships_hierC_at_free]

/-- existing width / optimizer / post-processing lemmas relating declWidth, weS, ports, wires, registers -/
def lemmaThms : List Name :=
  [``Tools.ShippingOptimizePorts.optimizeModule_ports,
   ``Tools.ShippingOptimizePorts.deinline_ports,
   ``Tools.ShippingOptimizePorts.checkedOptimize_ports,
   ``Tools.ShippingOptSoundness.checkedOptimize_wires_subset,
   ``Tools.ShippingOptSoundness.checkedOptimize_wires_sublist,
   ``Tools.ShippingNoPortsTypedI.checkedOptimize_ports_wires,
   ``Tools.ShippingNoPortsTypedI.weS_le_of_sub,
   ``Tools.ShippingNoPortsTypedI.weS_checkedOptimize_le,
   ``Tools.ShippingNonzeroInitWidths.weS_eq_of_sub,
   ``Tools.ShippingNonzeroInitWidths.weS_driven_checkedOptimize,
   ``Tools.ShippingLeafInputWidths.declWidth_le_weS_input,
   ``Tools.ShippingSatInputs.declWidth_of_wire,
   ``Tools.ShippingSatInputs.weS_input,
   ``Tools.ShippingWidthTables.declWidth_eq_weS,
   ``Tools.ShippingLeafSat.declWidth_mergeChecked,
   ``Sparkle.IR.RefineCheck.mergeChecked_ports,
   ``Sparkle.IR.RefineCheck.mergeChecked_cases,
   ``Sparkle.IR.RegDedup.mergeDuplicates_ports,
   ``Tools.ShippingModuleNames.checkedOptimize_name,
   ``Tools.ShippingMachineDepthRun.dropZW_name,
   ``Tools.ShippingOutsExtractedParts.dropZW_inputs,
   ``Tools.ShippingOutsExtractedParts.dropZW_wires,
   ``Tools.ShippingWireNamesRun.dropZW_wires_sublist,
   ``Tools.ShippingSrm13Supply.bounded_of_regsAtInit,
   ``Tools.ShippingSrm13Supply.bounded_not_forced,
   ``Tools.ShippingInputWiresRun.inputWires_runMT,
   ``Tools.ShippingWireNamesRun.wireNames_runMT,
   ``Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM,
   ``Tools.ShippingSrm3Iface.core_kids_facts_ranAM,
   ``Tools.ShippingHierOptRunHNoRst.seqRegs_openFlat,
   ``Tools.ShippingHierOptRunHNoRst.seqRegsL_openBody,
   ``Tools.ShippingSeqOptSoundness.seqRegs_eq,
   ``Tools.ShippingMachineShipsS.seqRegs_mem_seqNames]

def defs : List Name :=
  [``Tools.ShippingSrm13Supply.RegsAtInit,
   ``Tools.ShippingSrm13Supply.RegsFit,
   ``Tools.ShippingSrm13Supply.NonRegBounded,
   ``Sparkle.IR.RegDedup.declWidth,
   ``Tools.ShippingDesignSV.weS,
   ``Tools.ShippingDesignSV.wofOf,
   ``Tools.SVParser.RoundtripProof.moduleWof,
   ``Tools.SVParser.EmitSem.weOf,
   ``Tools.ShippingEntrySoundness.weOf,
   ``Sparkle.IR.HierCheck.openIns,
   ``Sparkle.IR.HierCheck.openOuts,
   ``Sparkle.IR.HierCheck.openFlat,
   ``Sparkle.IR.HierCheck.drivesOf,
   ``Sparkle.IR.OptCheck.seqRegs,
   ``Tools.ShippingHierOpen.bodyInstOuts,
   ``Sparkle.IR.ZeroWidth.dropZeroWidthModule,
   ``Sparkle.IR.ZeroWidth.allConcrete,
   ``Sparkle.IR.RefineCheck.mergeChecked,
   ``Sparkle.IR.OptCheck.checkedOptimize,
   ``Tools.ShippingSeqOptSoundness.seedIn,
   ``Tools.ShippingTextTyped.TypedIn]

def one (s : String) : String := s.replace "\n" " "

def locOf (n : Name) : MetaM String := do
  let env ← getEnv
  let some mi := env.getModuleIdxFor? n | return "(local)"
  let mn := env.header.moduleNames[mi.toNat]!
  let rg ← findDeclarationRanges? n
  let ln := match rg with | some r => toString r.range.pos.line | none => "?"
  return s!"{mn}:{ln}"

def dumpThm (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  logInfo m!"S22LOC|{n}|{← locOf n}"
  forallTelescope ci.type fun xs concl => do
    let mut i : Nat := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let bi := match d.binderInfo with
        | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst" | .default => "explicit"
      logInfo m!"S22INV|{n}|{i}|{bi}|{d.userName}|{one ((← ppExpr d.type).pretty 100000)}"
      i := i + 1
    logInfo m!"S22CONCL|{n}|{one ((← ppExpr concl).pretty 100000)}"

def dumpDef (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  logInfo m!"S22LOC|{n}|{← locOf n}"
  match ci.value? with
  | none => logInfo m!"S22DEF|{n}|(no value: {ci.isInductive})"
  | some v =>
    lambdaTelescope v fun xs b => do
      logInfo m!"S22DEF|{n}|binders={xs.size}|{one ((← ppExpr b).pretty 100000)}"
      forallTelescope ci.type fun ys _ => do
        let mut i : Nat := 0
        for y in ys do
          let d ← y.fvarId!.getDecl
          logInfo m!"S22DEFB|{n}|{i}|{d.userName}|{one ((← ppExpr d.type).pretty 100000)}"
          i := i + 1

run_meta do
  for n in binderThms do dumpThm n
  for n in lemmaThms do dumpThm n
  for n in defs do dumpDef n

end Tests.Compiler.Srm22InventoryTest
end
