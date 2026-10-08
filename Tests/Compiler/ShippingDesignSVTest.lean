import Tests.Compiler.ShippingMachineDepthHTest
import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tests.Compiler.ShippingMachineMemLinkedTest
import Tests.Compiler.ShippingMachineShipsHierHTest
import Tools.ShippingDesignSV
import Tools.ShippingPremiseEval
import Tools.ShippingShipsDesignSVCommand

/-! The closed emitted-Verilog run of a design (`design_sv_runN`).

The general theorem turns an IR linked run at depth `n` into a closed run of
the emitted texts — the children's texts supplying every instance-output
wire — under the decidable `designCheck` and the run-level width premises
`SVBounds`. Here `designCheck` is evaluated on real shipped designs:
`grandH → midH → rcH` (depth 1), a depth-2 chain `topD2 → mid2 → midH → rcH`,
and a parent with two DIFFERENT sequential children (`midH`, `cnt`). An
insufficient depth is rejected (a depth-0 leaf must be flat). -/
namespace Sparkle.Tests.Compiler.ShippingDesignSVTest
open Lean
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest (CntOut cnt)
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest (midH)

/-- A sequential child whose own child is `midH` (depth 2 below its parent). -/
@[hardware_module]
def mid2 {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := midH en
    r <~ Signal.mux k.hit (rs + k.n) rs
    return ({ n := rs, hit := k.hit } : CntOut dom)

def topD2 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := mid2 en
    r <~ Signal.mux m.hit (rs + m.n) rs
    return rs

/-- Two different sequential children at depth 1. -/
def mixD1 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := midH en
    let b := cnt en
    r <~ Signal.mux a.hit (rs + b.n) rs
    return rs

set_option maxHeartbeats 0 in
#machine_endpoint mid2
set_option maxHeartbeats 0 in
#machine_endpoint topD2
set_option maxHeartbeats 0 in
#machine_composedN topD2 2
set_option maxHeartbeats 0 in
#machine_ships_hierN topD2 2
set_option maxHeartbeats 0 in
#machine_endpoint mixD1
set_option maxHeartbeats 0 in
#machine_composedN mixD1 1
set_option maxHeartbeats 0 in
#machine_ships_hierN mixD1 1

/-! ## Source → the closed emitted texts, kernel-checked

`ships_design_svN` applied to the generated shipping theorems: for every run
of the compiler, every input sequence and every length, the shipped
design's emitted texts run closed (`DesignSV`) to environments showing the
source — under the theorem's stated premises (the module checker, the
run boundary, `designCheck`, the use conditions). -/
set_option maxHeartbeats 0 in
#machine_design_svN Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH 1
set_option maxHeartbeats 0 in
#machine_design_svN topD2 2

/-! The depth-0 route (`machine_ships_hier`: `KS = flatKS = KSn _ 0`, the
theorem's own reset / boundary / bound) and the combinational route
(`machine_ships_hierH` through `runModuleTG_flat_of_H`). A memory parent's
endpoint is generated too, but its premise `designCheck` is false on the real
module (memory leaves: `leafCheck` takes no memory statement), so it is not
counted as reaching the texts. -/
set_option maxHeartbeats 0 in
#machine_design_sv0 Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent
set_option maxHeartbeats 0 in
#machine_design_sv0 Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
set_option maxHeartbeats 0 in
#machine_design_svH Sparkle.Tests.Compiler.ShippingMachineInstTest.caller

open Tools.ShippingDesignSV in
run_cmd Lean.Elab.Command.liftTermElabM do
  let shipped (n : Lean.Name) : Lean.Meta.MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    return (Sparkle.IR.OptCheck.checkedOptimize b, D)
  for (n, dep) in [(``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 1), (``topD2, 2), (``mixD1, 1)] do
    let (o, D) ← shipped n
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless designCheck C dep o do throwError "{n}: designCheck {dep} rejects the shipped design"
    -- one level too shallow: a depth-0 leaf would have instances — rejected
    if designCheck C (dep - 1) o then throwError "{n}: designCheck {dep - 1} accepted an insufficient depth"
  Lean.logInfo m!"DESIGN SV: designCheck holds at the design's depth (grandH 1, topD2 2, mixD1 1) and is rejected one level shallower"

open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, v) in ([(``topD2, evalShipsHierSeq ``topD2 (some 2)), (``mixD1, evalShipsHierSeq ``mixD1 (some 1))] :
      List (Lean.Name × Lean.Meta.MetaM Verdict)) do
    let v ← v
    Lean.logInfo m!"{v.report}"
    unless v.moduleTag == "MOD:PREM" do throwError "{n}: {v.tag}"
  -- topD2: the source → DesignSV endpoint exists (SOURCE); mixD1: none generated (CHECKED only)
  let vt ← evalShipsHierSeq ``topD2 (some 2)
  unless vt.svChildTag == "SVCHILD:SOURCE" do throwError "topD2: {vt.tag}"
  let vg ← evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH (some 1)
  unless vg.svChildTag == "SVCHILD:SOURCE" do throwError "grandH: {vg.tag}"
  let vp ← evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent none
  unless vp.applies && vp.svChildTag == "SVCHILD:SOURCE" do throwError "parent: {vp.tag}"
  let vc ← evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  unless vc.applies && vc.svChildTag == "SVCHILD:SOURCE" do throwError "caller: {vc.tag}"
  let vmem ← evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter none
  Lean.logInfo m!"{vmem.report}"
  unless vmem.applies && vmem.svChildTag == "SVCHILD:OPEN" do throwError "memCounter: {vmem.tag}"
  let vx ← evalShipsHierSeq ``mixD1 (some 1)
  unless vx.svChildTag == "SVCHILD:CHECKED" do throwError "mixD1: {vx.tag}"
  -- two different sequential children: the instance correspondence is not reconstructed
  let vm ← evalShipsHierSeq ``mixD1 (some 1)
  unless vm.traceTag == "TRACE:UNTRACED" && !vm.applies do throwError "mixD1: {vm.tag}"

run_cmd do
  for name in [``Tools.ShippingDesignSV.design_sv_runN,
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svN1, ``topD2.machine_design_svN2,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_sv0,
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH, ``Tools.ShippingShipsDesignSV.ships_design_svH,
      ``Tools.ShippingShipsDesignSV.ships_design_svN, ``Tools.ShippingDesignSVBounds.svBounds_of_checks,
      ``Tools.ShippingDesignSVBounds.KSn_stepBound, ``Tools.ShippingDesignSVBounds.runModuleTG_envBound, ``Tools.ShippingDesignSV.child_runKS_of_linked,
      ``Tools.ShippingDesignSV.portsMatchB_sound, ``topD2.machine_ships_hierN2, ``mixD1.machine_ships_hierN1,
      ``Tools.ShippingHierShipsSV.shipped_sv_checked, ``Tools.ShippingHierShipsSV.linked_sv_of_runH_checked] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"AXIOMS: standard only"

end Sparkle.Tests.Compiler.ShippingDesignSVTest
