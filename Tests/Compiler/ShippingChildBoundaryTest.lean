import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tests.Compiler.ShippingDesignSVTest
import Tools.ShippingMachineSeqCommandR

/-! The child-run boundary DERIVED on real compiles (`#machine_design_svR0`).

The source → closed-emitted-texts endpoint whose run boundary is the session
boundary `ChildSynthIs` and the children's reflection facts, in the run's own
contexts — no premise about the parent's instances (`BoundaryOf` /
`InstOfCall`). Positive cases: one sequential child (`parent`), the same child
called twice (`chained`), two DIFFERENT sequential children (`two`) and a
sequential child next to a memory read (`seqMem`): for the last two the old
premise `BoundaryOf` is false (each child's premise would need the other
instance to be its run), which the evaluator reports as MISMATCH. -/
namespace Sparkle.Tests.Compiler.ShippingChildBoundaryTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

structure AccOut (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (AccOut dom) dom := ⟨⟩

/-- An accumulator: a second, different sequential child. -/
@[hardware_module] def acc {dom : DomainConfig} (x : Signal dom (BitVec 8)) : AccOut dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 1#8 : Signal dom (BitVec 8)) } : AccOut dom)

/-- Two different sequential children. -/
def two (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let a := acc rs
    r <~ Signal.mux k.hit (a.s + k.n) rs
    return rs

/-- A sequential child next to a memory read. -/
def seqMem (en : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let rd := Signal.memoryComboRead wa wd en wa
    r <~ Signal.mux k.hit (rd + k.n) rs
    return rs

#machine_endpoint two
#machine_endpoint seqMem

set_option maxHeartbeats 0 in
#machine_design_svR0 Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent
set_option maxHeartbeats 0 in
#machine_design_svR0 Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained
set_option maxHeartbeats 0 in
#machine_design_svR0 two
set_option maxHeartbeats 0 in
#machine_design_svR0 seqMem

-- the old route, for comparison: its boundary premise `BoundaryOf` as stated
set_option maxHeartbeats 0 in
#machine_composedTS two
set_option maxHeartbeats 0 in
#machine_ships_hier two
set_option maxHeartbeats 0 in
#machine_composedTS seqMem
set_option maxHeartbeats 0 in
#machine_ships_hier seqMem

def rEndpoints : List Lean.Name :=
  [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_svR0,
   ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_svR0,
   ``two.machine_design_svR0, ``seqMem.machine_design_svR0]

/-- `c` occurs in `e` (a constant, also inside the bodies of local definitions it unfolds to). -/
def mentions (e : Lean.Expr) (c : Lean.Name) : Bool := (e.find? (·.isConstOf c)).isSome

-- the derived boundary: the endpoint states `ChildSynthIs` and the children's
-- reflection in the run's contexts, and NO premise about the parent's
-- instances; existence and all closed runs, `outsCheck` explicit
run_cmd Lean.Elab.Command.liftTermElabM do
  for e in rEndpoints do
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildSynth.ChildSynthIs, ``Tools.ShippingMachineEntry.MachineDefines,
        ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingDesignSVBack.outsCheck,
        ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSV.DesignSV] do
      unless mentions ty c do throwError "{e}: {c} missing"
    for c in [``Tools.ShippingMachineSeqCommand.BoundaryOf, ``Tools.ShippingMachineCallsLinkedT.InstOfCall,
        ``Tools.ShippingGateChild.MachineRun, ``Tools.ShippingGateChild.GateRun,
        ``Tools.ShippingMachineDepthRun.MachineRunN] do
      if mentions ty c then throwError "{e}: still mentions {c}"
    -- and its proof is built from the derived composition, not the old one
    let some (.thmInfo ti) := (← Lean.getEnv).find? e | throwError "{e}"
    let ships := (ti.value.find? fun x => x.isConstOf (e.getPrefix ++ `machine_ships_hierR)).isSome
    unless ships do throwError "{e}: not built from machine_ships_hierR"
  Lean.logInfo m!"DERIVED BOUNDARY: {rEndpoints.length} endpoints state ChildSynthIs + the children's reflection, no BoundaryOf / InstOfCall / MachineRun premise"

-- the shipped designs pass the decidable premises the endpoints state
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained, ``two, ``seqMem] do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Tools.ShippingHierPremisesBase.shipsHierCheck C b do throwError "{n}: shipsHierCheck"
    unless Tools.ShippingDesignSV.designCheck C 0 o do throwError "{n}: designCheck 0"
    unless Tools.ShippingDesignSVBack.outsCheck C 0 o do throwError "{n}: outsCheck 0"
    unless Tools.ShippingMachineShipsHier.kidsMixed C b.body do throwError "{n}: kidsMixed"
  Lean.logInfo m!"DERIVED BOUNDARY: shipsHierCheck, designCheck 0, outsCheck 0, kidsMixed hold on the four shipped designs"

-- negative: the OLD premise pairs every instance with every sequential
-- child; with two different children, or a child next to a memory, that
-- pairing is false (MISMATCH, not applying); with one child it matches
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``two, ``seqMem] do
    let v ← evalShipsHierSeq n none
    unless v.traceTag == "TRACE:MISMATCH" && !v.applies do throwError "{n}: {v.tag}\n{v.report}"
  let vp ← evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent none
  unless vp.traceTag == "TRACE:MATCHED" do throwError "parent: {vp.tag}"
  Lean.logInfo m!"OLD BOUNDARY: false for two / seqMem (MISMATCH), matched for one child"

run_cmd do
  for name in rEndpoints ++ [``two.machine_ships_hierR, ``seqMem.machine_ships_hierR,
      ``two.machine_composedTR, ``seqMem.machine_composedTR] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"DERIVED BOUNDARY AXIOMS: standard only"

end Sparkle.Tests.Compiler.ShippingChildBoundaryTest
