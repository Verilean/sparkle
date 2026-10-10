import Tools.ShippingChildRun
import Tools.ShippingMachineSeqCommand
import Tools.ShippingGateChild
import Tools.ShippingMachineDepthRun
import Tools.ShippingMachineCallsLinkedTR

/-! The children of a machine-route compile are `RealChild`s
(`machine_children_real`), under the child boundary of the run's START world
(`ChildBnd`): the statement's premises are the parent's run, its reflection
facts and `ChildBnd` at that run's start — no per-child run boundary, no
trace. -/
namespace Sparkle.Tests.Compiler.ShippingChildSynthTest

run_cmd Lean.Elab.Command.liftTermElabM do
  let ty ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingChildInv.machine_children_real)
  for c in [``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingMachineEntry.MachineDefines,
      ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildInv.ChildBnd,
      ``Tools.ShippingChildInv.ChildrenReal, ``Tools.ShippingMachineEntry.CloseCalls] do
    unless (ty.find? (·.isConstOf c)).isSome do throwError "machine_children_real: {c} missing"
  -- no run boundary of a child among its premises
  for c in [``Tools.ShippingGateChild.MachineRun, ``Tools.ShippingGateChild.GateRun,
      ``Tools.ShippingMachineDepthRun.MachineRunN] do
    if (ty.find? (·.isConstOf c)).isSome then throwError "machine_children_real mentions {c}"
  Lean.logInfo m!"CHILD SYNTH: the children's runs derived from the parent's run under ChildBnd at its start world"

run_cmd do
  for name in [``Tools.ShippingChildInv.machine_children_real,
      ``Tools.ShippingChildInv.synthesizeMachineCertified_runs,
      ``Tools.ShippingChildInv.closeInstsGM_inv, ``Tools.ShippingChildInv.closeInstsM_inv,
      ``Tools.ShippingChildInv.mapM_hoare] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"CHILD SYNTH AXIOMS: standard only"

-- the instance level: the composed theorem's per-call premise is the child's
-- own theorem for runs of its entry and the child's reflection facts; the
-- served instance's being such a run is DERIVED (`ServedReal`, from
-- `ChildBnd`, through the endpoint's layers with the run's ids)
run_cmd Lean.Elab.Command.liftTermElabM do
  let ty ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingMachineCallsLinkedTR.machine_linkedT_callsR)
  for c in [``Tools.ShippingMachineTraceX.ServedReal, ``Tools.ShippingMachineCallsLinkedTR.SeqFactsR,
      ``Tools.ShippingMachineEntry.MachineDefines] do
    unless (ty.find? (·.isConstOf c)).isSome do throwError "machine_linkedT_callsR: {c} missing"
  for c in [``Tools.ShippingMachineCallsLinkedT.InstOfCall, ``Tools.ShippingMachineCallsLinkedT.SeqFacts,
      ``Tools.ShippingMachineSeqCommand.BoundaryOf] do
    if (ty.find? (·.isConstOf c)).isSome then throwError "machine_linkedT_callsR mentions {c}"
  let ty2 ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBR)
  unless (ty2.find? (·.isConstOf ``Tools.ShippingChildInv.ChildBnd)).isSome do
    throwError "machine_trace_lets_of_streamBR: no ChildBnd premise"
  Lean.logInfo m!"CHILD SERVED: the call-to-instance binding derived from the run (ServedReal)"

run_cmd do
  for name in [``Tools.ShippingChildServe.closeInstsG_serves,
      ``Tools.ShippingMachineEntry.synthesizeMachineCertified_soundX,
      ``Tools.ShippingMachineEntry.synthesizeMachineCertified_sound,
      ``Tools.ShippingMachineTraceX.synthesizeCombinationalCore_machine_soundR,
      ``Tools.ShippingMachineTraceX.machine_trace_lets_of_streamBR,
      ``Tools.ShippingMachineTraceX.machine_endpointX,
      ``Tools.ShippingMachineLinkedT.machine_linkedT_of, ``Tools.ShippingMachineLinkedT.machine_linkedT,
      ``Tools.ShippingMachineCallsLinkedTR.calls_hchildR,
      ``Tools.ShippingMachineCallsLinkedTR.machine_linkedT_callsR] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"CHILD SERVED AXIOMS: standard only"

end Sparkle.Tests.Compiler.ShippingChildSynthTest
