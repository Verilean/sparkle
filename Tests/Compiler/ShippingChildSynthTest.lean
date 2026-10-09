import Tools.ShippingChildSynth
import Tools.ShippingGateChild
import Tools.ShippingMachineDepthRun

/-! The children of a machine-route compile are runs of the real entry
(`machine_children_real`), under the single `ChildSynthIs` boundary: the
statement's premises are the parent's run, its reflection facts and
`ChildSynthIs` — no per-child run boundary, no trace. -/
namespace Sparkle.Tests.Compiler.ShippingChildSynthTest

run_cmd Lean.Elab.Command.liftTermElabM do
  let ty ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingChildSynth.machine_children_real)
  for c in [``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingMachineEntry.MachineDefines,
      ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildSynth.ChildSynthIs,
      ``Tools.ShippingChildSynth.ChildrenReal, ``Tools.ShippingMachineEntry.CloseCalls] do
    unless (ty.find? (·.isConstOf c)).isSome do throwError "machine_children_real: {c} missing"
  -- no run boundary of a child among its premises
  for c in [``Tools.ShippingGateChild.MachineRun, ``Tools.ShippingGateChild.GateRun,
      ``Tools.ShippingMachineDepthRun.MachineRunN] do
    if (ty.find? (·.isConstOf c)).isSome then throwError "machine_children_real mentions {c}"
  Lean.logInfo m!"CHILD SYNTH: the children's runs derived from the parent's run under ChildSynthIs"

run_cmd do
  for name in [``Tools.ShippingChildSynth.machine_children_real,
      ``Tools.ShippingChildSynth.synthesizeMachineCertified_runs,
      ``Tools.ShippingChildSynth.closeInstsGM_runs, ``Tools.ShippingChildSynth.closeInstsM_runs,
      ``Tools.ShippingChildSynth.RunsTo_mapM_get] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"CHILD SYNTH AXIOMS: standard only"

end Sparkle.Tests.Compiler.ShippingChildSynthTest
