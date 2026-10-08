import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.MultiInstanceTest
import Tools.ShippingMachineSeqCommand
import Tools.ShippingMachineShipsHierCommand

/-! Machines calling SEQUENTIAL `@[hardware_module]`s (`ShippingMachineSeqTest`),
composed with their children: `#machine_composedTS` proves that the stateful
linked run of the emitted module — each instance stepping its child's module
from reset — shows the source, given the run boundary (each instance's module
is a run of the full entry on its child). The child's own theorem at the full
entry is `c.seq_child_run`. -/
namespace Sparkle.Tests.Compiler.ShippingMachineSeqLinkedTest
open Lean Elab Command
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
#machine_composedTS parent
set_option maxHeartbeats 0 in
#machine_composedTS chained

-- domain-generic parents: one call, two identical calls (one instance), a 2×2 mesh
set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.MultiInstance.pe
set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.MultiInstance.engineOnce
set_option maxHeartbeats 0 in
#machine_composedTS Sparkle.Tests.Compiler.MultiInstance.engineOnce
set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.MultiInstance.twinCalls
set_option maxHeartbeats 0 in
#machine_composedTS Sparkle.Tests.Compiler.MultiInstance.twinCalls
set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.MultiInstance.mesh2x2
set_option maxHeartbeats 0 in
#machine_composedTS Sparkle.Tests.Compiler.MultiInstance.mesh2x2

/-! ## To the shipped module (`#machine_ships_hier`)

The composed theorems carried through the full entry and the optimizer
(checked on the extracted interface, `hierRefineCheck_linked`): the shipped
module's stateful linked run shows the source. Its premises that are facts
about the run's modules are evaluated here on the real modules. -/

#machine_ships_hier parent
#machine_ships_hier chained
#machine_ships_hier Sparkle.Tests.Compiler.MultiInstance.engineOnce
#machine_ships_hier Sparkle.Tests.Compiler.MultiInstance.twinCalls
#machine_ships_hier Sparkle.Tests.Compiler.MultiInstance.mesh2x2

open Tools.ShippingHierOpen Tools.ShippingHierState in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ds := [``parent, ``chained, ``Sparkle.Tests.Compiler.MultiInstance.engineOnce,
    ``Sparkle.Tests.Compiler.MultiInstance.twinCalls, ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2]
  for n in ds do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Sparkle.IR.RefineCheck.hierBinds b do throwError "{n}: the optimizer check does not bind"
    unless linkedWF C b.body && linkedWF C o.body do throwError "{n}: not linked-well-formed"
    unless (instNames b.body).Nodup && (instNames o.body).Nodup do throwError "{n}: instance names repeat"
    unless (bodyInstOuts C b.body).all (fun w =>
        ((Sparkle.IR.HierCheck.openIns b).map (·.name)).contains w) do
      throwError "{n}: an instance-driven wire is not an extracted input"
    unless instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body do
      throwError "{n}: instance-output widths"
    unless (b.inputs.map (·.name)).contains "rst" do throwError "{n}: no reset port"
    let selfRead := o.body.any fun st => match st with
      | .inst mn _ conns => match C mn with
        | some (child, _) => (inConns child.outputs conns).any fun c => match c.2 with
          | .ref w => (instOutWires child.outputs conns).contains w
          | _ => false
        | none => true
      | _ => false
    if selfRead then throwError "{n}: an instance reads its own output"
  Lean.logInfo m!"SHIPS HIER: {ds.length} machines with sequential children, to the shipped module; module premises hold"

run_cmd do
  if (← get).messages.hasErrors then throwError "sequential composition regression failed"
  for name in [``parent.machine_composedT, ``chained.machine_composedT, ``cnt.seq_child_run,
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_composedT,
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_composedT,
      ``Tools.ShippingMachineCallsLinkedT.machine_linkedT_calls,
      ``Tools.ShippingMachineSeqInst.seqChildRun_full,
      ``parent.machine_ships_hier, ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ships_hier,
      ``Tools.ShippingMachineShipsHier.machine_ships_hier] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"SEQUENTIAL COMPOSITION: machines calling sequential children, composed with their children's modules stepping from reset, kernel-checked"

end Sparkle.Tests.Compiler.ShippingMachineSeqLinkedTest
