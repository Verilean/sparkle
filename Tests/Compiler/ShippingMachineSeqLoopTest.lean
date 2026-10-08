import Sparkle
import Tests.Compiler.ShippingMachineFuseTest
import Tools.ShippingMachineSeqCommand
import Tools.ShippingMachineShipsHierCommand

/-! Sequential children and parents beyond `machine_trace_of_data`.

A `Signal.loop` child (the issue-107 toggle's shape): its endpoint goes
through `machine_trace_of_loop`, whose wired twin (`machine_traceL_of_loop`)
has the conclusion `seqChildRun_full` takes, so `c.seq_child_run`, the
composition and the shipped module follow as for a `circuit do` child. A
TRANSPORTED parent (`withMemory`: its endpoint proved on the fused source and
rewritten to the declaration's): the composed theorem is already transported,
and the cleanup facts come from the wired twin of the untransported head. -/
namespace Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest
open Lean Elab Command
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- A 1-bit register that flips when `en` is high, as a `Signal.loop`. -/
@[hardware_module]
def toggleL {dom : DomainConfig} (en : Signal dom Bool) : Signal dom Bool :=
  Signal.loop fun (s : Signal dom Bool) =>
    Signal.register false (Signal.mux en (~~~s) s)

/-- A machine latching the toggle's value. -/
def loopParent (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  circuit do
    let r0 ← Signal.reg false
    let t := toggleL en
    r0 <~ t
    return (r0 : Signal defaultDomain Bool)

set_option maxHeartbeats 0 in
#machine_endpoint toggleL
set_option maxHeartbeats 0 in
#machine_endpoint loopParent
set_option maxHeartbeats 0 in
#machine_composedTS loopParent
#machine_ships_hier loopParent

set_option maxHeartbeats 0 in
#machine_composedTS Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
#machine_ships_hier Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory

open Tools.ShippingHierOpen Tools.ShippingHierState in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``loopParent, ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory] do
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
    unless Tools.ShippingMachineShipsHier.kidsMasked C b.body ||
        Tools.ShippingMachineShipsHier.kidsMem C b.body do
      throwError "{n}: the children's output bound"
  Lean.logInfo m!"SEQ LOOP / TRANSPORTED: shipped, module premises hold"

run_cmd do
  if (← get).messages.hasErrors then throwError "loop-child / transported shipping regression failed"
  for name in [``loopParent.machine_composedT, ``loopParent.machine_ships_hier, ``toggleL.seq_child_run,
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_ships_hier] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"

end Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest
