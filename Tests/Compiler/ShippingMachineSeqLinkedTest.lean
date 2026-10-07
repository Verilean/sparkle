import Tests.Compiler.ShippingMachineSeqTest
import Tools.ShippingMachineSeqCommand

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

run_cmd do
  if (← get).messages.hasErrors then throwError "sequential composition regression failed"
  for name in [``parent.machine_composedT, ``chained.machine_composedT, ``cnt.seq_child_run,
      ``Tools.ShippingMachineCallsLinkedT.machine_linkedT_calls,
      ``Tools.ShippingMachineSeqInst.seqChildRun_full] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"SEQUENTIAL COMPOSITION: machines calling sequential children, composed with their children's modules stepping from reset, kernel-checked"

end Sparkle.Tests.Compiler.ShippingMachineSeqLinkedTest
