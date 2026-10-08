import Tests.Compiler.ShippingMachineSeqTest
import Tools.ShippingMachineDepthCommand

/-! Machines whose sequential children have children of their own
(`ShippingMachineSeqTest.grand` → `mid` → `cnt`), composed at depth:
`#machine_composedN f n` proves that the stateful linked run of `f`'s module,
its children stepping at depth `n`, shows the source. `mid`'s own composed
theorem (depth 0) gives `mid`'s run at depth 1 (`seqChildRunN_of_composed`,
under the hierarchical run boundary `MachineRunN`), which `grand`'s theorem
consumes. -/
namespace Sparkle.Tests.Compiler.ShippingMachineDepthTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
#machine_composedN Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 0
set_option maxHeartbeats 0 in
#machine_composedN Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 1

open Lean in
run_cmd do
  for name in [``grand.machine_composedN1, ``mid.machine_composedN0, ``mid.seq_child_runN_of0,
      ``cnt.seq_child_runN, ``parent.machine_composedN0,
      ``Tools.ShippingMachineDepthRun.seqChildRunN_of_composed,
      ``Tools.ShippingMachineDepthRun.seqChildRunN_full,
      ``Tools.ShippingHierMono.KSn_mono_away,
      ``Tools.ShippingMachineDepthChild.calls_ports] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"DEPTH: a machine whose child has children, composed at depth 1, kernel-checked; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMachineDepthTest
