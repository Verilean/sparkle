import Tests.Compiler.ShippingMachineSeqTest
import Tools.ShippingMachineDepthCommand
import Tools.ShippingPremiseEval

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

set_option maxHeartbeats 0 in
#machine_ships_hierN Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 1

-- the shipped module's premises, on the real modules (depth 1: `mid`'s children too)
open Tools.ShippingHierOpen Tools.ShippingHierState in
run_cmd Lean.Elab.Command.liftTermElabM do
  let n := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
  let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
  let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let C := Tools.ShippingMachineLinked.childMap D.modules
  unless Sparkle.IR.RefineCheck.hierBinds b do throwError "the optimizer check does not bind"
  unless linkedWF C b.body && linkedWF C o.body do throwError "not linked-well-formed"
  unless (instNames b.body).Nodup && (instNames o.body).Nodup do throwError "instance names repeat"
  unless (bodyInstOuts C b.body).all (fun w =>
      ((Sparkle.IR.HierCheck.openIns b).map (·.name)).contains w) do
    throwError "an instance-driven wire is not an extracted input"
  unless instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body do throwError "instance-output widths"
  unless Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body do
    throwError "a child's outputs are not masked"
  Lean.logInfo m!"DEPTH SHIPS: grand's shipped-module premises hold"

open Lean in
run_cmd do
  for name in [``grand.machine_composedN1, ``mid.machine_composedN0, ``mid.seq_child_runN_of0,
      ``cnt.seq_child_runN, ``parent.machine_composedN0,
      ``Tools.ShippingMachineDepthRun.seqChildRunN_of_composed,
      ``Tools.ShippingMachineDepthRun.seqChildRunN_full,
      ``Tools.ShippingHierMono.KSn_mono_away,
      ``Tools.ShippingMachineDepthChild.calls_ports, ``grand.machine_ships_hierN1,
      ``Tools.ShippingMachineShipsDepth.KSn_boundedIn] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"DEPTH: a machine whose child has children, composed at depth 1, kernel-checked; standard axioms only"

/-! ## The shipping theorems' premises, evaluated (`Tools.ShippingPremiseEval`)

Every premise each generated theorem states is evaluated on the real compile
with the checker it names, its run boundaries traced; generation alone is not
counted. -/
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, items) in ([(``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand (some 1))] : List (Lean.Name × Lean.Meta.MetaM Verdict)) do
    let v ← items
    unless v.applies && v.svTag == "SV:PARENT" do
      throwError "{n}: {v.tag}\n{v.report}"
  Lean.logInfo m!"DEPTH 1 (grand): every module premise holds or is a traced boundary; the shipped module's emitted-Verilog premises hold"

end Sparkle.Tests.Compiler.ShippingMachineDepthTest
