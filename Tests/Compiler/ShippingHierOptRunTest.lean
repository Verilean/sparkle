import Tools.ShippingHierOptRun
import Tests.Compiler.MultiInstanceTest
import Tests.Compiler.Issue107LetBoundInstanceDup

/-! # The optimizer on instance-bearing modules, over the stateful run

`checkedOptimize` keeps the optimizer's output of an instance-bearing module
only if `hierRefineCheck` accepts it (connections named again by
`deinline`). `Tools.ShippingHierOptRun.hierRefineCheck_linked` carries every
stateful linked run of the module to one of the shipped module with the same
outputs. Here, on real instance-bearing modules of the full entry: the check
accepted the optimizer's output (the shipped module IS the checked one), and
the design premises of the theorem hold (linked-well-formed bodies, distinct
instance names, no instance reading its own output, the instance-driven
wires among the extracted inputs). -/
namespace Sparkle.Tests.Compiler.ShippingHierOptRunTest
open Sparkle.Compiler.Elab
open Sparkle.IR.HierCheck
open Tools.ShippingHierOpen Tools.ShippingHierState

run_cmd Lean.Elab.Command.liftTermElabM do
  let ds := [``Sparkle.Tests.Compiler.MultiInstance.mesh2x2,
    ``Sparkle.Tests.Compiler.MultiInstance.engineOnce,
    ``Sparkle.Tests.Compiler.MultiInstance.twinCalls,
    ``Sparkle.Tests.Compiler.Issue107LetBoundInstanceDup.threeInstances]
  for n in ds do
    let (b, design) ← synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let children : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv) :=
      fun mn => (Sparkle.IR.Machine.moduleByName design.modules mn).map
        fun c => (c, Sparkle.IR.RegDedup.declWidth c)
    unless Sparkle.IR.RefineCheck.hierBinds b do throwError "{n}: the check does not bind"
    unless Sparkle.IR.RefineCheck.hierRefineCheck b o do
      throwError "{n}: the shipped module is not the checked optimizer output"
    unless o.body != b.body do throwError "{n}: the optimizer changed nothing"
    unless linkedWF children b.body && linkedWF children o.body do
      throwError "{n}: a body is not linked-well-formed"
    unless (instNames b.body).Nodup && (instNames o.body).Nodup do
      throwError "{n}: instance names repeat"
    unless (bodyInstOuts children b.body).all (fun w => ((openIns b).map (·.name)).contains w) do
      throwError "{n}: an instance-driven wire is not an extracted input"
    let selfRead := o.body.any fun st => match st with
      | .inst mn _ conns => match children mn with
        | some (child, _) => (inConns child.outputs conns).any fun c => match c.2 with
          | .ref w => (instOutWires child.outputs conns).contains w
          | _ => false
        | none => true
      | _ => false
    if selfRead then throwError "{n}: an instance reads its own output"
  Lean.logInfo m!"HIER OPT RUN: {ds.length} instance-bearing modules, optimizer output checked and shipped, design premises hold"

run_cmd do
  for name in [``Tools.ShippingHierOptRun.hierRefineCheck_linked,
      ``Tools.ShippingHierOptRun.open_linked_run, ``Tools.ShippingHierOptRun.linked_open_run,
      ``Tools.ShippingHierOptLinked.linked_openKG,
      ``Tools.ShippingHierOptLinked.linked_consistentKG] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"HIER OPT RUN: standard axioms only"

end Sparkle.Tests.Compiler.ShippingHierOptRunTest
