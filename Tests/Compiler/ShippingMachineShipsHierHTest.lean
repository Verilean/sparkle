import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingMachineInstTest
import Tools.ShippingMachineShipsHierHCommand

/-! Machines calling COMBINATIONAL `@[hardware_module]`s, to the shipped
module (`#machine_ships_hierH`): the composed theorems (`#machine_composed`)
carried through the full entry and the optimizer (checked on the extracted
interface, `hierRefineCheck_linkedH`), so the shipped module's combinational
linked run shows the source. The premises that are facts about the run's
modules are evaluated here on the real modules. -/
namespace Sparkle.Tests.Compiler.ShippingMachineShipsHierHTest
open Lean Elab Command

open Sparkle.Tests.Compiler.ShippingMachineLinkedTest in
#machine_ships_hierH callerL
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest in
#machine_ships_hierH callerLN
open Sparkle.Tests.Compiler.ShippingMachineInstTest in
#machine_ships_hierH caller
open Sparkle.Tests.Compiler.ShippingMachineInstTest in
#machine_ships_hierH callerTwice
open Sparkle.Tests.Compiler.ShippingMachineInstTest in
#machine_ships_hierH callerNested
open Sparkle.Tests.Compiler.ShippingMachineInstTest in
#machine_ships_hierH callerD

open Tools.ShippingHierOpen Tools.ShippingHierState in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ds := [`Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL, `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN,
    `Sparkle.Tests.Compiler.ShippingMachineInstTest.caller, `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
    `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested, `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD]
  for n in ds do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Sparkle.IR.RefineCheck.hierBinds b do throwError "{n}: the optimizer check does not bind"
    unless linkedWF C b.body && linkedWF C o.body do throwError "{n}: not linked-well-formed"
    unless (instNames b.body).Nodup && (instNames o.body).Nodup do throwError "{n}: instance names repeat"
    unless Tools.ShippingHierOptRunH.kidsLocal D.modules o.body do
      throwError "{n}: a child does not compute from its input ports"
    unless (bodyInstOuts C b.body).all (fun w =>
        ((Sparkle.IR.HierCheck.openIns b).map (·.name)).contains w) do
      throwError "{n}: an instance-driven wire is not an extracted input"
    unless (b.inputs.map (·.name)).contains "rst" do throwError "{n}: no reset port"
    unless Tools.ShippingHierTyped.hierTyped C b do
      throwError "{n}: the linked body is not width-typed (the output bound)"
    let selfRead := o.body.any fun st => match st with
      | .inst mn _ conns => match C mn with
        | some (child, _) => (inConns child.outputs conns).any fun c => match c.2 with
          | .ref w => (instOutWires child.outputs conns).contains w
          | _ => false
        | none => true
      | _ => false
    if selfRead then throwError "{n}: an instance reads its own output"
    let acc := Sparkle.IR.RefineCheck.hierRefineCheck b
      (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
    Lean.logInfo m!"{n}: optimizer output {if acc then "accepted" else "rejected (unoptimized module shipped)"}"
  Lean.logInfo m!"SHIPS HIER H: {ds.length} machines with combinational children, to the shipped module; module premises hold"

run_cmd do
  if (← get).messages.hasErrors then throwError "combinational-children shipping regression failed"
  for name in [``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_ships_hierH,
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD.machine_ships_hierH,
      ``Tools.ShippingMachineShipsHierH.machine_ships_hierH,
      ``Tools.ShippingHierOptRunH.hierRefineCheck_linkedH, ``Tools.ShippingHierOptRunH.fitX_of_runH,
      ``Tools.ShippingHierTyped.fitX_of_typed, ``Tools.ShippingHierTyped.runModuleH_typed] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"

end Sparkle.Tests.Compiler.ShippingMachineShipsHierHTest
