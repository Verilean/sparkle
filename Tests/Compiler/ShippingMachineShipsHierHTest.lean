import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingMachineInstTest
import Tools.ShippingMachineShipsHierHCommand
import Tools.ShippingHierSVRunH
import Tools.ShippingPremiseEval

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
    -- `linked_sv_of_runH` on the shipped module: its emitted Verilog
    let wof := Tools.SVParser.RoundtripProof.moduleWof o
    unless Tools.ShippingHierTyped.hierTyped C o do throwError "{n}: the shipped module is not width-typed"
    unless (bodyInstOuts C o.body).all (fun w =>
        ((Sparkle.IR.HierCheck.openIns o).map (·.name)).contains w &&
        decide (Sparkle.IR.RegDedup.declWidth o w ≤ Tools.SVParser.EmitSem.weOf wof w)) do
      throwError "{n}: a shipped instance-driven wire is not extracted or is wider than emitted"
    unless o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI do
      throwError "{n}: the shipped body leaves the instance/assign/register fragment"
    unless Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body do
      throwError "{n}: the emitted-Verilog check rejects the shipped module"
    unless (Tools.ShippingSeqSVSoundness.seqNames o.body).all (fun x =>
        Sparkle.IR.RegDedup.declWidth o x == Tools.SVParser.EmitSem.weOf wof x) do
      throwError "{n}: checker and emitter widths disagree"
    let acc := Sparkle.IR.RefineCheck.hierRefineCheck b
      (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
    Lean.logInfo m!"{n}: optimizer output {if acc then "accepted" else "rejected (unoptimized module shipped)"}"
  Lean.logInfo m!"SHIPS HIER H: {ds.length} machines with combinational children, to the shipped module; module and emitted-Verilog premises hold"

run_cmd do
  if (← get).messages.hasErrors then throwError "combinational-children shipping regression failed"
  for name in [``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_ships_hierH,
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD.machine_ships_hierH,
      ``Tools.ShippingMachineShipsHierH.machine_ships_hierH,
      ``Tools.ShippingHierOptRunH.hierRefineCheck_linkedH, ``Tools.ShippingHierOptRunH.fitX_of_runH,
      ``Tools.ShippingHierTyped.fitX_of_typed, ``Tools.ShippingHierSVRunH.linked_sv_of_runH,
      ``Tools.ShippingHierSVRunH.runModuleTG_of_H, ``Tools.ShippingHierTyped.runModuleH_typed] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"

/-! ## The shipping theorems' premises, evaluated (`Tools.ShippingPremiseEval`)

Every premise each generated theorem states is evaluated on the real compile
with the checker it names, its run boundaries traced; generation alone is not
counted. -/
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, items) in ([(``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL, evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL), (``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN, evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN), (``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller, evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller), (``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice, evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice), (``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested, evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested), (``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD, evalShipsHierH ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD)] : List (Lean.Name × Lean.Meta.MetaM Verdict)) do
    let v ← items
    unless v.applies && v.svTag == "SV:PARENT" do
      throwError "{n}: {v.tag}\n{v.report}"
  Lean.logInfo m!"COMB PARENTS: every module premise holds or is a traced boundary; the shipped module's emitted-Verilog premises hold"

end Sparkle.Tests.Compiler.ShippingMachineShipsHierHTest
