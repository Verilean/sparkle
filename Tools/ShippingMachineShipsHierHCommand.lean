import Tools.ShippingMachineShipsHierH
import Tools.ShippingGateChildCommand

/-! # `#machine_ships_hierH f`

For a machine with combinational children whose composed theorem
`f.machine_composed` is generated (`#machine_composed`), the theorem
`f.machine_ships_hierH`: `machine_ships_hierH` with `f`'s wired endpoint
(the linked twin `f.machine_linked` is built on) for the cleanup facts and
its composed theorem, the calls' premise `R` read off by unification. -/
namespace Tools.ShippingMachineShipsHierHCommand
open Lean Meta Elab
open Tools.ShippingMachineLinkedCommand (soundArgs addTheorem)

def generate (declName : Name) : MetaM Name := do
  if (← getEnv).contains (declName ++ `machine_ships_hierH) then return declName ++ `machine_ships_hierH
  let cName := declName ++ `machine_composed
  unless (← getEnv).contains cName do
    throwError "{declName}: run #machine_composed {declName} first"
  let r ← Tools.ShippingMachineCommand.readMachine declName
  -- the endpoint's wired twin, as `#machine_linked` takes it
  let soundHead := match (← getConstInfo (declName ++ `machine_sound)) with
    | .thmInfo t => t.value.getAppFn.constName?.getD .anonymous
    | _ => .anonymous
  let (head, headL) :=
    if soundHead == ``Tools.ShippingMachineTeleNest.machine_trace_of_tele_ext then
      (``Tools.ShippingMachineTeleNest.machine_trace_of_tele_ext,
        ``Tools.ShippingMachineTeleNest.machine_traceL_of_tele_ext)
    else if r.nested then
      (``Tools.ShippingMachineNest.machine_trace_of_nested_ext,
        ``Tools.ShippingMachineNest.machine_traceL_of_nested_ext)
    else (``Tools.ShippingMachineAuto.machine_trace_of_data_ext,
      ``Tools.ShippingMachineAuto.machine_traceL_of_data_ext)
  let args ← soundArgs declName head
  let soundL := mkAppN (mkConst headL) args
  let data := mkConst (declName ++ `machineData)
  let thm ← mkAppOptM ``Tools.ShippingMachineShipsHierH.machine_ships_hierH
    #[none, none, data, none, none, none, none, none, none, none, none,
      soundL, mkConst cName]
  let thm ← instantiateMVars thm
  let ty ← inferType thm
  let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
  let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
  if thm.hasMVar then throwError "{declName}: unassigned arguments"
  let name := declName ++ `machine_ships_hierH
  addTheorem name (← inferType thm) thm
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return name

elab "#machine_ships_hierH " d:ident : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) (generate declName)
  logInfo m!"{name}: the shipped (optimized) module's linked run shows the source, checked by the kernel"

end Tools.ShippingMachineShipsHierHCommand
