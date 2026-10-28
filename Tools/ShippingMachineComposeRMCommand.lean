import Tools.ShippingMachineComposeRACommand
import Tools.ShippingMachineComposeRM
-- BUILT (unit SR2d, par/u-sr2d): rm1/rm4 exit 0; co-import co1 exit 0. No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR2d: `f.machine_composedRM` — `machine_composedRN` with the trace `h` DISCHARGED

`f.machine_composedRM` is `f.machine_composedRN` (SR2c) with its trace premise `h` replaced by
`Tools.ShippingMachineComposeRM.machine_traceL_of_data_extRM` applied to the data of `f.machine_sound`
(as `generateComposedR` does for the old head): the trace comes from the core run `hr`,
`MachineDefines`, `MachineClosesAtA` (a premise of the generated theorem) and the start world
`JQ O.quiet 0 w`. Premises of the generated theorem: `O`, `hA`, `T : RefLawsATele`, the run, `entry`,
`closes`, `hw`, one `EntryDefines` per distinct callee. Only the flat `machine_trace_of_data_ext`
head is handled (error otherwise). -/
namespace Tools.ShippingMachineComposeRMCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine)
open Tools.ShippingMachineLinkedCommand

def generateComposedRM (declName : Name) : MetaM Name := do
  let name := declName ++ `machine_composedRM
  if (← getEnv).contains name then return name
  let rn ← Tools.ShippingMachineComposeRACommand.generateComposedRN declName
  let soundHead := match (← getConstInfo (declName ++ `machine_sound)) with
    | .thmInfo t => t.value.getAppFn.constName?.getD .anonymous
    | _ => .anonymous
  unless soundHead == ``Tools.ShippingMachineAuto.machine_trace_of_data_ext do
    throwError "{declName}: only the flat data_ext head is handled, not {soundHead}"
  let args ← soundArgs declName soundHead
  let pM := mkAppN (mkConst ``Tools.ShippingMachineComposeRM.machine_traceL_of_data_extRM) args
  forallTelescope (← inferType pM) fun xs _ => do
    let h := mkAppN pM xs
    let find (n : Name) : MetaM Lean.Expr := do
      for x in xs do
        if (← whnfR (← inferType x)).isAppOf n then return x
      throwError "{declName}: no binder of type {n}"
    let findRef (st : Name) : MetaM Lean.Expr := do
      for x in xs do
        let t ← whnfR (← inferType x)
        if t.isAppOf ``ST.Ref && (t.getAppArgs.back?.map (·.isConstOf st)).getD false then return x
      throwError "{declName}: no reference to {st}"
    let O ← find ``Tools.ShippingChildInvA.RefLawsAOps
    let (ms, _, _) ← forallMetaBoundedTelescope (← inferType (mkConst rn)) 8
    unless ms.size == 8 do throwError "{rn}: binders"
    ms[0]!.mvarId!.assign (← find ``Lean.Meta.Context)
    ms[1]!.mvarId!.assign (← findRef ``Lean.Meta.State)
    ms[2]!.mvarId!.assign (← find ``Lean.Core.Context)
    ms[3]!.mvarId!.assign (← findRef ``Lean.Core.State)
    ms[6]!.mvarId!.assign O
    unless ← isDefEq (← inferType ms[7]!) (← inferType h) do
      throwError "{declName}: the trace's type does not match {rn}"
    ms[7]!.mvarId!.assign h
    let p ← instantiateMVars (mkAppN (mkConst rn) ms)
    if p.hasMVar then throwError "{declName}: unassigned arguments"
    forallTelescope (← inferType p) fun hRs concl => do
      let value ← mkLambdaFVars (xs ++ hRs) (mkAppN p hRs)
      let _ := concl
      addTheorem name (← inferType value) value
      return name

end Tools.ShippingMachineComposeRMCommand
