import Tools.ShippingFinalGoal
import Tools.ShippingMachineClosesGen
import Tools.ShippingMachineLinkedCommand

/-! # `#machine_goal_gap f n`: the gap of a generated endpoint, as a statement

For the generated SV endpoint of `f` at depth `n`
(`f.machine_design_svNR{n}_closed` if it exists, else
`f.machine_design_svNR{n}`), whose conclusion is the head's
(`Tools.ShippingFinalGoal.HeadConclusion`), the command adds

    f.machine_goal_gap{n} : ∀ (the endpoint's own binders),
      hShips → hDesign → hOuts → hBnd → hBd → RunGoal n Reset f d kD dom src ext extB b

by `Tools.ShippingFinalGoal.runGoal_of_head` — kernel-checked, nothing new
proved — and logs every hypothesis among the endpoint's own binders with
`ALLOWED` (the run, `MachineDefines`, `EntryDefines`, `ChildBnd`) or
`NOT ALLOWED` (anything else). The gap between today's endpoint and
`Tools.ShippingFinalGoal.MachineGoal` is: the five named hypotheses, and
every binder logged `NOT ALLOWED`. -/
namespace Tools.ShippingFinalGoalCommand
open Lean Meta Elab Command

/-- A hypothesis the final goal allows: the run, a reflection, the runtime
laws at the start world. -/
def allowed (t : Lean.Expr) : Bool :=
  t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo ||
  t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
  t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
  t.isAppOf ``Tools.ShippingChildInv.ChildBnd

/-- The gap theorem of endpoint `e`, and the classification of `e`'s
hypotheses. -/
def gapOf (e newName : Name) : MetaM (Array String) := do
  let info ← getConstInfo e
  let (value, report) ← forallTelescope info.type fun xs _ => do
    let h := mkAppN (mkConst e (info.levelParams.map mkLevelParam)) xs
    let v ← mkAppM ``Tools.ShippingFinalGoal.runGoal_of_head #[h]
    let v ← instantiateMVars v
    if v.hasMVar then throwError "{e}: the head's parameters were not all inferred"
    let mut report : Array String := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        let tag := if allowed t then "ALLOWED    " else "NOT ALLOWED"
        report := report.push s!"{tag}: {← ppExpr t}"
    return (← mkLambdaFVars xs v, report)
  Tools.ShippingMachineLinkedCommand.addTheorem newName (← inferType value) value
  return report

elab "#machine_goal_gap " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let open0 := f ++ Name.mkSimple s!"machine_design_svNR{n.getNat}"
  let closed := Tools.ShippingMachineClosesGen.closedName open0
  let e := if (← getEnv).contains closed then closed else open0
  let newName := f ++ Name.mkSimple s!"machine_goal_gap{n.getNat}"
  let report ← liftTermElabM (gapOf e newName)
  logInfo m!"GOALGAP {newName} from {e}\n{String.intercalate "\n" report.toList}\nNOT ALLOWED: hShips, hDesign, hOuts, hBnd, hBd (the five hypotheses of runGoal_of_head)"

end Tools.ShippingFinalGoalCommand
