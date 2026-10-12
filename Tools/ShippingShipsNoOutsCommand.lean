import Tools.ShippingShipsNoOuts
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingMachineLinkedCommand

/-! # `#machine_no_outs f n using h`: the depth endpoint without the output check

`f.machine_ships_hierNR{n}` is `machine_ships_hierC` applied to the
generator's arguments. This command applies
`Tools.ShippingShipsNoOuts.machine_design_noOuts` to THE SAME arguments
(read off that theorem's proof term, as the existing composition does) and
discharges its hypothesis `hOuts` with the theorem `h` the user names, which
must have the explicit arguments

    h hcore hpost entry closes hb hBnd :
      outsCheck (childMap D.modules) n (checkedOptimize b) = true

(the core run, the post-processing fact, the declaration's reflection and
closing, `hierBinds b`, the endpoint's boundary). It adds

    f.machine_design_noOutsNR{n} : ∀ {contexts, run} hr entry closes,
      ∃ raw D, … ∧ (shipsHierCheck → designCheck → Bnd → Bd → …)

— the statement of `f.machine_design_svNR{n}` with the `outsCheck`
antecedent removed (checked here: the constant `outsCheck` does not occur in
the new statement) — and, when `f.machine_closes_at` exists, its `_closed`
form by the existing `closeEndpointAt`.

Nothing is assumed: the theorem is kernel-checked with standard axioms. -/
namespace Tools.ShippingShipsNoOutsCommand
open Lean Meta Elab Command

/-- `f.machine_design_noOutsNR{n}` from `f.machine_ships_hierNR{n}` and the
output-check theorem `outs`. -/
def generate (f : Name) (n : Nat) (outs : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noOutsNR{n}"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svNR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    -- n Reset Bnd C Bd Inv hBd hRI {declName} d {kD ι dom src ext extB lsrc srcL extL extBL}
    -- soundL composed houtTy, then the run's binders
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingShipsNoOuts.machine_design_noOuts args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    let .forallE _ T _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope T fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      -- zs: raw D w1 hcore hpost hb hBnd ; xs[9] = entry, xs[10] = closes
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!, zs[6]!]
      unless ← isDefEq (← inferType p) goal do
        throwError "{outs}: proves{indentExpr (← inferType p)}\nbut the head asks{indentExpr goal}"
      mkLambdaFVars zs p
    mkLambdaFVars xs (mkApp pre hOuts)
  let value ← instantiateMVars value
  let type ← inferType value
  if (type.find? (·.isConstOf ``Tools.ShippingDesignSVBack.outsCheck)).isSome then
    throwError "{name}: the statement still mentions outsCheck"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

elab "#machine_no_outs " d:ident n:num " using " h:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let outs ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo h
  let name ← liftTermElabM (generate f n.getNat outs)
  let mut made := #[name]
  let cl := f ++ `machine_closes_at
  if (← getEnv).contains cl then
    let nn := Tools.ShippingMachineClosesGen.closedName name
    if ← liftTermElabM (Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn) then
      made := made.push nn
  logInfo m!"NOOUTS {made}: the depth endpoint without the outsCheck antecedent (derived from the core run by {outs})"

end Tools.ShippingShipsNoOutsCommand
