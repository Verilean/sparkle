import Tools.ShippingGen5AccRouteR
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- No sorry / axiom / native_decide.

/-! # Check for `accServed0_of_cover_gatesR` (scripts/gen5/AC9_FREEZE.md)

The telescope of `accServed0_of_cover_gatesR` against `accServed0_of_cover_gates`: the new one has one extra non-Prop binder `lvl`
(skipped), and at the position of `hDS` it has `hK`; every other binder (name, info, type) and the conclusion agree by `==`.
`hDS` is not a binder of the new theorem. Controls: the walk without the `hDS ↦ hK` exception fails. Axioms.
Not claimed: supply of `ReachCover` / `GatesNoneAt` / `ClosesOfShape` / `ReadsSupplyAt`, a real kit, FG. -/

namespace Tests.Gen5.AC9TopCheck
open Lean Meta
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)

/-- Walk `a` (new) and `e` (old); in `a`, skip the binder named `extra`; the binder named `sw` in `e` must face `sw'` in `a`
(types not compared there). -/
partial def walk (allowSwap : Bool) (a e : Expr) (i : Nat := 0) (names : Array Name := #[]) : MetaM (Array Name) := do
  match a, e with
  | .forallE na ta ba bia, _ =>
    if na.eraseMacroScopes == `lvl then
      withLocalDecl na bia ta fun x => walk allowSwap (ba.instantiate1 x) e i (names.push `lvl)
    else match e with
    | .forallE ne te be bie =>
      let swapped := allowSwap && ne.eraseMacroScopes == `hDS && na.eraseMacroScopes == `hK
      unless swapped do
        unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "AC9 CHECK FAILED: binder {i} name {na} vs {ne}"
        unless bia == bie do throwError "AC9 CHECK FAILED: binder {i} info"
        unless ta == te do throwError "AC9 CHECK FAILED: binder {i} ({na}) type"
      -- the old binder must not be used later (so it can be instantiated by anything of its type)
      if swapped && be.hasLooseBVars then
        withLocalDecl ne bie te fun y =>
        withLocalDecl na bia ta fun x => walk allowSwap (ba.instantiate1 x) (be.instantiate1 y) (i + 1) (names.push na.eraseMacroScopes)
      else
        withLocalDecl na bia ta fun x =>
          walk allowSwap (ba.instantiate1 x) (be.instantiate1 (if swapped then mkConst ``True else x)) (i + 1)
            (names.push na.eraseMacroScopes)
    | _ => throwError "AC9 CHECK FAILED: extra binder {i} ({na})"
  | _, .forallE ne .. => throwError "AC9 CHECK FAILED: missing binder {i} ({ne})"
  | _, _ =>
    unless a == e do throwError "AC9 CHECK FAILED: conclusion"
    pure names

run_cmd Lean.Elab.Command.liftTermElabM do
  let a ← stmtOf ``Tools.ShippingGen5Acc.accServed0_of_cover_gatesR
  let e ← stmtOf ``Tools.ShippingGen5Acc.accServed0_of_cover_gates
  let names ← walk true a e
  if names.contains `hDS then throwError "AC9 CHECK FAILED: hDS is a binder"
  logInfo m!"AC9 BINDERS: accServed0_of_cover_gatesR = accServed0_of_cover_gates with hDS ↦ hK (+ lvl); conclusion =="
  let bad ← try let _ ← walk false a e; pure true catch _ => pure false
  if bad then throwError "AC9 CHECK CONTROL: walk without the swap accepted"
  logInfo "AC9 CONTROL: walk without the hDS ↦ hK exception rejected"
  for n in [``Tools.ShippingGen5Acc.accServed0_of_cover_gatesR, ``Tools.ShippingGen5Acc.dataOfShape_of_dataOfAt] do
    checkAxioms n
  logInfo "AC9 COUNTS: BINDERS 1 (+1 control), AXIOMS 2"

end Tests.Gen5.AC9TopCheck
