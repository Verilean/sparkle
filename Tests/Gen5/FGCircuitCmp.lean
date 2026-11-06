import Lean
set_option autoImplicit false
-- FG circuit pilot S2r: the ONE comparison criterion of the FGCircuitPilotCheck21/26/27/28/30/31/32/37 signature checks (docs/FG-CIRCUIT-PILOT.md §42). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # FGCircuitCmp

Reviewer finding (S2r): in Check21/26/27/28/30/31/32 the positive case was compared at the default transparency, while the mutants were compared at reducible/instances: not the same criterion.

Here positive and negative cases go through ONE function, `stmtEq`. The caller normalises both sides with the same normalisation (its own whitelist, applied to the real type once and cached, and to every expected statement and mutant; `normCommon` below is applied on top of it for both).
`stmtEq a e` holds iff the two normal forms are structurally equal (`Expr.eqv`: alpha equivalence, no unfolding, no `isDefEq`, so the answer does not depend on a transparency setting) AND the binder kinds of EVERY binder at every depth agree (not only the top-level telescope).
`checkSame` throws when `stmtEq` is false (positive case); `checkDiff` throws when `stmtEq` is true (mutant). -/
namespace Tests.Gen5.FGCircuitCmp
open Lean Meta

/-- the binder kinds of every binder in traversal order (all depths: `∀`, `fun`, `let` bodies, application arguments, ...) -/
partial def allBinderInfos : Lean.Expr → List BinderInfo
  | .forallE _ d b bi => bi :: (allBinderInfos d ++ allBinderInfos b)
  | .lam _ d b bi => bi :: (allBinderInfos d ++ allBinderInfos b)
  | .app f a => allBinderInfos f ++ allBinderInfos a
  | .letE _ t v b _ => allBinderInfos t ++ allBinderInfos v ++ allBinderInfos b
  | .mdata _ e => allBinderInfos e
  | .proj _ _ e => allBinderInfos e
  | _ => []

/-- literal data the real statements name by a constant (the output shape of the root); unfolded on both sides -/
def commonUnfold : List Name := [`Tools.ShippingFGCircuitS1kStmt.shHft]

/-- the shared tail of every check's normalisation: metavariables instantiated, metadata erased, the constants of the checks' own namespaces (`Tests.Gen5.FGCircuitPilotCheck*`: the expected statements, their abbreviations and knobs) unfolded, the constants that are `Name` literals (`hftRoot`, `hftHttp`, ...) unfolded, beta reduced -/
def normCommon (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  let e := e.replace fun x => match x with | .mdata _ y => some y | _ => none
  let step (e : Lean.Expr) : MetaM Lean.Expr :=
    Meta.transform e (post := fun e => do
      let e := e.headBeta
      if let .const c _ := e.getAppFn then
        let isNameConst : Bool := match (← getEnv).find? c with
          | some ci => ci.type.isConstOf ``Lean.Name
          | none => false
        if (`Tests.Gen5).isPrefixOf c || isNameConst || commonUnfold.contains c then
          if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
      return .done e)
  let mut e := e
  for _ in [0:4] do
    e ← step e
  return e

/-- THE criterion (positive and negative cases alike) -/
def stmtEq (a e : Lean.Expr) : Bool := a.eqv e && allBinderInfos a == allBinderInfos e

/-- the first place where two expressions differ (for the error message of a failed positive case) -/
partial def firstDiff (a e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if a.eqv e then none
  else match a, e with
    | .forallE _ d b _, .forallE _ d' b' _ => (firstDiff d d').orElse fun _ => firstDiff b b'
    | .lam _ d b _, .lam _ d' b' _ => (firstDiff d d').orElse fun _ => firstDiff b b'
    | .app f x, .app f' x' => if a.getAppNumArgs == e.getAppNumArgs && f.getAppFn.eqv f'.getAppFn then (firstDiff f f').orElse fun _ => firstDiff x x' else some (a, e)
    | _, _ => some (a, e)

def checkSame (what : String) (a e : Lean.Expr) : MetaM Unit := do
  unless stmtEq a e do
    if a.eqv e then throwError "{what}: type is NOT the expected statement: the binder kinds differ"
    match firstDiff a e with
    | some (x, y) => throwError "{what}: type is NOT the expected statement; first difference:\n  real:     {(toString x).take 700}\n  expected: {(toString y).take 700}"
    | none => throwError "{what}: type is NOT the expected statement"

def checkDiff (what : String) (a e : Lean.Expr) : MetaM Unit := do
  if stmtEq a e then throwError "{what}: the MUTANT was accepted (same normal form, same binder kinds)"

end Tests.Gen5.FGCircuitCmp
