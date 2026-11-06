import Lean
set_option autoImplicit false
-- FG circuit pilot S2r: the ONE comparison criterion of the FGCircuitPilotCheck21/26/27/28/30/31/32/37 signature checks (docs/FG-CIRCUIT-PILOT.md §42). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # FGCircuitCmp

Reviewer finding (S2r): in Check21/26/27/28/30/31/32 the positive case was compared at the default transparency, while the mutants were compared at reducible/instances: not the same criterion.

Here positive and negative cases go through ONE function, `stmtEq`. The caller normalises both sides with the same normalisation (its own whitelist, applied to the real type once and cached, and to every expected statement and mutant; `normCommon` below is applied on top of it for both).
`stmtEq a e` holds iff the two normal forms are structurally equal (`Expr.eqv`: alpha equivalence; `stmtEq` ITSELF does not unfold and does not call `isDefEq`, so its answer does not depend on a transparency setting; the unfolding / `whnf` / instance checks happen in the preceding `normCommon`, for both sides alike) AND the binder kinds of EVERY binder at every depth agree (not only the top-level telescope).
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
def commonUnfold : List Name := [`Tools.ShippingFGCircuitS1kStmt.shHft, `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machineInners, `Tools.ShippingFGCircuitS2hHist.StartEv]

/-- `inst` is the standard instance `inst0` (structurally, or definitionally at default transparency): a non-standard instance (an always-`false` `BEq Nat`, another `OfNat Nat` instance) is NOT accepted -/
def isStdInst (inst inst0 : Lean.Expr) : MetaM Bool := do
  if inst.eqv inst0 then return true
  withTransparency .default (isDefEq inst inst0)

/-- a literal Boolean: `true`, `false`, or `n == m` for two `Nat` numerals, where the `BEq Nat` instance is the standard (synthesised) one -/
def litBool? (c : Lean.Expr) : MetaM (Option Bool) := do
  match c with
  | .const ``Bool.true _ => return some true
  | .const ``Bool.false _ => return some false
  | _ =>
    if c.isAppOfArity ``BEq.beq 4 && (c.getArg! 0).isConstOf ``Nat then
      match c.getArg! 2, c.getArg! 3 with
      | .lit (.natVal a), .lit (.natVal b) =>
        let std ← synthInstance (mkApp (.const ``BEq [0]) (.const ``Nat []))
        if ← isStdInst (c.getArg! 1) std then return some (a == b) else return none
      | _, _ => return none
    else return none

/-- `if b then x else y` with a literal Boolean test: the chosen branch -/
def iteLit (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.isAppOfArity ``ite 5 then
    let c := e.getArg! 1
    if c.isAppOfArity ``Eq 3 && (c.getArg! 2).isConstOf ``Bool.true then
      match ← litBool? (c.getArg! 1) with
      | some true => return some (e.getArg! 3)
      | some false => return some (e.getArg! 4)
      | none => return none
    else return none
  else return none

/-- the shared tail of every check's normalisation (`reduceHeads`: heads of computed types evaluated by `whnf`, the same list for every statement): metavariables instantiated, metadata erased, the constants of the checks' own namespaces (`Tests.Gen5.FGCircuitPilotCheck*`: the expected statements, their abbreviations and knobs) unfolded, `if` on a literal Boolean selected, applications of theorems (proofs) replaced by one constant, the constants that are `Name` literals (`hftRoot`, `hftHttp`, ...) unfolded, beta reduced -/
def normCommon (e : Lean.Expr) (reduceHeads : List Name := []) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  let e := e.replace fun x => match x with | .mdata _ y => some y | _ => none
  let step (e : Lean.Expr) : MetaM Lean.Expr :=
    Meta.transform e (post := fun e => do
      let e := e.headBeta
      -- a `Nat` numeral is the same whether it was elaborated as `OfNat.ofNat Nat n _` or kept as the raw literal
      if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Nat then
        if let .lit (.natVal n) := e.getArg! 1 then
          if ← isStdInst (e.getArg! 2) (mkApp (.const ``instOfNatNat []) (.lit (.natVal n))) then return .done (.lit (.natVal n))
      if let some e' ← iteLit e then return .visit e'
      -- a structure projection is the same whether it was elaborated as `Prod.fst x` or as the primitive `x.1`: both become the primitive projection
      if let .const c _ := e.getAppFn then
        if let some info ← getProjectionFnInfo? c then
          if !info.fromClass && e.getAppNumArgs > info.numParams then
            let args := e.getAppArgs
            let ctor ← getConstInfoCtor info.ctorName
            return .visit (mkAppN (Lean.Expr.proj ctor.induct info.i args[info.numParams]!) (args.extract (info.numParams + 1) args.size))
      -- computed types / lists named by the caller (`SType.Type (.bits 6)`, `List.take 6 [...]`): evaluated by `whnf` (default transparency), the same for every statement
      if let .const c _ := e.getAppFn then
        if reduceHeads.contains c then
          let r ← withTransparency .all (whnf e)
          if r != e then return .visit r
        let isNameConst : Bool := match (← getEnv).find? c with
          | some ci => ci.type.isConstOf ``Lean.Name
          | none => false
        if (`Tests.Gen5).isPrefixOf c || isNameConst || commonUnfold.contains c then
          if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
      return .done e)
  -- proofs are irrelevant: an application of a theorem (or `Eq.refl`) is replaced as a whole (before its arguments are visited) by `proofIrrelevant P`, where `P` is its type (the proposition is kept: two proofs are equal only if they prove the same proposition). The decision rests on the type (`isProof`: the type is a `Prop`), never on the NAME of a constant: a `def _proof_a : Nat := 0` is data and is kept. `Meta.transform` opens binders with free variables, so `inferType` never sees a loose bound variable; if inference fails the term is kept.
  let proofs (e : Lean.Expr) : MetaM Lean.Expr :=
    Meta.transform e (pre := fun e => do
      if let .const c _ := e.getAppFn then
        let cand : Bool := c == ``Eq.refl || c == ``rfl || (match (← getEnv).find? c with | some (.thmInfo _) => true | _ => false)
        if cand && !e.hasLooseBVars then
          try
            if ← Meta.isProof e then
              return .done (mkApp (.const `proofIrrelevant []) (← instantiateMVars (← inferType e)))
          catch _ => pure ()
      return .continue)
  let mut e ← proofs e
  for _ in [0:4] do
    e ← step e
  proofs e

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
