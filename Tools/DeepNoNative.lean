import Lean

/-!
# Non-native closers for the trace goals of `#verify_elab_deep` (H2d)

The hierarchical checker's strict audit admits the three standard axioms only, so the trace closers it runs
(`sparkle.deepNoNative`) must not use `bv_decide` (`Lean.ofReduceBool`).  The register-step goals of a real
circuit are conjunctions of `if`/`bif` identities over Bool and literal-width atoms; the single-bit atoms
(`BitVec 1`: the encoding of a Bool, or a parser's `done` flag) occur under `&&&`.  `ved_cases_bv1` splits each such
atom into its two values, after which `simp_all` evaluates the `&&&`.
-/

theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by bv_omega

open Lean Meta Elab Tactic in
/-- Case-split every local `BitVec 1` variable of the main goal's context: `x = 0#1` or `x = 1#1`, substituted. -/
elab "ved_cases_bv1" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut names : Array Name := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``BitVec 1 && (ty.getArg! 0).nat? == some 1 then names := names.push d.userName
  for n in names do
    evalTactic (← `(tactic| rcases bv1_cases $(mkIdent n) with h | h <;> subst h))

open Lean Meta Elab Tactic in
/-- Is `e` an (in)equality of `BitVec`/`Bool`/`Nat`/`Int` atoms, or a `¬ ∧ ∨ ↔` of such? -/
partial def isBvProp (e : Lean.Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  let okTy (α : Lean.Expr) : Bool :=
    α.isConstOf ``Nat || α.isConstOf ``Int || α.isConstOf ``Bool || α.isAppOf ``BitVec || α.isAppOf ``Fin
  match e.getAppFnArgs with
  | (``Eq, #[α, _, _]) | (``LT.lt, #[α, _, _, _]) | (``LE.le, #[α, _, _, _]) | (``Ne, #[α, _, _]) => pure (okTy α)
  | (``Not, #[p]) => isBvProp p
  | (``And, #[p, q]) | (``Or, #[p, q]) | (``Iff, #[p, q]) => do pure ((← isBvProp p) && (← isBvProp q))
  | _ => pure false

open Lean Meta Elab Tactic in
/-- Clear the propositions of the context that are not facts about literal-width atoms (the loop equations, the
prefix guards): `simp_all` would rewrite with and inside each of them, on every branch of the split. -/
elab "ved_bv_ctx" : tactic => withMainContext do
  let mut g ← getMainGoal
  let lctx ← getLCtx
  for d in lctx.decls.toList.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    if (← isProp d.type) && !(← isBvProp d.type) then
      g ← g.tryClear d.fvarId
  replaceMainGoal [g]

/-- The non-native closer: split the conjunction, the Bool encodings and every `if`, evaluate each branch. -/
macro "ved_bv_close" : tactic =>
  `(tactic| (((repeat' apply And.intro) <;> (try simp only [cond_eq_ite]) <;> (try ved_cases_bv1) <;>
      ((repeat' split) <;> (try ved_bv_ctx) <;> (try simp_all) <;> (try bv_omega))); done))
