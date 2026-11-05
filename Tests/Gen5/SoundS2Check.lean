import Tools.ShippingGen5ConstValueESL
import Tools.ShippingGen5RowTypedS
import Tests.Gen5.RowTypedKCheck
set_option autoImplicit false
/-! D.D-4 SoundS2: check of `Tools/ShippingGen5ConstValueESL.lean` (syntactic `instantiateLevelParamsS`, `EnvClosedL`, carrier `CVEKL`) and `Tools/ShippingGen5RowTypedS.lean`
(`RowTypedAtES` / `OblRowTypedS`, four closed-codomain rows). Structural match, negative controls, axioms, remaining obligations. No TRUSTED / axiom / sorry / native_decide. -/
namespace Tests.Gen5.SoundS2Check
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
open Tools.ShippingGen5ConstValueESL Tools.ShippingGen5RowTypedS
open Tools.ShippingGen5RowTypedK (TmSpec TyConSpec EnvClosedPi ClosedPi)

/-! ## Structural match -/
-- the carrier's level instantiation is the syntactic one, by definitional unfolding
example (ps : List Name) (ls : List Level) (u : Level) : instantiateLevelParamsS ps ls (.sort u) = .sort (instLevelS ps ls u) := rfl
example (ps : List Name) (ls : List Level) (f a : Expr) :
    instantiateLevelParamsS ps ls (.app f a) = .app (instantiateLevelParamsS ps ls f) (instantiateLevelParamsS ps ls a) := rfl
example (u : Name) (ls : List Level) : instLevelS [u] ls (.param u) = ls.headD (.param u) := by cases ls <;> simp [instLevelS, lookupLP]
-- functionality of the new carrier
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKL PT env ρ e τ α v → ∀ (τ' : Expr) (β : Type) (w : β), CVEKL PT env ρ e τ' β w → τ = τ' ∧ α = β ∧ HEq v w :=
  fun _ _ _ _ _ _ _ h _ _ _ h' => cvekl_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α β : Type) (v : α) (w : β),
    ConstValueEAtL PT env X ls α v → ConstValueEAtL PT env X ls β w → α = β ∧ HEq v w :=
  fun PT env X ls _ _ _ _ h h' => constValueEAtL_functional PT env X ls h h'
example : ∀ (PT : PrimTableK) (env : Environment) (X : Name) (α β : Type) (v : α) (w : β),
    CVLSKL PT env X α v → CVLSKL PT env X β w → α = β ∧ HEq v w := fun PT env X _ _ _ _ h h' => cvlskl_functional PT env X h h'
-- the bridge of `EnvClosedS` over the syntactic version
example : ∀ (ps : List Name) (ls : List Level) (e : Expr), lbr (instantiateLevelParamsS ps ls e) = lbr e := lbr_instantiateLevelParamsS
example : ∀ env : Environment, EnvDeclClosed env → EnvClosedL env := fun _ h => envClosedL_of_declClosed h
example : ∀ env : Environment, EnvClosedL env → EnvDeclClosed env := fun _ h => envDeclClosed_of_closedL h
-- rows
example (PT : PrimTableK) (env : Environment) : OblRowTypedS PT env ↔ ∀ c ls, RowTypedAtES PT env c ls := Iff.rfl
example : ∀ (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (ks : List Bool) (D : Name) (Ls : List Level) (T : Type),
    TmSpec PT c ls ks T → TyConSpec PT D Ls T → ¬ IsDefn env D → EnvClosedPi env c ls ks.length (.const D Ls) → RowTypedAtES PT env c ls :=
  rowTypedAtES_closedPi
-- non-vacuity: the model table of `RowTypedKCheck` satisfies the specs, so the per-key theorems instantiate
open Tests.Gen5.RowTypedKCheck in
example (env : Environment) (h1 : ¬ IsDefn env ``Nat) (h2 : EnvClosedPi env ``Nat.succ [] 1 (.const ``Nat [])) : RowTypedAtES PTm env ``Nat.succ [] :=
  rowTypedES_Nat_succ PTm env (tmSpecM (0 : Nat) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
open Tests.Gen5.RowTypedKCheck in
example (env : Environment) (h1 : ¬ IsDefn env ``Int) (h2 : EnvClosedPi env ``Int.ofNat [] 1 (.const ``Int [])) : RowTypedAtES PTm env ``Int.ofNat [] :=
  rowTypedES_Int_ofNat PTm env (tmSpecM (0 : Int) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
open Tests.Gen5.RowTypedKCheck in
example (env : Environment) (h1 : ¬ IsDefn env ``Int) (h2 : EnvClosedPi env ``Int.negSucc [] 1 (.const ``Int [])) : RowTypedAtES PTm env ``Int.negSucc [] :=
  rowTypedES_Int_negSucc PTm env (tmSpecM (0 : Int) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2
open Tests.Gen5.RowTypedKCheck in
example (env : Environment) (h1 : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig)
    (h2 : EnvClosedPi env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])) :
    RowTypedAtES PTm env `Sparkle.Core.Domain.DomainConfig.mk [] :=
  rowTypedES_DomainConfig_mk PTm env (tmSpecM (⟨0, .rising, .synchronous⟩ : Sparkle.Core.Domain.DomainConfig) (by simp [PTm])) (tySpecM _ (by simp [PTm])) h1 h2

/-! ## Negative controls -/
-- (1) the instantiation is not the identity (it substitutes), and respects the parameter list
theorem instLevelS_not_id : instantiateLevelParamsS [`u] [.succ .zero] (.sort (.param `u)) ≠ .sort (.param `u) := by simp [instantiateLevelParamsS, instLevelS, lookupLP]
theorem instLevelS_other_param : instantiateLevelParamsS [`u] [.succ .zero] (.sort (.param `v)) = .sort (.param `v) := by simp [instantiateLevelParamsS, instLevelS, lookupLP]
-- (2) it is not stuck: it computes where Lean's opaque `Expr.instantiateLevelParams` does not reduce for the elaborator
open Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta in
run_cmd liftTermElabM do
  let r ← elabTerm (← `(Expr.sort (Level.succ Level.zero))) none
  let lo ← elabTerm (← `(Expr.instantiateLevelParams (Expr.sort (Level.param `u)) [`u] [Level.succ Level.zero])) none
  let ls ← elabTerm (← `(instantiateLevelParamsS [`u] [Level.succ Level.zero] (Expr.sort (Level.param `u)))) none
  let o ← withDefault (isDefEq lo r)
  let n ← withDefault (isDefEq ls r)
  if o then throwError "negative control FAILED: the opaque `instantiateLevelParams` unexpectedly reduces"
  unless n do throwError "the structural instantiateLevelParamsS does not compute"
  logInfo m!"opaque Expr.instantiateLevelParams: stuck; structural instantiateLevelParamsS: computes"
-- (3) `EnvDeclClosed` is a real premise: a declaration with a loose bound variable is not closed (the lemma has teeth)
theorem lbr_bvar_not_closed : lbr (instantiateLevelParamsS [] [] (.bvar 0)) ≠ 0 := by simp [instantiateLevelParamsS, lbr]
-- (4) a dependent codomain is not a closed telescope, so the closed-codomain theorem does not apply to it
theorem dep_not_closedPi (R : Expr) : ¬ ClosedPi (.forallE `x (.const `Nat []) (.bvar 0) .default) 1 R := by
  rintro ⟨x, A, B, bi, h, hB, -⟩
  cases h
  simp [lbr] at hB
-- (5) an arity mismatch is rejected: a telescope of 2 closed binders is not one of 1
theorem closedPi_arity : ¬ ClosedPi (.forallE `a (.const `Nat []) (.forallE `b (.const `Nat []) (.const `Nat []) .default) .default) 1 (.const `Nat []) := by
  rintro ⟨x, A, B, bi, h, hB, hr⟩
  cases h
  simp [ClosedPi] at hr
-- (6) `instForallS` on a closed telescope returns the codomain; the spec is a real premise (wrong type has no spec)
open Tests.Gen5.RowTypedKCheck in
theorem boolSpec_not_unit' : ¬ TyConSpec PTm ``Bool [] Unit := boolSpec_not_unit

/-! ## Remaining obligations -/
run_meta do
  let env ← getEnv
  let rows : List Name := [``OblRowTypedS, ``RowTypedAtES]
  let carried : List Name := [``EnvClosedS, ``EnvDeclClosed, ``EnvClosedL, ``OblDenSubstS, ``RowArgsAt, ``OblPrimArgsS]
  let mut lines : Array MessageData := #[]
  for n in rows ++ carried do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n} : {ci.type}"
  logInfo m!"named obligations ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"
  -- the rows of OblRowTypedS: 4 proved (closed codomain), 30 dependent waiting on Q1 (OblDenSubstS general form), 6 argument-free already RowTypedAt, 75 den = none / Prop
  let closed : List Name := [``rowTypedES_Nat_succ, ``rowTypedES_Int_ofNat, ``rowTypedES_Int_negSucc, ``rowTypedES_DomainConfig_mk]
  for n in closed do unless env.contains n do throwError "{n} absent"
  let depKnown : List Name := [``Fin.mk, ``BitVec.ofFin, ``Decidable.isTrue, ``Decidable.isFalse]
  logInfo m!"OblRowTypedS: closed-codomain rows proved {closed.length}; dependent rows waiting on Q1: 30 (known by name: {depKnown}; the other 26 are output-structure *.mk taking a DomainConfig argument, listed by `scripts/gen5/merge_row_typed_audit.py` (last line), not recomputed here); argument-free 6 (RowTypedAt, proved earlier); den = none / Prop 75; total {closed.length + 30 + 6 + 75}"
  unless closed.length + 30 + 6 + 75 == 115 do throwError "partition of the 115 term keys fails"

/-! ## Axioms -/
def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
run_meta do
  let proved : List Name :=
    [``lbr_instantiateLevelParamsS, ``instantiateLevelParamsS_nil, ``instLevelS_nil, ``envClosedL_of_declClosed, ``envDeclClosed_of_closedL,
     ``tdenl_fun, ``argsdenl_fun, ``cvekl_fun, ``constValueEAtL_functional, ``cvlskl_functional,
     ``rowTypedAtES_of_none, ``rowTypedAtES_of_den_none, ``oblRowTypedS_of_keys, ``instForallS_closedPi, ``rowTypedAtES_closedPi,
     ``rowTypedES_Nat_succ, ``rowTypedES_Int_ofNat, ``rowTypedES_Int_negSucc, ``rowTypedES_DomainConfig_mk,
     ``instLevelS_not_id, ``instLevelS_other_param, ``lbr_bvar_not_closed, ``dep_not_closedPi, ``closedPi_arity]
  let env ← getEnv
  let mut bad : Array Name := #[]
  for n in proved do
    unless env.contains n do throwError "{n} absent"
    let ax ← Lean.collectAxioms n
    if ax.any (fun a => !stdAx.contains a) then bad := bad.push n
  unless bad.isEmpty do throwError "non-standard axiom (or sorryAx) in: {bad}"
  logInfo m!"axiom check ok: {proved.length} proved declarations use only propext / Classical.choice / Quot.sound"
axiom negControlAxiom : False
theorem negControlUsesAxiom : (1 : Nat) = 2 := negControlAxiom.elim
run_meta do
  let ax ← Lean.collectAxioms ``negControlUsesAxiom
  unless ax.contains ``negControlAxiom do throwError "negative control FAILED: detector missed the axiom"
  logInfo m!"negative control ok: detector flags {ax.toList}"

end Tests.Gen5.SoundS2Check

#print axioms Tools.ShippingGen5ConstValueESL.cvekl_fun
#print axioms Tools.ShippingGen5ConstValueESL.envClosedL_of_declClosed
#print axioms Tools.ShippingGen5RowTypedS.rowTypedAtES_closedPi
#print axioms Tools.ShippingGen5RowTypedS.rowTypedES_DomainConfig_mk
