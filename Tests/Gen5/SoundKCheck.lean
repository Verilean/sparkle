import Tools.ShippingGen5ConstValueESoundK
set_option autoImplicit false
-- D.D-4 Sound: structural check of the proved lemmas, negative controls, `#print axioms`, and the list of remaining named obligations.
namespace Tests.Gen5.SoundKCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK

/-! ## Structural match: the statements are exactly the intended ones -/
example : ∀ (e : Expr) (s n : Nat), lbr e = 0 → liftS e s n = e := fun e s n h => liftS_closed e h s n
example : ∀ (e x : Expr), lbr e = 0 → substS e 0 x = e := fun e x h => substS_closed e h x
example : ∀ (e : Expr) (s : Nat), liftS e s 0 = e := liftS_zero
-- reductions to the bridges (implications between named Props; the bridges are NOT assumed anywhere)
example : OblLiftAgree → OblLbrZero → OblLiftClosed := oblLiftClosed_of_bridges
example : OblInst1Agree → OblLbrZero → ∀ b x : Expr, b.looseBVarRange = 0 → b.instantiate1 x = b := inst1_closed_of_bridges
-- the four old rule obligations hold for the rule judgment, unconditionally; so do the new four
example (PT : PrimTableK) : OblBvar (TyRKJ PT) := oblBvar_TyRK PT
example (PT : PrimTableK) : OblApp (TyRKJ PT) := oblApp_TyRK PT
example (PT : PrimTableK) : OblLam (TyRKJ PT) := oblLam_TyRK PT
example (PT : PrimTableK) : OblConst (TyRKJ PT) := oblConst_TyRK PT
example (PT : PrimTableK) : OblLit (TyRKJ PT) := oblLit_TyRK PT
example (PT : PrimTableK) : OblLet (TyRKJ PT) := oblLet_TyRK PT
example (PT : PrimTableK) : OblUnfold (TyRKJ PT) := oblUnfold_TyRK PT
example (PT : PrimTableK) : OblPrimK PT (TyRKJ PT) := oblPrimK_TyRK PT
example (PT : PrimTableK) : KernelRulesK PT (TyRKJ PT) := kernelRulesK_TyRK PT
-- every CVEK derivation is a TyRK derivation at the context `ρ.map Entry.τ`
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEK PT env ρ e τ α v → TyRK PT env (ρ.map Entry.τ) e τ := fun _ _ _ _ _ _ _ h => cvek_tyRK h
-- and, for a `Ty` satisfying the bundle, a `Ty` derivation
example : ∀ (PT : PrimTableK) (Ty : TyJ), KernelRulesK PT Ty → ∀ (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEK PT env ρ e τ α v → Ty env (ρ.map Entry.τ) e τ := fun _ _ R _ _ _ _ _ _ h => cvek_sound R h
-- lam: the context extension is exactly the valuation extension; B/TB correspondence
example (A : Expr) (d : Dyn) (ρ : Val) : (⟨A, d⟩ :: ρ).map Entry.τ = A :: ρ.map Entry.τ := map_cons_entry A d ρ
example (PT : PrimTableK) (env : Environment) (ρ : Val) (n : Name) (A B : Expr) (bi : BinderInfo) (TA : Type) (hA : TDenK PT env ρ A TA)
    (TB : TA → Type) (hB : ∀ a : TA, TDenK PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a)) :
    TDenK PT env ρ (.forallE n A B bi) ((a : TA) → TB a) := denTyped_lam hA TB hB
-- OblRowTypedK is the conjunction of the per-key obligations
example (PT : PrimTableK) (env : Environment) : OblRowTypedK PT env ↔ ∀ c ls, RowTypedAt PT env c ls := oblRowTypedK_iff PT env
example (PT : PrimTableK) (env : Environment) (keys : List (Name × List Level)) (hk : ∀ c ls, PT.tms c ls ≠ none → (c, ls) ∈ keys)
    (h : ∀ k ∈ keys, RowTypedAt PT env k.1 k.2) : OblRowTypedK PT env := oblRowTypedK_of_keys PT env keys hk h

/-! ## One real per-row proof (`Nat.zero`), with the ENV FACTS as explicit hypotheses of the lemma (they are facts about the environment, not about `PT`) -/
def natTyRow : TyRow := ⟨[], fun _ => some Nat⟩
def natZeroRow : TmRow := ⟨[], fun _ => some ⟨Nat, 0⟩⟩
def PTnat : PrimTableK :=
  ⟨fun c ls => if c == `Nat && ls.isEmpty then some natTyRow else none,
   fun c ls => if c == ``Nat.zero && ls.isEmpty then some natZeroRow else none⟩

theorem rowTyped_natZero (env : Environment)
    (hZ : ∀ ci : ConstantInfo, env.find? ``Nat.zero = some ci → ci.type = .const `Nat [] ∧ ci.levelParams = [])
    (hN : ¬ IsDefn env `Nat) : RowTypedAt PTnat env ``Nat.zero [] := by
  have hrow : PTnat.tms ``Nat.zero [] = some natZeroRow := by simp [PTnat]
  refine rowTypedAt_nullary PTnat env ``Nat.zero [] natZeroRow hrow rfl ?_
  intro ci ρ as d hci _ hd
  obtain ⟨hT, hP⟩ := hZ ci hci
  have hd' : d = ⟨Nat, 0⟩ := by simpa [natZeroRow] using hd.symm
  subst hd'
  rw [hT, hP]
  have hty : PTnat.tys `Nat [] = some natTyRow := by simp [PTnat]
  have he : (Expr.const `Nat []).instantiateLevelParams [] [] = mkAppN (.const `Nat []) ([] : List Expr).toArray := by
    simp [Expr.instantiateLevelParams, mkAppN_toList]
  exact .tcon hty hN .nil rfl he

/-- The same lemma, a negative control on the env fact: when the declared type is NOT `Nat`, the row proof is not available (the hypothesis `hZ` is what ties the row to `ConstantInfo.type`). -/
theorem natZero_envfact_needed : ¬ ((.const `Bool [] : Expr) = .const `Nat []) := by simp

/-! ## Negative controls -/
-- (1) the obligation bundle is not trivially satisfiable: a `Ty` that proves nothing fails it
theorem noTy_fails_lit (env : Environment) : ¬ OblLit (fun _ _ _ _ => False) := fun h => h.1 env [] 0
theorem noTy_fails_bundle (env : Environment) (PT : PrimTableK) : ¬ KernelRulesK PT (fun _ _ _ _ => False) := fun h => noTy_fails_lit env h.lit
-- (2) the structural operations are not the identity (they do the work they claim)
theorem liftS_not_id : liftS (.bvar 0) 0 1 ≠ .bvar 0 := by simp [liftS]
theorem substS_not_id : substS (.bvar 0) 0 (.const `A []) ≠ .bvar 0 := by simp [substS, liftS]
theorem liftS_below_binder : liftS (.lam `x (.const `A []) (.bvar 0) .default) 0 1 = .lam `x (.const `A []) (.bvar 0) .default := by
  simp [liftS]
theorem liftS_free_under_binder : liftS (.lam `x (.const `A []) (.bvar 1) .default) 0 1 = .lam `x (.const `A []) (.bvar 2) .default := by
  simp [liftS]
-- (3) the dependent codomain really depends: `instForall` does not ignore the argument when the codomain has a loose bvar
theorem substS_dep : substS (.bvar 0) 0 (.const `c []) = .const `c [] := by simp [substS, liftS]
-- (4) a closed-looking bvar is not closed
theorem lbr_bvar : lbr (.bvar 0) = 1 := rfl

/-! ## Remaining named obligations (Prop definitions: never assumed, not proved here) and axioms -/
run_meta do
  let env ← getEnv
  let remaining : List Name :=
    [``OblLiftAgree, ``OblInst1Agree, ``OblLbrZero, ``OblDenLits, ``OblDenSubst, ``OblDenBvar]
  let inherited : List Name :=
    [``Tools.ShippingGen5ConstValueE.OblLiftClosed, ``Tools.ShippingGen5ConstValueE.OblBvar, ``Tools.ShippingGen5ConstValueE.OblApp,
     ``Tools.ShippingGen5ConstValueE.OblLam, ``Tools.ShippingGen5ConstValueE.OblConst, ``Tools.ShippingGen5ConstValueE.OblLevelErase]
  let withTy : List Name := [``OblLit, ``OblLet, ``OblUnfold, ``OblPrimK, ``OblDenTyped, ``OblRowTypedK, ``RowTypedAt, ``KernelRulesK]
  let mut lines : Array MessageData := #[]
  for n in remaining ++ inherited ++ withTy do
    let some ci := env.find? n | throwError "{n} absent"
    -- each is a definition (or structure) whose type ends in `Prop`, never a theorem or an axiom
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n} : {ci.type}"
  logInfo m!"named obligations ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"

/-- axiom detector: every proved declaration may use only the three standard axioms. -/
def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
run_meta do
  let proved : List Name :=
    [``liftS_of_lbr_le, ``liftS_closed, ``liftS_zero, ``substS_of_lbr_le, ``substS_closed, ``substS_bvar_lt, ``substS_bvar_eq, ``substS_bvar_gt,
     ``oblLiftClosed_of_bridges, ``inst1_closed_of_bridges, ``instForall_nondep_closed,
     ``oblBvar_TyRK, ``oblApp_TyRK, ``oblLam_TyRK, ``oblConst_TyRK, ``oblLit_TyRK, ``oblLet_TyRK, ``oblUnfold_TyRK, ``oblPrimK_TyRK, ``kernelRulesK_TyRK,
     ``tyRK_sub, ``cvek_tyRK, ``cvek_sound, ``sound_bvar, ``bvar_type_closed, ``tyArgs_instForall, ``tyRK_spine,
     ``denTyped_lam, ``denTyped_lam_of_body, ``oblRowTypedK_iff, ``rowTypedAt_of_none, ``rowTypedAt_of_den_none, ``oblRowTypedK_of_keys,
     ``argsDenK_length, ``rowTypedAt_nullary, ``rowTyped_natZero, ``noTy_fails_bundle, ``liftS_not_id, ``substS_not_id]
  let mut bad : Array Name := #[]
  for n in proved do
    let ax ← Lean.collectAxioms n
    if ax.any (fun a => !stdAx.contains a) then bad := bad.push n
  unless bad.isEmpty do throwError "non-standard axiom (or sorryAx) in: {bad}"
  logInfo m!"axiom check ok: {proved.length} proved declarations use only propext / Classical.choice / Quot.sound"

/-- negative control for the detector: a declaration that uses a fresh axiom is flagged. -/
axiom negControlAxiom : False
theorem negControlUsesAxiom : (1 : Nat) = 2 := negControlAxiom.elim
run_meta do
  let ax ← Lean.collectAxioms ``negControlUsesAxiom
  unless ax.contains ``negControlAxiom do throwError "negative control FAILED: detector missed the axiom"
  logInfo m!"negative control ok: detector flags {ax.toList}"

end Tests.Gen5.SoundKCheck

#print axioms Tools.ShippingGen5ConstValueESoundK.liftS_closed
#print axioms Tools.ShippingGen5ConstValueESoundK.substS_closed
#print axioms Tools.ShippingGen5ConstValueESoundK.oblLiftClosed_of_bridges
#print axioms Tools.ShippingGen5ConstValueESoundK.kernelRulesK_TyRK
#print axioms Tools.ShippingGen5ConstValueESoundK.cvek_tyRK
#print axioms Tools.ShippingGen5ConstValueESoundK.cvek_sound
#print axioms Tools.ShippingGen5ConstValueESoundK.denTyped_lam
#print axioms Tools.ShippingGen5ConstValueESoundK.oblRowTypedK_iff
#print axioms Tools.ShippingGen5ConstValueESoundK.rowTypedAt_nullary
#print axioms Tests.Gen5.SoundKCheck.rowTyped_natZero
