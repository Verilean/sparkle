import Tools.ShippingGen5ConstValueELProof
import Tools.ShippingGen5EnvDeclClosed
import Tools.ShippingGen5RowTypedS
set_option autoImplicit false
/-! D.D-4 SoundS3: check of `Tools/ShippingGen5ConstValueELProof.lean` (the `ESProof` lemmas on the level-syntactic carrier `CVEKL`) and
`Tools/ShippingGen5EnvDeclClosed.lean` (the localised `EnvDeclClosed` hypothesis). Structural match, negative controls, axioms, remaining obligations.
The corpus audit of `EnvDeclClosed` is a META AUDIT in `Tests/Gen5/EnvDeclClosedAudit*.lean` (needs the Sparkle corpus imports; its numbers are in draft §SoundS3), not repeated here.
No TRUSTED / axiom / sorry / native_decide. -/
namespace Tests.Gen5.SoundS3Check
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
open Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueELProof Tools.ShippingGen5EnvDeclClosed

/-! ## Structural match: each lemma has the `CVEKL` shape and takes `EnvClosedL` -/
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedL env → ∀ (E : Entry) (s : Nat) (ρ ρ' : Val), InsV E s ρ ρ' →
    ∀ (e τ : Expr) (α : Type) (v : α), CVEKL PT env ρ e τ α v → CVEKL PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
  fun _ _ hcl _ _ _ _ hI _ _ _ _ h => cvekl_wk hcl hI h
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedL env → ∀ (E : Entry) (s : Nat) (ρ ρ' : Val), InsV E s ρ ρ' →
    ∀ (τ : Expr) (T : Type), TDenL PT env ρ τ T → TDenL PT env ρ' (liftS τ s 1) T :=
  fun _ _ hcl _ _ _ _ hI _ _ h => tdenl_wk hcl hI h
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedL env → ∀ (A : Expr) (TA : Type) (av : TA) (x : Expr), SafeArg x →
    ∀ (k : Nat) (ρ ρ' : Val), SubVL PT env A TA av x k ρ ρ' →
    ∀ (e τ : Expr) (α : Type) (v : α), CVEKL PT env ρ e τ α v → CVEKL PT env ρ' (substS e k x) (substS τ k x) α v :=
  fun _ _ hcl _ _ _ _ hx _ _ _ hS _ _ _ _ h => cvekl_subst hcl hx hS h
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedL env → ∀ (ρ : Val) (A B x : Expr) (TA T : Type) (av : TA), SafeArg x →
    TDenL PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T → CVEKL PT env ρ x A TA av → TDenL PT env ρ (substS B 0 x) T :=
  fun _ _ hcl _ _ _ _ _ _ _ hx hB hv => oblDenSubstL_safe hcl hx hB hv
example (PT : PrimTableK) (env : Environment) : OblDenBvarL PT env := oblDenBvarL PT env
example (PT : PrimTableK) (env : Environment) : WfValL PT env [] := wfValL_nil PT env
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedL env →
    (∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) → (∀ ρ : Val, TDenL PT env ρ (.const `String []) String) → OblDenSubstL PT env → OblDenTypedL PT env :=
  fun _ _ => denTypedL
-- the plain environment fact is the only environment hypothesis
example : ∀ (PT : PrimTableK) (env : Environment), EnvDeclClosed env →
    (∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) → (∀ ρ : Val, TDenL PT env ρ (.const `String []) String) → OblDenSubstL PT env → OblDenTypedL PT env :=
  fun _ _ => denTypedL_of_declClosed
-- soundness of the rules against any judgment satisfying the bundle (an implication between named Props)
example : ∀ (PT : PrimTableK) (env : Environment) (Ty : TyJ), KernelRulesKL Ty → OblPrimArgsL PT env → ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKL PT env ρ e τ α v → Ty env (ρ.map Entry.τ) e τ :=
  fun _ _ _ R hP _ _ _ _ _ h => cvekl_sound R hP h
-- the bundle is satisfiable (not vacuous)
example (PT : PrimTableK) : KernelRulesKL (TyRKLJ PT) := kernelRulesKL_TyRKL PT
-- nullary rows have no argument-typing obligation, rows with no entry neither
example (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (h : PT.tms c ls = none) : RowArgsAtL PT env c ls := rowArgsAtL_of_none PT env c ls h
-- the localised hypothesis
example (env : Environment) : EnvDeclClosedOn env (fun _ => True) ↔ EnvDeclClosed env := envDeclClosedOn_univ_iff env
example (env : Environment) (hz : OblLbrZero) (h : KernelClosedInvariant env) : EnvClosedL env := envClosedL_of_declClosed (envDeclClosed_of_kernel hz h)

/-! ## Negative controls -/
/-- the empty table: no type row, no term row -/
def PTe : PrimTableK := ⟨fun _ _ => none, fun _ _ => none⟩
-- (1) well-formedness is a real premise: a junk entry (label `Sort 0` for a `Nat`-valued entry) makes the valuation ill-formed, so `oblDenBvarL` does not hold for arbitrary valuations
theorem sort_not_tden (env : Environment) (ρ : Val) (T : Type) : ¬ TDenL PTe env ρ (.sort 0) T := by
  intro h
  cases h with
  | tcon hrow _ _ _ he => exact spine_ne he (by intros; simp [Expr.getAppFn])
  | tunfold _ _ he => exact spine_ne he (by intros; simp [Expr.getAppFn])
theorem junk_not_wf (env : Environment) : ¬ WfValL PTe env [⟨.sort 0, ⟨Nat, (0 : Nat)⟩⟩] := by
  intro h
  exact sort_not_tden env _ Nat (by simpa [liftS] using h 0 _ rfl)
-- (2) `EnvClosedL` is a real premise: a loose bound variable survives level instantiation, so a declaration with one is not closed
theorem lbr_bvar_not_closed : lbr (instantiateLevelParamsS [] [] (.bvar 0)) ≠ 0 := by simp [instantiateLevelParamsS, lbr]
-- (3) `EnvDeclClosedOn` localises: the empty set is trivial, so a localised fact says nothing about other names (it does not imply the global one by itself)
example (env : Environment) : EnvDeclClosedOn env (fun _ => False) := fun _ h => h.elim
-- (4) `SafeArg` is a real restriction (the restricted substitution lemma is not the general one): a `lam` argument is not safe
theorem lam_not_safe (A b : Expr) : ¬ SafeArg (.lam `x A b .default) := by
  rintro ⟨h, -, -⟩; simp [Expr.isLambda] at h

/-! ## Remaining obligations (Prop definitions, none assumed or proved here) -/
run_meta do
  let env ← getEnv
  let obls : List Name := [``OblDenSubstL, ``OblPrimArgsL, ``RowArgsAtL, ``EnvDeclClosed, ``EnvClosedL, ``KernelClosedInvariant, ``OblLbrZero,
    ``Tools.ShippingGen5RowTypedS.OblRowTypedS, ``Tools.ShippingGen5RowTypedS.RowTypedAtES]
  let mut lines : Array MessageData := #[]
  for n in obls do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n}"
  logInfo m!"named obligations ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"

/-! ## Axioms -/
def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
run_meta do
  let proved : List Name :=
    [``tdenl_wk, ``argsdenl_wk, ``cvekl_wk, ``subvl_get, ``subvl_wk, ``tdenl_subst, ``argsdenl_subst, ``cvekl_subst,
     ``wfValL_nil, ``wfValL_cons, ``oblDenBvarL, ``tdenL_const_nullary, ``oblDenLitsL_of_rows, ``oblDenSubstL_safe, ``denTypedL_aux, ``denTypedL,
     ``tyArgsL_instForallS, ``kernelRulesKL_TyRKL, ``tyRKL_sub, ``tyArgsL_sub, ``rowArgsAtL_of_none, ``argsdenl_length, ``rowArgsAtL_nullary, ``cvekl_tyRKS, ``cvekl_sound,
     ``cvekl_wk_of_declClosed, ``cvekl_subst_of_declClosed, ``denTypedL_of_declClosed,
     ``envDeclClosedOn_univ_iff, ``envDeclClosedOn_mono, ``envDeclClosedOn_of_list, ``envDeclClosed_of_on, ``envDeclClosed_of_kernel,
     ``sort_not_tden, ``junk_not_wf, ``lbr_bvar_not_closed, ``lam_not_safe]
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

end Tests.Gen5.SoundS3Check

#print axioms Tools.ShippingGen5ConstValueELProof.cvekl_wk
#print axioms Tools.ShippingGen5ConstValueELProof.cvekl_subst
#print axioms Tools.ShippingGen5ConstValueELProof.denTypedL
#print axioms Tools.ShippingGen5ConstValueELProof.cvekl_sound
#print axioms Tools.ShippingGen5EnvDeclClosed.envDeclClosed_of_kernel
