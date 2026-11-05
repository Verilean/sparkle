import Tools.ShippingGen5ConstValueESProof
set_option autoImplicit false
-- D.D-4 SoundS: structural match of the proved statements about the syntactic carrier `CVEKS`, negative controls, `#print axioms`, remaining named obligations.
namespace Tests.Gen5.SoundSCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES

/-! ## Structural match: the statements are exactly the intended ones -/
-- functionality of the new carrier (same shape as `cvek_fun`)
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKS PT env ρ e τ α v → ∀ (τ' : Expr) (β : Type) (w : β), CVEKS PT env ρ e τ' β w → τ = τ' ∧ α = β ∧ HEq v w :=
  fun _ _ _ _ _ _ _ h _ _ _ h' => cveks_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α β : Type) (v : α) (w : β),
    ConstValueEAtS PT env X ls α v → ConstValueEAtS PT env X ls β w → α = β ∧ HEq v w :=
  fun PT env X ls _ _ _ _ h h' => constValueEAtS_functional PT env X ls h h'
example : ∀ (PT : PrimTableK) (env : Environment) (X : Name) (α β : Type) (v : α) (w : β),
    CVLSKS PT env X α v → CVLSKS PT env X β w → α = β ∧ HEq v w := fun PT env X _ _ _ _ h h' => cvlsks_functional PT env X h h'
-- the carrier's operations are the structural ones (definitional unfolding, no opaque `Expr` operation)
example (b : Expr) (a : Expr) (as : List Expr) (y : Name) (A : Expr) (bi : BinderInfo) :
    betaS (.lam y A b bi) (a :: as) = betaS (substS b 0 a) as := rfl
example (n : Name) (A B a : Expr) (bi : BinderInfo) (as : List Expr) :
    instForallS (.forallE n A B bi) (a :: as) = instForallS (substS B 0 a) as := rfl
-- commutation lemmas
example : ∀ (B : Expr) (k s n : Nat) (x : Expr), k ≤ s → liftS (substS B k x) s n = substS (liftS B (s + 1) n) k (liftS x (s - k) n) := liftS_substS
example : ∀ (B : Expr) (m k : Nat) (y x : Expr), m ≤ k → substS (substS B m y) k x = substS (substS B (k + 1) x) m (substS y (k - m) x) := substS_substS
example : ∀ (B : Expr) (a m k : Nat) (x : Expr), a + m ≤ k → substS (liftS B a m) k x = liftS (substS B (k - m) x) a m := substS_liftS_ge
example : ∀ (B : Expr) (a n c : Nat) (x : Expr), a ≤ c → c < a + n → substS (liftS B a n) c x = liftS B a (n - 1) := substS_liftS_in
example (x : Expr) (hx : SafeArg x) (as : List Expr) (f : Expr) (k : Nat) :
    substS (betaS f as) k x = betaS (substS f k x) (as.map (fun a => substS a k x)) := substS_betaS hx as f k
example (x : Expr) (hx : SafeArg x) (as : List Expr) (T : Expr) (k : Nat) :
    substS (instForallS T as) k x = instForallS (substS T k x) (as.map (fun a => substS a k x)) := substS_instForallS hx as T k
-- weakening and substitution of derivations
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ (E : Entry) (s : Nat) (ρ ρ' : Val), InsV E s ρ ρ' →
    ∀ (e τ : Expr) (α : Type) (v : α), CVEKS PT env ρ e τ α v → CVEKS PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
  fun _ _ hcl _ _ _ _ hI _ _ _ _ h => cveks_wk hcl hI h
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ (A : Expr) (TA : Type) (av : TA) (x : Expr), SafeArg x →
    ∀ (k : Nat) (ρ ρ' : Val), SubV PT env A TA av x k ρ ρ' →
    ∀ (e τ : Expr) (α : Type) (v : α), CVEKS PT env ρ e τ α v → CVEKS PT env ρ' (substS e k x) (substS τ k x) α v :=
  fun _ _ hcl _ _ _ _ hx _ _ _ hS _ _ _ _ h => cveks_subst hcl hx hS h
-- P1
example : ∀ (PT : PrimTableK) (env : Environment), OblDenBvarS PT env := oblDenBvarS
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ ρ : Val, WfValS PT env ρ → ∀ (A : Expr) (TA : Type) (hA : TDenS PT env ρ A TA) (a : TA),
    WfValS PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) := fun _ _ hcl _ hρ _ _ hA a => wfValS_cons hcl hρ hA a
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ (ρ : Val) (A B x : Expr) (TA T : Type) (av : TA), SafeArg x →
    TDenS PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T → CVEKS PT env ρ x A TA av → TDenS PT env ρ (substS B 0 x) T :=
  fun _ _ hcl _ _ _ _ _ _ _ hx hB hv => oblDenSubstS_safe hcl hx hB hv
example (PT : PrimTableK) (env : Environment) (hcl : EnvClosedS env)
    (hN : ∀ ρ : Val, TDenS PT env ρ (.const `Nat []) Nat) (hS : ∀ ρ : Val, TDenS PT env ρ (.const `String []) String)
    (hsub : OblDenSubstS PT env) : OblDenTypedS PT env := denTypedS hcl hN hS hsub
-- P2
example (PT : PrimTableK) : KernelRulesKS (TyRKSJ PT) := kernelRulesKS_TyRKS PT
example : ∀ (PT : PrimTableK) (env : Environment), OblPrimArgsS PT env → ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKS PT env ρ e τ α v → TyRKS PT env (ρ.map Entry.τ) e τ := fun _ _ hP _ _ _ _ _ h => cveks_tyRKS hP h
example : ∀ (PT : PrimTableK) (Ty : TyJ), KernelRulesKS Ty → ∀ (env : Environment), OblPrimArgsS PT env → ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKS PT env ρ e τ α v → Ty env (ρ.map Entry.τ) e τ := fun _ _ R _ hP _ _ _ _ _ h => cveks_sound R hP h
example (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow) (hrow : PT.tms c ls = some row) (hk : row.kinds = []) :
    RowArgsAt PT env c ls := rowArgsAt_nullary PT env c ls row hrow hk

/-! ## Negative controls -/
-- (1) the obligation bundle is not trivially satisfiable: a `Ty` that proves nothing fails it
theorem noTy_fails_lit (env : Environment) : ¬ OblLit (fun _ _ _ _ => False) := fun h => h.1 env [] 0
theorem noTy_fails_bundleS (env : Environment) : ¬ KernelRulesKS (fun _ _ _ _ => False) := fun h => noTy_fails_lit env h.lit
-- (2) the OLD carrier needs a bridge where the new one does not: for a closed entry type, the `bvar` label equals the entry type.
--     old: `bvar_type_closed` takes `OblLiftClosed` (opaque `liftLooseBVars`) as a hypothesis; new: `liftS_closed` needs only `lbr = 0`.
example : (∀ (e : Expr) (s n : Nat), e.looseBVarRange = 0 → e.liftLooseBVars s n = e) → ∀ (en : Entry) (i : Nat), en.τ.looseBVarRange = 0 → en.τ.liftLooseBVars 0 (i + 1) = en.τ :=
  fun hL en i hc => bvar_type_closed hL en hc i
example : ∀ (en : Entry) (i : Nat), lbr en.τ = 0 → liftS en.τ 0 (i + 1) = en.τ := fun en i hc => liftS_closed en.τ hc 0 (i + 1)
-- and by evaluation: the opaque operation is STUCK for the elaborator, the structural one computes
open Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta in
run_cmd liftTermElabM do
  let r ← elabTerm (← `(Expr.const `c [])) none
  let lo ← elabTerm (← `(Expr.instantiate1 (Expr.bvar 0) (Expr.const `c []))) none
  let ls ← elabTerm (← `(substS (Expr.bvar 0) 0 (Expr.const `c []))) none
  let o ← withDefault (isDefEq lo r)
  let n ← withDefault (isDefEq ls r)
  if o then throwError "negative control FAILED: the opaque `instantiate1` unexpectedly reduces"
  unless n do throwError "the structural substS does not compute"
  logInfo m!"opaque Expr.instantiate1: stuck (not defeq to its result); structural substS: computes"
-- (3) the restriction `SafeArg` is needed: `substS` does not commute with `betaS` when the substituted argument is a `lam` ...
theorem substS_betaS_needs_nonlam :
    substS (betaS (.lam `a (.const `T []) (.bvar 0) .default) [.bvar 0, .const `c []]) 0 (.lam `y (.const `T []) (.bvar 0) .default) ≠
    betaS (substS (.lam `a (.const `T []) (.bvar 0) .default) 0 (.lam `y (.const `T []) (.bvar 0) .default))
      ([Expr.bvar 0, .const `c []].map (fun a => substS a 0 (.lam `y (.const `T []) (.bvar 0) .default))) := by
  simp [betaS, substS, liftS]
-- ... nor `instForallS` with `substS` when the substituted argument is a `forallE`
theorem substS_instForallS_needs_nonforall :
    substS (instForallS (.forallE `a (.const `T []) (.bvar 0) .default) [.bvar 0, .const `c []]) 0 (.forallE `y (.const `T []) (.const `c []) .default) ≠
    instForallS (substS (.forallE `a (.const `T []) (.bvar 0) .default) 0 (.forallE `y (.const `T []) (.const `c []) .default))
      ([Expr.bvar 0, .const `c []].map (fun a => substS a 0 (.forallE `y (.const `T []) (.const `c []) .default))) := by
  simp [instForallS, substS, liftS]
-- (4) the structural operations do work
theorem liftS_not_id : liftS (.bvar 0) 0 1 ≠ .bvar 0 := by simp [liftS]
theorem substS_not_id : substS (.bvar 0) 0 (.const `A []) ≠ .bvar 0 := by simp [substS, liftS]
-- (5) `SafeArg` is not vacuous and not trivial
theorem safeArg_bvar : SafeArg (.bvar 3) := ⟨rfl, rfl, by rintro ⟨c, ls, h⟩; simp [Expr.getAppFn] at h⟩
theorem not_safeArg_const : ¬ SafeArg (.const `c []) := fun h => h.2.2 ⟨`c, [], rfl⟩
theorem not_safeArg_lam : ¬ SafeArg (.lam `y (.const `T []) (.bvar 0) .default) := fun h => by simpa [Expr.isLambda] using h.1

/-! ## Remaining named obligations (Prop definitions; none is assumed or proved as stated) and axioms -/
run_meta do
  let env ← getEnv
  let remaining : List Name :=
    [``EnvClosedS, ``OblDenSubstS, ``RowArgsAt, ``OblPrimArgsS]
  let rulesOnly : List Name := [``OblUnfoldS, ``OblPrimKS, ``OblBvarS, ``OblAppS, ``OblLetS, ``KernelRulesKS, ``OblDenTypedS, ``OblDenBvarS, ``WfValS]
  let mut lines : Array MessageData := #[]
  for n in remaining ++ rulesOnly do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n} : {ci.type}"
  logInfo m!"named obligations / judgments ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"

def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
run_meta do
  let proved : List Name :=
    [``tdens_fun, ``argsdens_fun, ``cveks_fun, ``constValueEAtS_functional, ``cvlsks_functional,
     ``liftS_liftS_le, ``liftS_liftS_add, ``liftS_substS, ``liftS_betaS, ``liftS_instForallS, ``getAppFn_liftS,
     ``substS_liftS_in, ``substS_liftS_ge, ``substS_substS, ``substS_betaS, ``substS_instForallS, ``getAppFn_substS,
     ``tdens_wk, ``argsdens_wk, ``cveks_wk, ``tdens_subst, ``argsdens_subst, ``cveks_subst, ``subv_get, ``subv_wk, ``insV_get,
     ``wfValS_nil, ``wfValS_cons, ``oblDenBvarS, ``tden_const_nullary, ``oblDenLits_of_rows, ``oblDenSubstS_safe, ``denTypedS_aux, ``denTypedS,
     ``tyArgsS_instForallS, ``kernelRulesKS_TyRKS, ``tyRKS_sub, ``tyArgsS_sub, ``rowArgsAt_of_none, ``rowArgsAt_nullary, ``cveks_tyRKS, ``cveks_sound,
     ``noTy_fails_bundleS, ``substS_betaS_needs_nonlam, ``substS_instForallS_needs_nonforall, ``safeArg_bvar, ``not_safeArg_const, ``not_safeArg_lam]
  let mut bad : Array Name := #[]
  for n in proved do
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

end Tests.Gen5.SoundSCheck

#print axioms Tools.ShippingGen5ConstValueES.cveks_fun
#print axioms Tools.ShippingGen5ConstValueES.cveks_wk
#print axioms Tools.ShippingGen5ConstValueES.cveks_subst
#print axioms Tools.ShippingGen5ConstValueES.denTypedS
#print axioms Tools.ShippingGen5ConstValueES.cveks_sound
#print axioms Tools.ShippingGen5ConstValueES.oblDenSubstS_safe
