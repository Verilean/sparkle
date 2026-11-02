import Tools.PassPh.Defs
set_option autoImplicit false
-- SKELETON: sorry あり、探索ブランチのみ（受理の対象ではない）. Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of dec1b348 (Lean content identical; header comment-only). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: Beta group (freeze §5: beta_target, beta_good, headBetaM_good). Depends on Defs only. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern

theorem arr_push_ind {α : Type} {motive : Array α → Prop} (h0 : motive #[])
    (hs : ∀ (as : Array α) (a : α), motive as → motive (as.push a)) : ∀ as, motive as := by
  intro as
  obtain ⟨l⟩ := as
  suffices ∀ (n : Nat) (l : List α), l.length = n → motive ⟨l⟩ from this _ l rfl
  intro n
  induction n with
  | zero => intro l hl; rw [List.length_eq_zero_iff.mp hl]; exact h0
  | succ n ih =>
    intro l hl
    obtain ⟨l', a, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left (by rintro rfl; simp at hl)
    have := hs ⟨l'⟩ a (ih l' (by simpa using hl))
    simpa using this

theorem mkAppN_push (f a : Lean.Expr) (args : Array Lean.Expr) : mkAppN f (args.push a) = .app (mkAppN f args) a := by
  simp [mkAppN]; rfl

theorem getAppFn_mkAppN (f : Lean.Expr) (hf : ¬f.isApp = true) (args : Array Lean.Expr) : (mkAppN f args).getAppFn = f := by
  induction args using arr_push_ind with
  | h0 => cases f <;> simp_all [mkAppN, Lean.Expr.getAppFn, Lean.Expr.isApp]
  | hs as a ih => rw [mkAppN_push]; simpa [Lean.Expr.getAppFn] using ih

theorem revArgsAux_mkAppN (f : Lean.Expr) (hf : ¬f.isApp = true) (args : Array Lean.Expr) :
    ∀ (as : Array Lean.Expr), (priv% Lean.Expr.getAppRevArgsAux) (mkAppN f args) as = as ++ args.reverse := by
  induction args using arr_push_ind with
  | h0 =>
    intro as
    cases f <;> simp_all [mkAppN, Lean.Expr.isApp] <;> (unfold_priv Lean.Expr.getAppRevArgsAux; simp)
  | hs bs a ih =>
    intro as
    rw [mkAppN_push]
    show (priv% Lean.Expr.getAppRevArgsAux) (mkAppN f bs) (as.push a) = _
    rw [ih]
    simp [Array.reverse_push]

theorem beta_target : ∀ (f : Lean.Expr) (args : Array Lean.Expr),
    f.isHeadBetaTargetFn false = true → ¬f.isApp = true → f.beta args = (mkAppN f args).headBeta := by
  intro f args ht hf
  have h1 := getAppFn_mkAppN f hf args
  have h2 : (mkAppN f args).getAppRevArgs = args.reverse := by
    unfold Lean.Expr.getAppRevArgs
    rw [revArgsAux_mkAppN f hf args]
    simp
  unfold Lean.Expr.headBeta Lean.Expr.beta
  rw [h1, h2, if_pos ht]

theorem mkAppN_good (f : Lean.Expr) (args : Array Lean.Expr) (hf : G f) (ha : ∀ a ∈ args, G a) : G (mkAppN f args) := by
  induction args using arr_push_ind with
  | h0 => simpa [mkAppN] using hf
  | hs as a ih =>
    rw [mkAppN_push]
    have h1 := ih (fun x hx => ha x (Array.mem_push.mpr (Or.inl hx)))
    have h2 := ha a (Array.mem_push.mpr (Or.inr rfl))
    simp only [G, NoPh, BvarLt, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

theorem isHeadBetaTargetFn_not_app : ∀ (f : Lean.Expr), f.isHeadBetaTargetFn false = true → ¬f.isApp = true := by
  intro f
  induction f with
  | mdata _ x ih =>
    intro h
    have := ih (by simpa [Lean.Expr.isHeadBetaTargetFn] using h)
    simpa [Lean.Expr.isApp] using this
  | app _ _ _ _ => intro h; simp [Lean.Expr.isHeadBetaTargetFn] at h
  | _ => intro _; simp [Lean.Expr.isApp]

theorem beta_good (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (f : Lean.Expr) (args : Array Lean.Expr), G f → (∀ a ∈ args, G a) → G (f.beta args) := by
  intro f args hf ha
  cases ht : f.isHeadBetaTargetFn false
  · rw [hbt f args ht]; exact mkAppN_good f args hf ha
  · rw [beta_target f args ht (isHeadBetaTargetFn_not_app f ht)]
    have := mkAppN_good f args hf ha
    exact Tools.ShippingGen5ReaderTraceAbbrevS1.headBeta_good hh _ this.1 this.2

theorem consumeMData_good : ∀ (e : Lean.Expr), G e → G e.consumeMData := by
  intro e
  induction e with
  | mdata _ x ih => intro h; exact ih (by simpa [G, NoPh, BvarLt] using h)
  | _ => intro h; exact h

theorem getAppFn_G : ∀ (e : Lean.Expr), G e → G e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [G, NoPh, BvarLt, Bool.and_eq_true] at h
    exact ihf ⟨h.1.1, h.2.1⟩
  | _ => intro h; exact h

theorem argsAux_G : ∀ (e : Lean.Expr) (as : Array Lean.Expr) (i : Nat), G e → (∀ a ∈ as, G a) →
    ∀ a ∈ (priv% Lean.Expr.getAppArgsAux) e as i, G a := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro as i h hs
    simp only [G, NoPh, BvarLt, Bool.and_eq_true] at h
    show ∀ a ∈ (priv% Lean.Expr.getAppArgsAux) f (as.set! i x) (i - 1), G a
    refine ihf (as.set! i x) (i - 1) ⟨h.1.1, h.2.1⟩ ?_
    intro a ha
    rcases Array.mem_or_eq_of_mem_setIfInBounds ha with h' | h'
    · exact hs a h'
    · subst h'; exact ⟨h.1.2, h.2.2⟩
  | _ => intro as i _ hs; exact hs

theorem getAppArgs_G (e : Lean.Expr) (h : G e) : ∀ a ∈ e.getAppArgs, G a := by
  refine argsAux_G e _ _ h ?_
  intro a ha
  obtain ⟨_, _, rfl⟩ := Array.mem_replicate.mp ha
  exact ⟨rfl, rfl⟩

theorem headBetaM_good (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr), G e → Sparkle.Compiler.MachRecUnfold.headBetaM fuel e = .ok r → G r := by
  intro fuel
  induction fuel with
  | zero =>
    intro e r he h
    unfold Sparkle.Compiler.MachRecUnfold.headBetaM at h
    dsimp only at h
    by_cases c : (e.consumeMData.getAppFn.consumeMData.isLambda && decide (e.consumeMData.getAppNumArgs > 0)) = true
    · rw [if_pos c] at h; cases h
    · rw [if_neg c] at h; cases h; exact consumeMData_good e he
  | succ n ih =>
    intro e r he h
    unfold Sparkle.Compiler.MachRecUnfold.headBetaM at h
    dsimp only at h
    by_cases c : (e.consumeMData.getAppFn.consumeMData.isLambda && decide (e.consumeMData.getAppNumArgs > 0)) = true
    · rw [if_pos c] at h
      have he' := consumeMData_good e he
      have hf := consumeMData_good _ (getAppFn_G _ he')
      exact ih _ r (beta_good hh hbt _ _ hf (getAppArgs_G _ he')) h
    · rw [if_neg c] at h; cases h; exact consumeMData_good e he

end Tools.PassPh
