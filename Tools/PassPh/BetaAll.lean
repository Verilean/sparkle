import Tools.PassPh.Beta
set_option autoImplicit false
-- freeze rev2 + rev3 (scripts/gen5/RT_PASS_PH_FREEZE.md). Built in Pod (kjob lake build Tools.PassPh.Pass Tests.Gen5.PassPhCheck Tools.ShippingGen5ReaderTraceAbbrevS1 Tests.Gen5.ReaderTraceAbbrevS1Check, exit 0) on the tree of 18fa57ac6bdb999e9ac4747bbe7ad43143004dfd (Lean content identical; header comment-only). No sorry / axiom / native_decide in source (all of Tools/PassPh/*.lean). Conditional on BetaNonTargetAgrees, ExprEqvLaws (T1 +1 candidates), HeadBetaAgreesL (replaces T1L-74), RecRulePhU (hypothesis definition); none accepted. Clean build is the coder's.

/-! # pass_ph skeleton: BetaAll group (mutual betaAll / betaSpine, measure (fuel, sizeOf, k)). Depends on Beta. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

theorem gl_app_split {L : Nat} {f a : Lean.Expr} (h : GL L (.app f a)) : GL L f ∧ GL L a := by
  simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at h
  exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

theorem gl_app_mk {L : Nat} {f a : Lean.Expr} (hf : GL L f) (ha : GL L a) : GL L (.app f a) := by
  simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at hf ha ⊢
  exact ⟨⟨hf.1, ha.1⟩, ⟨hf.2, ha.2⟩⟩

theorem betaAll_spine_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat), (∀ f, f < fuel → ∀ (L : Nat) (e r : Lean.Expr), GL L e → betaAll f e = .ok r → GL L r) →
    ∀ (e : Lean.Expr),
      (∀ (L : Nat) (r : Lean.Expr), GL L e → betaAll fuel e = .ok r → GL L r) ∧
      (∀ (L : Nat) (h : Lean.Expr) (args : Array Lean.Expr), GL L e → betaSpine fuel e = .ok (h, args) →
        GL L h ∧ ∀ a ∈ args, GL L a) := by
  intro fuel ihf e
  induction e with
  | app f a ihf' iha =>
    have hA : ∀ (L : Nat) (r : Lean.Expr), GL L (.app f a) → betaAll fuel (.app f a) = .ok r → GL L r := by
      intro L r he h
      obtain ⟨hf, ha⟩ := gl_app_split he
      rw [betaAll] at h
      cases hs : betaSpine fuel f with
      | error m => simp [hs, bind, Except.bind] at h
      | ok p =>
        obtain ⟨hd, args⟩ := p
        obtain ⟨hhd, hargs⟩ := ihf'.2 L hd args hf hs
        cases ha' : betaAll fuel a with
        | error m => simp [hs, ha', bind, Except.bind] at h
        | ok a' =>
          have hga' := iha.1 L a' ha ha'
          have he' : GL L (mkAppN hd (args.push a')) := by
            refine mkAppN_goodL L _ _ hhd ?_
            intro x hx
            rcases Array.mem_push.mp hx with h | h
            · exact hargs x h
            · subst h; exact hga'
          simp only [hs, ha', bind, Except.bind, pure, Except.pure] at h
          split at h
          · cases fuel with
            | zero => cases h
            | succ n =>
              cases hb : Sparkle.Compiler.MachRecUnfold.headBetaM headBetaLimit (mkAppN hd (args.push a')) with
              | error m => simp [hb] at h
              | ok e'' =>
                simp only [hb] at h
                exact ihf n (Nat.lt_succ_self n) L e'' r (headBetaM_goodL hh hbt _ L _ _ he' hb) h
          · injection h with h; subst h; exact he'
    refine ⟨hA, ?_⟩
    intro L h args he hsp
    obtain ⟨hf, ha⟩ := gl_app_split he
    rw [betaSpine] at hsp
    cases hs : betaSpine fuel f with
    | error m => simp [hs, bind, Except.bind] at hsp
    | ok p =>
      obtain ⟨hd, args0⟩ := p
      obtain ⟨hhd, hargs⟩ := ihf'.2 L hd args0 hf hs
      cases ha' : betaAll fuel a with
      | error m => simp [hs, ha', bind, Except.bind] at hsp
      | ok a' =>
        have hga' := iha.1 L a' ha ha'
        simp only [hs, ha', bind, Except.bind, pure, Except.pure] at hsp
        injection hsp with hsp
        injection hsp with h1 h2
        subst h1; subst h2
        refine ⟨hhd, ?_⟩
        intro x hx
        rcases Array.mem_push.mp hx with h | h
        · exact hargs x h
        · subst h; exact hga'
  | lam n t b bi iht ihb =>
    have hA : ∀ (L : Nat) (r : Lean.Expr), GL L (.lam n t b bi) → betaAll fuel (.lam n t b bi) = .ok r → GL L r := by
      intro L r he h
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at he
      rw [betaAll] at h
      cases hb : betaAll fuel b with
      | error m => simp [hb, bind, Except.bind] at h
      | ok b' =>
        have := ihb.1 (L + 1) b' ⟨he.1.2, he.2.2⟩ hb
        simp only [hb, bind, Except.bind, pure, Except.pure] at h
        injection h with h; subst h
        simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at this ⊢
        exact ⟨⟨he.1.1, this.1⟩, ⟨he.2.1, this.2⟩⟩
    refine ⟨hA, ?_⟩
    intro L h args he hsp
    rw [betaSpine] at hsp
    cases hb : betaAll fuel (.lam n t b bi) with
    | error m => simp [hb, bind, Except.bind] at hsp
    | ok r =>
      simp only [hb, bind, Except.bind, pure, Except.pure] at hsp
      injection hsp with hsp
      injection hsp with h1 h2
      subst h1; subst h2
      exact ⟨hA L r he hb, by intro x hx; simp at hx⟩
    · intro f a h; cases h
  | letE n t v b nd iht ihv ihb =>
    have hA : ∀ (L : Nat) (r : Lean.Expr), GL L (.letE n t v b nd) → betaAll fuel (.letE n t v b nd) = .ok r → GL L r := by
      intro L r he h
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at he
      rw [betaAll] at h
      cases hv : betaAll fuel v with
      | error m => simp [hv, bind, Except.bind] at h
      | ok v' =>
        cases hb : betaAll fuel b with
        | error m => simp [hv, hb, bind, Except.bind] at h
        | ok b' =>
          have h1 := ihv.1 L v' ⟨he.1.1.2, he.2.1.2⟩ hv
          have h2 := ihb.1 (L + 1) b' ⟨he.1.2, he.2.2⟩ hb
          simp only [hv, hb, bind, Except.bind, pure, Except.pure] at h
          injection h with h; subst h
          simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at h1 h2 ⊢
          exact ⟨⟨⟨he.1.1.1, h1.1⟩, h2.1⟩, ⟨⟨he.2.1.1, h1.2⟩, h2.2⟩⟩
    refine ⟨hA, ?_⟩
    intro L h args he hsp
    rw [betaSpine] at hsp
    cases hb : betaAll fuel (.letE n t v b nd) with
    | error m => simp [hb, bind, Except.bind] at hsp
    | ok r =>
      simp only [hb, bind, Except.bind, pure, Except.pure] at hsp
      injection hsp with hsp
      injection hsp with h1 h2
      subst h1; subst h2
      exact ⟨hA L r he hb, by intro x hx; simp at hx⟩
    · intro f a h; cases h
  | mdata m b ihb =>
    have hA : ∀ (L : Nat) (r : Lean.Expr), GL L (.mdata m b) → betaAll fuel (.mdata m b) = .ok r → GL L r := by
      intro L r he h
      simp only [GL, NoPh, BvarLt] at he
      rw [betaAll] at h
      cases hb : betaAll fuel b with
      | error m => simp [hb, bind, Except.bind] at h
      | ok b' =>
        have := ihb.1 L b' he hb
        simp only [hb, bind, Except.bind, pure, Except.pure] at h
        injection h with h; subst h
        exact this
    refine ⟨hA, ?_⟩
    intro L h args he hsp
    rw [betaSpine] at hsp
    cases hb : betaAll fuel (.mdata m b) with
    | error m => simp [hb, bind, Except.bind] at hsp
    | ok r =>
      simp only [hb, bind, Except.bind, pure, Except.pure] at hsp
      injection hsp with hsp
      injection hsp with h1 h2
      subst h1; subst h2
      exact ⟨hA L r he hb, by intro x hx; simp at hx⟩
    · intro f a h; cases h
  | _ =>
    all_goals
      refine ⟨?_, ?_⟩
      · intro L r he h
        simp [betaAll, pure, Except.pure] at h
        subst h; exact he
      · intro L h args he hsp
        simp [betaSpine, betaAll, bind, Except.bind, pure, Except.pure] at hsp
        obtain ⟨h1, h2⟩ := hsp
        subst h1; subst h2
        exact ⟨he, by intro x hx; simp at hx⟩

theorem betaAll_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → betaAll fuel e = .ok r → GL L r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro L e r he h
    exact (betaAll_spine_goodL hh hbt fuel (fun f hf L e r => ih f hf L e r) e).1 L r he h

theorem betaSpine_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e h : Lean.Expr) (args : Array Lean.Expr), GL L e → betaSpine fuel e = .ok (h, args) →
      GL L h ∧ ∀ a ∈ args, GL L a := by
  intro fuel L e h args he hs
  exact (betaAll_spine_goodL hh hbt fuel (fun f _ L e r => betaAll_goodL hh hbt f L e r) e).2 L h args he hs

end Tools.PassPh
