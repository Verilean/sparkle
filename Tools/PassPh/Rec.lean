import Tools.PassPh.Defs
import Tools.ShippingGen5ReaderTraceReg
set_option autoImplicit false
-- SKELETON: sorry あり、探索ブランチのみ（受理の対象ではない）. Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of dec1b348 (Lean content identical; header comment-only). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: Rec group (freeze §5; types from RT_RECRULE_FREEZE §3 scratch output). Depends on Defs only. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern

theorem mkAppN_good : ∀ (f : Lean.Expr) (as : Array Lean.Expr), G f → (∀ a ∈ as, G a) → G (mkAppN f as) := by
  intro f as hf has
  unfold mkAppN
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Lean.Expr) (f : Lean.Expr), G f → (∀ a ∈ l, G a) → G (l.foldl mkApp f) := by
    intro l
    induction l with
    | nil => intro f hf _; exact hf
    | cons a t ih =>
      intro f hf hl
      refine ih _ ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have ha := hl a List.mem_cons_self
      simp only [G, NoPh, BvarLt, Bool.and_eq_true] at hf ha ⊢
      exact ⟨⟨hf.1, ha.1⟩, ⟨hf.2, ha.2⟩⟩
  exact key as.toList f hf (fun a ha => has a (Array.mem_toList_iff.mp ha))

theorem rnc_ph2 : ∀ (f : Lean.Expr → Option Lean.Expr),
    (∀ (x v : Lean.Expr), f x = some v → ∀ (L : Nat), NoPh x = true → BvarLt L x = true → NoPh v = true ∧ BvarLt L v = true) →
    ∀ (e : Lean.Expr) (L : Nat), NoPh e = true → BvarLt L e = true →
      NoPh (Lean.Expr.replaceNoCache f e) = true ∧ BvarLt L (Lean.Expr.replaceNoCache f e) = true := by
  intro f hf e
  have leaf : ∀ (e : Lean.Expr), Lean.Expr.replaceNoCache f e = (match f e with | some v => v | none => e) →
      ∀ L, NoPh e = true → BvarLt L e = true →
        NoPh (Lean.Expr.replaceNoCache f e) = true ∧ BvarLt L (Lean.Expr.replaceNoCache f e) = true := by
    intro e hr L hn hb
    rw [hr]
    rcases hfx : f e with _ | v
    · exact ⟨hn, hb⟩
    · exact hf _ v hfx L hn hb
  induction e with
  | app a b iha ihb =>
    intro L hn hb
    have hn0 := hn; have hb0 := hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [Tools.ShippingGen5ReaderTraceAbbrevS1.rnc_app]
    rcases hfx : f (.app a b) with _ | v
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iha L hn.1 hb.1; have h2 := ihb L hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · exact hf _ v hfx L hn0 hb0
  | lam n t b bi iht ihb =>
    intro L hn hb
    have hn0 := hn; have hb0 := hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [Tools.ShippingGen5ReaderTraceAbbrevS1.rnc_lam]
    rcases hfx : f (.lam n t b bi) with _ | v
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iht L hn.1 hb.1; have h2 := ihb (L + 1) hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · exact hf _ v hfx L hn0 hb0
  | forallE n t b bi iht ihb =>
    intro L hn hb
    have hn0 := hn; have hb0 := hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [Tools.ShippingGen5ReaderTraceAbbrevS1.rnc_forallE]
    rcases hfx : f (.forallE n t b bi) with _ | v
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iht L hn.1 hb.1; have h2 := ihb (L + 1) hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · exact hf _ v hfx L hn0 hb0
  | letE n t v b nd iht ihv ihb =>
    intro L hn hb
    have hn0 := hn; have hb0 := hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [Tools.ShippingGen5ReaderTraceAbbrevS1.rnc_letE]
    rcases hfx : f (.letE n t v b nd) with _ | w
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iht L hn.1.1 hb.1.1; have h2 := ihv L hn.1.2 hb.1.2; have h3 := ihb (L + 1) hn.2 hb.2
      exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨⟨h1.2, h2.2⟩, h3.2⟩⟩
    · exact hf _ w hfx L hn0 hb0
  | mdata m b ih =>
    intro L hn hb
    have hn0 := hn; have hb0 := hb
    simp only [NoPh, BvarLt] at hn hb
    rw [Tools.ShippingGen5ReaderTraceAbbrevS1.rnc_mdata]
    rcases hfx : f (.mdata m b) with _ | v
    · simp only [NoPh, BvarLt]; exact ih L hn hb
    · exact hf _ v hfx L hn0 hb0
  | proj n i b ih =>
    intro L hn hb
    have hn0 := hn; have hb0 := hb
    simp only [NoPh, BvarLt] at hn hb
    rw [Tools.ShippingGen5ReaderTraceAbbrevS1.rnc_proj]
    rcases hfx : f (.proj n i b) with _ | v
    · simp only [NoPh, BvarLt]; exact ih L hn hb
    · exact hf _ v hfx L hn0 hb0
  | bvar _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | fvar _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | mvar _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | sort _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | const _ _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | lit _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb

open Lean.Elab Lean.Elab.Tactic Lean.Meta in
/-- delta-expand the private declaration `n` in the goal (for a private `where` helper whose equation lemmas `unfold_priv` cannot use) -/
elab "delta_priv " n:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Core.betaReduce (← deltaExpand t (fun c => Lean.privateToUserName? c == some n.getId))
  if t' == t then throwError "delta_priv: no progress"
  replaceMainGoal [← g.replaceTargetDefEq t']

theorem ilp_ph : ReplaceAgrees →
    ∀ (ps : List Lean.Name) (ls : List Lean.Level) (e : Lean.Expr), G e → G (e.instantiateLevelParams ps ls) := by
  intro hr ps ls e he
  unfold Lean.Expr.instantiateLevelParams
  split
  · exact he
  · unfold Lean.Expr.instantiateLevelParamsCore
    rw [hr]
    refine rnc_ph2 _ ?_ e 0 he.1 he.2
    delta_priv Lean.Expr.instantiateLevelParamsCore.replaceFn
    intro x v hx L hn hb
    split at hx
    · cases hx; exact ⟨hn, hb⟩
    · cases x <;> simp_all [Lean.Expr.updateConst!, Lean.Expr.updateSort!, NoPh, BvarLt] <;> (subst hx; exact ⟨rfl, rfl⟩)

theorem rec_arm_goodU : ReplaceAgrees →
    ∀ (env : Lean.Environment), RecRulePhU env →
    ∀ (p : Lean.Name) (rv : Lean.RecursorVal), env.find? (p.str "rec") = some (Lean.ConstantInfo.recInfo rv) →
    ∀ (c : Lean.Name) (rule : Lean.RecursorRule), rv.rules.find? (fun x => x.ctor == c) = some rule →
    ∀ (ls : List Lean.Level) (pre fields rest : Array Lean.Expr),
      (∀ a ∈ pre, G a) → (∀ a ∈ fields, G a) → (∀ a ∈ rest, G a) →
      G (mkAppN (mkAppN (mkAppN (rule.rhs.instantiateLevelParams rv.levelParams ls) pre) fields) rest) := by
  sorry

theorem ctorApp_good : ∀ (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (e : Lean.Expr)
    (cv : Lean.ConstructorVal) (fs : Array Lean.Expr), G e →
    Sparkle.Compiler.MachRecUnfold.ctorApp? env natLit? e = some (cv, fs) → ∀ f ∈ fs, G f := by
  intro env natLit? e cv fs he h f hf
  have hcm : ∀ (x : Lean.Expr), G x → G x.consumeMData := by
    intro x
    induction x with
    | mdata m b ih => intro hx; simp only [G, NoPh, BvarLt] at hx; rw [Lean.Expr.consumeMData]; exact ih hx
    | _ => intro hx; exact hx
  have hg := hcm e he
  unfold Sparkle.Compiler.MachRecUnfold.ctorApp? at h
  dsimp only at h
  generalize e.consumeMData = e' at hg h
  have hlit : ∀ n, G (Sparkle.Compiler.MachRecUnfold.natLitE n) := by
    intro n
    simp [G, Sparkle.Compiler.MachRecUnfold.natLitE, Lean.mkApp3, Lean.mkApp, NoPh, BvarLt]
  split at h
  · rename_i c fields hc
    unfold Sparkle.Compiler.MachRecUnfold.natCtor? at hc
    split at hc <;> try (split at hc)
    all_goals first | contradiction | skip
    all_goals
      split at h
      all_goals first | contradiction | skip
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at h hc
      obtain ⟨_, rfl⟩ := h
      obtain ⟨_, rfl⟩ := hc
      first
        | (simp at hf; subst hf; exact hlit _)
        | simp at hf
  · split at h
    · split at h
      · split at h
        · have := phArgs_getAppArgs hg.1 hg.2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          obtain ⟨i, hi, rfl⟩ := Array.mem_extract_iff_getElem.mp hf
          exact this _ (Array.getElem_mem _)
        · contradiction
      · contradiction
    · contradiction

end Tools.PassPh
