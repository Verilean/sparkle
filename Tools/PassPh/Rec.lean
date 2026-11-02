import Tools.PassPh.Defs
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
  sorry

theorem ilp_ph : ReplaceAgrees →
    ∀ (ps : List Lean.Name) (ls : List Lean.Level) (e : Lean.Expr), G e → G (e.instantiateLevelParams ps ls) := by
  sorry

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
  sorry

end Tools.PassPh
