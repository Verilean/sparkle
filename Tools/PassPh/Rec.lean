import Tools.PassPh.Defs
set_option autoImplicit false
-- NOT BUILT (SKELETON: sorry あり、探索ブランチのみ。受理の対象ではない). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: Rec group (freeze §5; types from RT_RECRULE_FREEZE §3 scratch output). Depends on Defs only. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern

theorem mkAppN_good : ∀ (f : Lean.Expr) (as : Array Lean.Expr), G f → (∀ a ∈ as, G a) → G (mkAppN f as) := by
  sorry

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
