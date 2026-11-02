import Tools.PassPh.Beta
set_option autoImplicit false
-- SKELETON (rev2 L version): sorry あり、探索ブランチのみ（受理の対象ではない）. Not built yet. Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev2.

/-! # pass_ph skeleton: BetaAll group (mutual betaAll / betaSpine, measure (fuel, sizeOf, k)). Depends on Beta. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

theorem betaAll_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → betaAll fuel e = .ok r → GL L r := by
  sorry

theorem betaSpine_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e h : Lean.Expr) (args : Array Lean.Expr), GL L e → betaSpine fuel e = .ok (h, args) →
      GL L h ∧ ∀ a ∈ args, GL L a := by
  sorry

end Tools.PassPh
