import Tools.PassPh.Beta
import Tools.PassPh.Rec
set_option autoImplicit false
-- NOT BUILT (SKELETON: sorry あり、探索ブランチのみ。受理の対象ではない). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: Iota group (iota_good, reduceMatcher?_good, reduceHead_good). Depends on Beta + Rec. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

theorem iota_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr), G e → iota env natLit? fuel e = ExceptT.mk (some (.ok r)) → G r := by
  sorry

theorem reduceMatcher?_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (e r : Lean.Expr), G e → reduceMatcher? env natLit? e = ExceptT.mk (some (.ok r)) → G r := by
  sorry

theorem reduceHead_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr), G e → reduceHead env natLit? fuel e = ExceptT.mk (some (.ok r)) → G r := by
  sorry

end Tools.PassPh
