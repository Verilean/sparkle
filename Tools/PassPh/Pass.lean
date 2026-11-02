import Tools.PassPh.Beta
import Tools.PassPh.Rec
import Tools.PassPh.Iota
import Tools.PassPh.BetaAll
import Tools.PassPh.ListLit
set_option autoImplicit false
-- SKELETON (rev2 L version): sorry あり、探索ブランチのみ（受理の対象ではない）. Not built yet. Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev2.

/-! # pass_ph skeleton: Pass group (evalNode?_good, unfoldCall?_good, joint induction on passM/passStep/passSpine, passWith_ph, pass_ph).
Depends on all other groups. Memo invariant `MemoGoodL` (Defs): every (k, v) in the memo has `∀ L, GL L k → GL L v`. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

theorem evalNode?_goodL (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → evalNode? natLit? e = ExceptT.mk (some (.ok r)) → GL L r := by
  sorry

theorem unfoldCall?_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → unfoldCall? env natLit? isUser e = ExceptT.mk (some (.ok r)) → GL L r := by
  sorry

/-- joint induction on `passM` / `passStep` / `passSpine` (measure as in the definitions); the three statements are proved together -/
theorem passM_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passM env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r := by
  sorry

theorem passStep_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passStep env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r := by
  sorry

theorem passSpine_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e h : Lean.Expr) (args : Array Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr),
      MemoGoodL s → (passSpine env natLit? isUser fuel e).run.run s = (Except.ok (h, args), s') →
      MemoGoodL s' ∧ ∀ L, GL L e → GL L h ∧ ∀ a ∈ args, GL L a := by
  sorry

theorem passWith_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (fuel : Nat) (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.passWith fuel env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  sorry

theorem pass_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  sorry

theorem passPh' : PassPh' := fun natLit? => pass_ph natLit?

end Tools.PassPh
