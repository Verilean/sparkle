import Tools.PassPh.Beta
import Tools.PassPh.Rec
import Tools.PassPh.Iota
import Tools.PassPh.BetaAll
import Tools.PassPh.ListLit
set_option autoImplicit false
-- NOT BUILT (SKELETON: sorry あり、探索ブランチのみ。受理の対象ではない). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: Pass group (evalNode?_good, unfoldCall?_good, joint induction on passM/passStep/passSpine, passWith_ph, pass_ph).
Depends on all other groups. Memo invariant `MemoGood`: every (k, v) in the memo with `G k` has `G v`. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

def MemoGood (s : Std.HashMap Lean.Expr Lean.Expr) : Prop :=
  ∀ (k v : Lean.Expr), s.get? k = some v → G k → G v

theorem evalNode?_good (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) :
    ∀ (e r : Lean.Expr), G e → evalNode? natLit? e = ExceptT.mk (some (.ok r)) → G r := by
  sorry

theorem unfoldCall?_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (e r : Lean.Expr), G e → unfoldCall? env natLit? isUser e = ExceptT.mk (some (.ok r)) → G r := by
  sorry

/-- joint induction on `passM` / `passStep` / `passSpine` (measure as in the definitions); the three statements are proved together -/
theorem passM_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), G e → MemoGood s →
      (passM env natLit? isUser fuel e).run.run s = (Except.ok r, s') → G r ∧ MemoGood s' := by
  sorry

theorem passStep_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), G e → MemoGood s →
      (passStep env natLit? isUser fuel e).run.run s = (Except.ok r, s') → G r ∧ MemoGood s' := by
  sorry

theorem passSpine_good (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgrees0) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e h : Lean.Expr) (args : Array Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr),
      G e → MemoGood s →
      (passSpine env natLit? isUser fuel e).run.run s = (Except.ok (h, args), s') →
      (G h ∧ ∀ a ∈ args, G a) ∧ MemoGood s' := by
  sorry

theorem passWith_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgrees0 → BetaNonTargetAgrees →
    ∀ (fuel : Nat) (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.passWith fuel env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  sorry

theorem pass_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgrees0 → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  sorry

theorem passPh' : PassPh' := fun natLit? => pass_ph natLit?

end Tools.PassPh
