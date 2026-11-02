import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tools.ShippingGen5ReaderTraceInst1
import Sparkle.Compiler.MachRecUnfold
set_option autoImplicit false
-- SKELETON: sorry あり、探索ブランチのみ（受理の対象ではない）. Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of dec1b348 (Lean content identical; header comment-only). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: common definitions (freeze §1)
`RecRulePhU` is a hypothesis definition only (not registered). `BetaNonTargetAgrees` is an UNPROVEN T1 +1 candidate (not accepted, not counted). -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern

/-- the invariant carried by the pass -/
def G (e : Lean.Expr) : Prop := NoPh e = true ∧ BvarLt 0 e = true

/-- (hypothesis only; approved freeze RT_RECRULE_FREEZE §1.2, bab003d9) -/
def RecRulePhU (env : Lean.Environment) : Prop :=
  ∀ (p : Lean.Name) (rv : Lean.RecursorVal) (c : Lean.Name) (r : Lean.RecursorRule),
    env.find? (.str p "rec") = some (.recInfo rv) → rv.rules.find? (·.ctor == c) = some r →
    NoPh r.rhs = true ∧ BvarLt 0 r.rhs = true

/-- (NEW T1 candidate, unproven) `Expr.beta` agrees with `mkAppN` on heads that are not `headBeta` targets -/
def BetaNonTargetAgrees : Prop :=
  ∀ (f : Lean.Expr) (args : Array Lean.Expr), f.isHeadBetaTargetFn false = false → f.beta args = mkAppN f args

/-- the statement of `pass_ph` (freeze §1), as a Prop -/
def PassPh' : Prop :=
  ∀ (natLit? : Lean.Expr → Option Nat),
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgrees0 → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true

theorem G_iff (e : Lean.Expr) : G e ↔ (NoPh e = true ∧ BvarLt 0 e = true) := Iff.rfl

end Tools.PassPh
