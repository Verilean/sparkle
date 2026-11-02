import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tools.ShippingGen5ReaderTraceInst1
import Sparkle.Compiler.MachRecUnfold
set_option autoImplicit false
-- rev2 L version (scripts/gen5/RT_PASS_PH_FREEZE.md rev2). Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of aa24f5ed161ebaf66322fc58f0d153e215e4d94f (Lean content identical; header comment-only). no sorry. Clean build is the coder's. Exploration branch, not an acceptance target.

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
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true

/-- rev2 invariant: no placeholders and loose bvars below `L` -/
def GL (L : Nat) (e : Lean.Expr) : Prop := NoPh e = true ∧ BvarLt L e = true

/-- rev2 memo invariant: each entry preserves `GL L` for every `L` -/
def MemoGoodL (s : Std.HashMap Lean.Expr Lean.Expr) : Prop :=
  ∀ (k v : Lean.Expr), s.get? k = some v → ∀ L, GL L k → GL L v

theorem headBetaAgreesL_zero : HeadBetaAgreesL → HeadBetaAgrees0 := fun h e hn hb => h 0 e hn hb

theorem GL_zero (e : Lean.Expr) : GL 0 e ↔ G e := Iff.rfl

theorem GL_mono {L L' : Nat} {e : Lean.Expr} (hL : L ≤ L') (h : GL L e) : GL L' e := ⟨h.1, bvarLt_mono hL h.2⟩

theorem mkAppN_goodL : ∀ (L : Nat) (f : Lean.Expr) (as : Array Lean.Expr), GL L f → (∀ a ∈ as, GL L a) → GL L (mkAppN f as) := by
  intro L f as hf has
  unfold mkAppN
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Lean.Expr) (f : Lean.Expr), GL L f → (∀ a ∈ l, GL L a) → GL L (l.foldl mkApp f) := by
    intro l
    induction l with
    | nil => intro f hf _; exact hf
    | cons a t ih =>
      intro f hf hl
      refine ih _ ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have ha := hl a List.mem_cons_self
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at hf ha ⊢
      exact ⟨⟨hf.1, ha.1⟩, ⟨hf.2, ha.2⟩⟩
  exact key as.toList f hf (fun a ha => has a (Array.mem_toList_iff.mp ha))

theorem G_iff (e : Lean.Expr) : G e ↔ (NoPh e = true ∧ BvarLt 0 e = true) := Iff.rfl

end Tools.PassPh
