import Tools.ShippingLegacySemBody

/-! # Handler walks, 1: `handleErrorPatterns`, `handleApplicative`, `handleRegister`

Each legacy handler tests the head's NAME before anything else and returns
`none` when no test matches. For a head that fails every name test the
handler's successful runs return `none` from the same builder state — the
handler facts of `PlainChain` (`Tools/ShippingLegacySemBody.lean`).

The proofs do not enter the arms: after unfolding, the program is a nest of
`if`s (the arms' early `return`s become join points, which `dsimp only`
inlines), each arm's branch carries the hypothesis that its name test holds,
which contradicts the lemma's premise, and the last branch is `pure none`.
The tactic `plain_none` does that: `pure none` → done; a contradictory
context → done; otherwise `split`.

**Expected elaborated shapes** (NOT observed — written from the source; if a
build fails, the goal at the failing line shows the real one):

* `Rec.handleErrorPatterns e name args hint named` — OBSERVED (first build):
  a join point, not a bind of two `if`s:
  `have __do_jp := fun __r => if (name == ``Decidable.rec || name ==
  ``Decidable.casesOn) = true then liftMetaM (throwError …) else pure ();
  if (name == ``ite || name == ``dite) = true then (ppExpr; throwError;
  __do_jp __r) else __do_jp ()`. So: `dsimp only` inlines the join point and
  the same nest-of-`if`s walk applies, with the postcondition `t = s`
  (`plain_frame`).
* `Rec.handleApplicative tr e name args hint named` =
  `if (name == ``Signal.ap) = true then (match apSpine e [] with
     | some (f, signals) => lower … >>= fun w => pure (some w) | none => pure none)
   else pure none` (from `unless … do return none`; the polarity of the `if`
  may be the other one — the tactic does not depend on it).
* `Rec.handleRegister tr e name args hint named` =
  `if (name.toString.endsWith ".register" && decide (args.size ≥ 2)) = true
   then ARM₁ else if (name.toString.endsWith ".registerWithEnable" && …) = true
   then ARM₂ else pure none`.

What is NOT proved: anything when a name test holds. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- Close `Ensures P ctx s (fun r t => r = none ∧ t = s)` for a program that is
a nest of `if`s / `match`es over `pure none`, every other branch of which
contradicts the context. -/
macro "plain_none" : tactic =>
  `(tactic| repeat' (first
      | exact Ensures.pure ⟨rfl, rfl⟩
      | (exfalso; simp_all; done)
      | split))

/-- The same for a program returning `Unit`, with the postcondition "the
builder state is left". -/
macro "plain_frame" : tactic =>
  `(tactic| repeat' (first
      | exact Ensures.pure rfl
      | (exfalso; simp_all; done)
      | split))

/-- **`handleErrorPatterns` on a head that is none of its four names**: the
builder state is left. -/
theorem handleErrorPatterns_frame {e : Lean.Expr} {name : Name} {args : Array Lean.Expr}
    {hint : String} {named : Bool} {ctx : CompilerState} {s : CircuitState}
    (h1 : (name == ``ite) = false) (h2 : (name == ``dite) = false)
    (h3 : (name == ``Decidable.rec) = false) (h4 : (name == ``Decidable.casesOn) = false) :
    Ensures (Rec.handleErrorPatterns e name args hint named) ctx s (fun _ t => t = s) := by
  unfold Rec.handleErrorPatterns
  try dsimp only
  plain_frame

/-- **`handleApplicative` on a head that is not `Signal.ap`.** -/
theorem handleApplicative_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (hap : (name == ``Sparkle.Core.Signal.Signal.ap) = false) :
    Ensures (Rec.handleApplicative tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleApplicative
  try dsimp only
  plain_none

/-- **`handleRegister` on a head whose name ends in neither `.register` nor
`.registerWithEnable`.** -/
theorem handleRegister_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (hreg : name.toString.endsWith ".register" = false)
    (hregE : name.toString.endsWith ".registerWithEnable" = false) :
    Ensures (Rec.handleRegister tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleRegister
  try dsimp only
  plain_none

end Tools.ShippingLegacySem
