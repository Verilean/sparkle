import Tools.Prototype.PreprocLetOk
import Tools.ShippingLetsExternSpec
import Tools.Prototype.RawNodeRangeLetOk
import Tools.Assume.N3Extern
set_option autoImplicit false
-- NOT BUILT: C1 skeleton (all theorem bodies are `sorry`); scripts/gen3/N3_EXTERN_MIN.md rev2 (bb665fa2) §3.4.2.

/-! # N3 extern agreement premises → range lemmas (skeleton)

The types of `scripts/gen3/N3_EXTERN_MIN.md` §3.4.2 (reviewer-approved design, rev 2).

* The behaviour assumptions `LiftAgrees0` / `LowerAgreesEq` / `ZeroLitAgrees0` and the definitions their statements
  use (`lowerGo` / `lowerSpec` / `zeroLitF`) live in `Tools/Assume/N3Extern.lean`, not here; this file only proves.
* `r1` / `r2` / `r3` (and `lowerGo_ok`, `lowerSpec_ok`): the range statements are PROVED from the equalities.
* `rawNode_ok_of_agrees`: `rawNode_ok` with `LiftLooseRange` / `LowerLooseRange` replaced by `LiftAgrees0` / `LowerAgreesEq`.

Nothing here is a new axiom, law, or TRUSTED boundary. -/

namespace Tools.ShippingN3ExternAgree
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsAliasInv Tools.ShippingLetsReaderInv
open Tools.Prototype.PreprocLetOk Tools.Prototype.RawNodeRangeLetOk
open Tools.Assume.N3Extern
open Sparkle.Compiler.MachRawSurface (rawNode)

/-- Range statements (derived below, NOT assumed). -/
def LiftLooseRange0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars 0 d) = true

def LowerLooseRangeEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars i i) = true

def ZeroLitRange0 : Prop :=
  ∀ (e : Lean.Expr), LetOk 0 e = true →
    LetOk 0 (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true

theorem lowerGo_ok (n : Nat) : ∀ (e : Expr) s d, LetOk n e = true → LetOk n (lowerGo e s d) = true := by
  sorry

theorem lowerSpec_ok (n : Nat) : ∀ (e : Expr) s d, LetOk n e = true → LetOk n (lowerSpec e s d) = true := by
  sorry

theorem r1 (h : LiftAgrees0) : LiftLooseRange0 := by
  sorry

theorem r2 (h : LowerAgreesEq) : LowerLooseRangeEq := by
  sorry

theorem r3 (h : ZeroLitAgrees0) : ZeroLitRange0 := by
  sorry

theorem rawNode_ok_of_agrees (hl : LiftAgrees0) (hlo : LowerAgreesEq) (hb : BetaRange) (pm : Name → Option Nat) :
    ∀ e e', LetOk 0 e = true → rawNode pm e = some e' → LetOk 0 e' = true := by
  sorry

end Tools.ShippingN3ExternAgree
