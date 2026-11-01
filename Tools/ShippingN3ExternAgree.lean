import Tools.Prototype.PreprocLetOk
import Tools.ShippingLetsExternSpec
import Tools.Prototype.RawNodeRangeLetOk
set_option autoImplicit false
-- NOT BUILT: C1 skeleton (all theorem bodies are `sorry`); scripts/gen3/N3_EXTERN_MIN.md rev2 (bb665fa2) §3.4.2.

/-! # N3 extern agreement premises → range lemmas (skeleton)

The types of `scripts/gen3/N3_EXTERN_MIN.md` §3.4.2 (reviewer-approved design, rev 2).

* `LiftAgrees0` / `LowerAgreesEq` / `ZeroLitAgrees0`: the behaviour premises (Prop definitions, NOT axioms) on `LetOk 0` inputs.
* `lowerGo` / `lowerSpec`: new definitions (a model of `Expr.lowerLooseBVars`, not a trust statement).
* `r1` / `r2` / `r3` (and `lowerGo_ok`, `lowerSpec_ok`): the range statements are PROVED from the equalities.
* `rawNode_ok_of_agrees`: `rawNode_ok` with `LiftLooseRange` / `LowerLooseRange` replaced by `LiftAgrees0` / `LowerAgreesEq`.

Nothing here is a new axiom, law, or TRUSTED boundary. -/

namespace Tools.ShippingN3ExternAgree
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsAliasInv Tools.ShippingLetsReaderInv
open Tools.Prototype.PreprocLetOk Tools.Prototype.RawNodeRangeLetOk
open Sparkle.Compiler.MachRawSurface (rawNode)

/-- The `Expr.replace` function of `zeroLit` (the text of `ZeroLitAgrees`' right-hand side). -/
def zeroLitF (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | .app (.const ``BitVec.zero _) w =>
    (canonicalNatLitValue? w).map fun n => mkApp2 (.const ``BitVec.ofNat []) (inlNatLit n) (inlNatLit 0)
  | _ => none

/-- Model of `Expr.lowerLooseBVars e s d`: loose bound variables `≥ s` are lowered by `d`. -/
def lowerGo : Expr → Nat → Nat → Expr
  | .bvar i, s, d => if i < s then .bvar i else .bvar (i - d)
  | .app f a, s, d => .app (lowerGo f s d) (lowerGo a s d)
  | .lam n t b bi, s, d => .lam n (lowerGo t s d) (lowerGo b (s + 1) d) bi
  | .forallE n t b bi, s, d => .forallE n (lowerGo t s d) (lowerGo b (s + 1) d) bi
  | .letE n t v b nd, s, d => .letE n (lowerGo t s d) (lowerGo v s d) (lowerGo b (s + 1) d) nd
  | .mdata m e, s, d => .mdata m (lowerGo e s d)
  | .proj n i e, s, d => .proj n i (lowerGo e s d)
  | e, _, _ => e

/-- `lowerLooseBVars` model; the `s < d` branch is the C++ `if (s < d) return e`. -/
def lowerSpec (e : Expr) (s d : Nat) : Expr := if s < d then e else lowerGo e s d

/-- Range statements (derived below, NOT assumed). -/
def LiftLooseRange0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars 0 d) = true

def LowerLooseRangeEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars i i) = true

def ZeroLitRange0 : Prop :=
  ∀ (e : Lean.Expr), LetOk 0 e = true →
    LetOk 0 (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true

/-- PREMISE (OPEN; C++ extern): `liftLooseBVars` at `s = 0` on `LetOk 0` inputs agrees with `liftSpec`. -/
def LiftAgrees0 : Prop :=
  ∀ (e : Expr) (d : Nat), LetOk 0 e = true → e.liftLooseBVars 0 d = liftSpec e 0 d

/-- PREMISE (OPEN; C++ extern): `lowerLooseBVars i i` on `LetOk 0` inputs agrees with `lowerSpec`. -/
def LowerAgreesEq : Prop :=
  ∀ (e : Expr) (i : Nat), LetOk 0 e = true → e.lowerLooseBVars i i = lowerSpec e i i

/-- PREMISE (OPEN; C++ extern `Expr.replace`): `zeroLit` on `LetOk 0` inputs agrees with `replaceNoCache zeroLitF`. -/
def ZeroLitAgrees0 : Prop :=
  ∀ e, LetOk 0 e = true →
    Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e = e.replaceNoCache zeroLitF

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
