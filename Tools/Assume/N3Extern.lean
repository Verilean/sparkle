import Tools.ShippingLetsExternSpec
import Sparkle.Compiler.MachRawSurface
set_option autoImplicit false
-- NOT BUILT: assumption module (statements only; no theorems).

/-! # Behaviour assumptions: Lean C++ externs used by the reader (N3)

**This directory (`Tools/Assume/`) holds ONLY assumption statements** — `Prop` definitions that proofs take as
hypotheses — and the definitions their statements mention. Nothing here is an `axiom` or a theorem. They are expected
to change (Lean version updates, narrowed domains), so they are kept apart from the proofs: a change here is a change
of what is assumed and needs reviewer approval; proof files must not redefine them.

Design: `scripts/gen3/N3_EXTERN_MIN.md` rev2 (bb665fa2, reviewer-approved design) §3.4.2. Each assumption is a
domain-limited equality between an opaque C++ extern and a structural Lean model; the range (LetOk-preservation)
statements are PROVED from them in `Tools/ShippingN3ExternAgree.lean`.

Pins: `lean-toolchain` = leanprover/lean4:v4.32.1 (commit f054605aea4b840552cca2e725580bffd1e1b704). The C++ comparison
is a reading of the source, not a proof; known limits: `unsigned` truncation of `s,d ≥ 2^32` (out of the reader's
range), the running binary being built from that source (commit string matched only).

| name | ledger row | extern |
|---|---|---|
| `LiftAgrees0` (A1) | T1L-55 | `Expr.liftLooseBVars` |
| `LowerAgreesEq` (A2) | T1L-56 | `Expr.lowerLooseBVars` |
| `ZeroLitAgrees0` (A3) | T1L-54 | `Expr.replace` (in `zeroLit`) |
-/

namespace Tools.Assume.N3Extern
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv

/-- (Definition used by A3.) The `Expr.replace` function of `zeroLit` (the text of `ZeroLitAgrees`' right-hand side). -/
def zeroLitF (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | .app (.const ``BitVec.zero _) w =>
    (canonicalNatLitValue? w).map fun n => mkApp2 (.const ``BitVec.ofNat []) (inlNatLit n) (inlNatLit 0)
  | _ => none

/-- (Definition used by A2; part of the assumption's meaning.) Model of `Expr.lowerLooseBVars e s d`: loose bound variables `≥ s` are lowered by `d`. -/
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

/-- **ASSUMPTION A1 (T1L-55).** `liftLooseBVars` at `s = 0` on `LetOk 0` inputs agrees with `liftSpec`.
* Why not proved: `Expr.liftLooseBVars` is `@[extern "lean_expr_lift_loose_bvars"] opaque` (`Lean/Expr.lean:1362-1363`,
  v4.32.1): no body in the logic.
* C++ compared (by reading, not formally): `src/kernel/expr.cpp:469-475` (body `lift_loose_bvars` :448-463), tag v4.32.1.
* Domain: `LetOk 0` inputs, `s = 0`, any `d` (the reader's callsites). Re-check when `lean-toolchain` changes. -/
def LiftAgrees0 : Prop :=
  ∀ (e : Expr) (d : Nat), LetOk 0 e = true → e.liftLooseBVars 0 d = liftSpec e 0 d

/-- **ASSUMPTION A2 (T1L-56).** `lowerLooseBVars i i` on `LetOk 0` inputs agrees with `lowerSpec`.
* Why not proved: `Expr.lowerLooseBVars` is `@[extern "lean_expr_lower_loose_bvars"] opaque` (`Lean/Expr.lean:1357-1358`).
* C++ compared (by reading): `src/kernel/expr.cpp:440-446` (body :417-434), tag v4.32.1.
* Domain: `LetOk 0` inputs, `s = d = i`. Re-check when `lean-toolchain` changes. -/
def LowerAgreesEq : Prop :=
  ∀ (e : Expr) (i : Nat), LetOk 0 e = true → e.lowerLooseBVars i i = lowerSpec e i i

/-- **ASSUMPTION A3 (T1L-54).** `zeroLit` on `LetOk 0` inputs agrees with `replaceNoCache zeroLitF`.
* Why not proved: `Expr.replace` is `replaceImpl`, `@[extern "lean_replace_expr"] opaque` (`Lean/Util/ReplaceExpr.lean:16-19`);
  the structural reference `replaceNoCache` (:22-35) is not linked to it in the logic.
* C++ compared (by reading): `src/kernel/replace_fn.cpp:151-154` (`replace_fn` :87-146), tag v4.32.1.
* Domain: `LetOk 0` inputs. Re-check when `lean-toolchain` changes. -/
def ZeroLitAgrees0 : Prop :=
  ∀ e, LetOk 0 e = true →
    Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e = e.replaceNoCache zeroLitF

end Tools.Assume.N3Extern
