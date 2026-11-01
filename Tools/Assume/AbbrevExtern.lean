import Tools.ShippingLetsExternSpec
import Tools.ShippingGen5ReaderTrace
set_option autoImplicit false
-- Built in Pod (kjob lake build, exit 0) on the tree of 2afbcc18af7226555f7c5b77916e265d4bbc3779 (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source. (assumption module: statements and the model definitions they mention; no theorems.)

/-! # Behaviour assumptions: `Expr.replace` and `Expr.headBeta` as used by `inlAbbrevs` (RT abbrev S1)

**This file holds ONLY assumption statements** — `Prop` definitions that proofs take as hypotheses — and the total Lean
models their statements mention. Nothing here is an `axiom` or a theorem; proof files must not redefine them.
Design: `scripts/gen5/RT_ABBREV_S1_FREEZE.md` rev2 (reviewer-approved at 7aefd1b4; the new T1 premise was adopted by the
user, option A of `scripts/gen5/RT_ABBREV_S1_DECISION.md`).

Pins: `lean-toolchain` = leanprover/lean4:v4.32.1 (commit f054605aea4b840552cca2e725580bffd1e1b704). Both comparisons are
READINGS of the source, not proofs.

| name | ledger row | extern / core function |
|---|---|---|
| `ReplaceAgrees` (U-1) | replaces T1L-54 (`ZeroLitAgrees0` becomes a theorem, `zeroLitAgrees0_of_replace`) | `Expr.replace` (`lean_replace_expr`) |
| `HeadBetaAgrees0` (U-2) | new T1 (+1) | `Expr.headBeta` (`betaRev` is a `partial def`; `instantiate` / `instantiateRange` are externs) |

* `ReplaceAgrees`: C++ `replace_fn.cpp:87-154` (v4.32.1) caches the result for shared nodes keyed by pointer and otherwise recurses
  exactly as `replaceNoCache` does; since `f` is a pure function the cache cannot change the result. Limits: the pointer-keyed cache's
  correctness (no address reuse during one call) is a runtime property read, not proved; the running binary is matched to the source by
  commit string only; `update_let`'s `nondep` handling was not re-checked in detail.
* `HeadBetaAgrees0`: `headBetaSpec` copies the control flow of core `headBeta` / `betaRev.go` (a reading of the Lean source) and models
  `instantiate` / `instantiateRange` after `kernel/instantiate.cpp` (`instantiate_core`, with `lift_loose_bvars` for substituted values).
  Limits: `unsigned` truncation for offsets / counts `≥ 2^32` is not modelled; the `partial def` is assumed to run its body as read.
  The statement is limited to `NoPh e ∧ BvarLt 0 e` inputs (the inputs `inlAbbrevs` passes). Preservation of `NoPh ∧ BvarLt 0` is NOT assumed:
  it is a theorem (`headBeta_good`).
* Re-check both when `lean-toolchain` changes. -/

namespace Tools.Assume.AbbrevExtern
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace

/-- (Definition used by `HeadBetaAgrees0`.) Model of `Expr.instantiate` / `Expr.instantiateRange`: loose `bvar i` (`i ≥ off`) with
`i - off < e - b` becomes `subst[b + (i - off)]` lifted by `off`; larger ones are lowered by `e - b`. -/
def instSpec (subst : Array Lean.Expr) (b e : Nat) : Lean.Expr → Nat → Lean.Expr
  | .bvar i, off =>
    if i < off then .bvar i
    else if i - off < e - b then liftSpec (subst[b + (i - off)]!) 0 off
    else .bvar (i - (e - b))
  | .app f x, off => .app (instSpec subst b e f off) (instSpec subst b e x off)
  | .lam n t bd bi, off => .lam n (instSpec subst b e t off) (instSpec subst b e bd (off + 1)) bi
  | .forallE n t bd bi, off => .forallE n (instSpec subst b e t off) (instSpec subst b e bd (off + 1)) bi
  | .letE n t v bd nd, off =>
    .letE n (instSpec subst b e t off) (instSpec subst b e v off) (instSpec subst b e bd (off + 1)) nd
  | .mdata m x, off => .mdata m (instSpec subst b e x off)
  | .proj n i x, off => .proj n i (instSpec subst b e x off)
  | x, _ => x

/-- (Definition used by `HeadBetaAgrees0`.) Model of `betaRev.go` (`useZeta := false`, `preserveMData := false`). -/
def betaGo (revArgs : Array Lean.Expr) (sz : Nat) : Lean.Expr → Nat → Lean.Expr
  | .lam _ _ bd _, i => if i + 1 < sz then betaGo revArgs sz bd (i + 1) else instSpec revArgs 0 sz bd 0
  | .mdata _ bd, i => betaGo revArgs sz bd i
  | e, i => Lean.Expr.mkAppRevRange (instSpec revArgs (sz - i) sz e 0) 0 (sz - i) revArgs

/-- (Definition used by `HeadBetaAgrees0`.) Model of `betaRev f revArgs`. -/
def betaRevSpec (f : Lean.Expr) (revArgs : Array Lean.Expr) : Lean.Expr :=
  if revArgs.size == 0 then f else betaGo revArgs revArgs.size f 0

/-- (Definition used by `HeadBetaAgrees0`.) Total model of `Expr.headBeta`. -/
def headBetaSpec (e : Lean.Expr) : Lean.Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then betaRevSpec f e.getAppRevArgs else e

/-- **ASSUMPTION U-1 (replaces T1L-54).** `Expr.replace f e` equals the structural `Expr.replaceNoCache f e`, for every `f` and `e`.
* Why not proved: `Expr.replace` is `replaceImpl`, `@[extern "lean_replace_expr"] opaque` (`Lean/Util/ReplaceExpr.lean:16-19`); the
  structural `replaceNoCache` (:22-35) is not linked to it in the logic.
* C++ compared (by reading, not formally): `src/kernel/replace_fn.cpp:151-154` (`replace_fn` :87-146), tag v4.32.1. The cache only
  reuses the result of a pure `f` for shared nodes.
* Use: one direction only (rewrite `replace` to `replaceNoCache`) in `inlAbbrevs` and, via `zeroLitAgrees0_of_replace`, for `zeroLit`.
* Limits: cache correctness (pointer keys) is a runtime property that was read, not proved. Re-check when `lean-toolchain` changes. -/
def ReplaceAgrees : Prop :=
  ∀ (f : Lean.Expr → Option Lean.Expr) (e : Lean.Expr), e.replace f = e.replaceNoCache f

/-- **ASSUMPTION U-2 (new T1).** On `NoPh e ∧ BvarLt 0 e` inputs core `Expr.headBeta` equals the total model `headBetaSpec`.
* Why not proved: `betaRev` is a `partial def` (no body in the logic) calling the externs `Expr.instantiate` /
  `Expr.instantiateRange`.
* Compared (by reading, not formally): Lean `Lean/Expr.lean:1593-1617, 1658-1660` and C++ `src/kernel/instantiate.cpp` (`instantiate_core`,
  `lean_expr_instantiate`, `lean_expr_instantiate_range`), `kernel/expr.cpp:448-475` (`lift_loose_bvars`), tag v4.32.1.
* Domain: `NoPh e ∧ BvarLt 0 e`. Not assumed: that `headBeta` preserves `NoPh ∧ BvarLt 0` (proved in `headBeta_good`).
* Limits: `unsigned` truncation (`≥ 2^32`) is out of the model; the `partial def` is read as running its body. -/
def HeadBetaAgrees0 : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true → e.headBeta = headBetaSpec e

end Tools.Assume.AbbrevExtern
