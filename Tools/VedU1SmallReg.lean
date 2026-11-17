import Sparkle.IR.Semantics
import Sparkle.Core.Signal

/-!
# Lemmas for small regression rows of the U1 generated proof script

`Neg` on a `Signal (BitVec n)` and `Operator.neg` of the IR semantics, stated like the
other operator lemmas of `Tools.VedU1Lemmas` (unfolding lemmas, `rfl`).
-/

namespace Tools.VedU1SmallReg

open Sparkle.IR.Semantics

theorem neg_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Sparkle.Core.Signal.Signal dom (BitVec n)) (s : Nat) :
    (-a).val s = -(a.val s) := rfl

theorem evalOp_neg_raw (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a w : Nat) :
    evalOp we .neg xs [a] w = some ((2 ^ w - a % 2 ^ w) % 2 ^ w) := rfl

end Tools.VedU1SmallReg
