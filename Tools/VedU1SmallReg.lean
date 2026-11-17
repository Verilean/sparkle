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

theorem fst_val {dom : Sparkle.Core.Domain.DomainConfig} {α β : Type}
    (x : Sparkle.Core.Signal.Signal dom (α × β)) (s : Nat) :
    (Sparkle.Core.Signal.Signal.fst x).val s = (x.val s).1 := rfl

theorem snd_val {dom : Sparkle.Core.Domain.DomainConfig} {α β : Type}
    (x : Sparkle.Core.Signal.Signal dom (α × β)) (s : Nat) :
    (Sparkle.Core.Signal.Signal.snd x).val s = (x.val s).2 := rfl

/-- the high half of a concatenation `hi * 2^w + lo` (here `m = 2^w`) is `hi`. -/
theorem concat_div (x y m : Nat) (hy : y < m) : (x * m + y) / m = x := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hy, Nat.zero_add]

end Tools.VedU1SmallReg
