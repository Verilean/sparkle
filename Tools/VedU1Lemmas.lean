import Sparkle.IR.Semantics
import Sparkle.Core.Signal

/-!
# Lemmas for the U1 generated proof script (register-free operators)

Stated over the symbolic width (`2 ^ w`, never a folded literal) so the rule
is general for any width; the script instantiates `evalOp_not_lit` before
`simp` folds `2 ^ 16` to `65536`.
-/

namespace Tools.VedU1Lemmas

open Sparkle.IR.Semantics

/-- Complement within `k` bits is subtraction from all-ones. -/
theorem xor_ones (a k : Nat) (h : a < 2 ^ k) : a ^^^ (2 ^ k - 1) = 2 ^ k - 1 - a := by
  have e : 2 ^ k - 1 - a = 2 ^ k - (a + 1) := by omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_succ h, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < k
  · simp [hi]
  · have : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

/-- `Operator.not` on an in-range operand (any width). -/
theorem evalOp_not_lit (we : WEnv) (x : Sparkle.IR.AST.Expr) (a w : Nat)
    (ha : a < 2 ^ widthOf we x) :
    evalOp we .not [x] [a] w = some (2 ^ widthOf we x - 1 - a) := by
  simp only [evalOp, mask]
  rw [xor_ones _ _ ha, Nat.mod_eq_of_lt]
  omega

/-- `~~~a` on a `BitVec` signal, pointwise (the instance does not unfold under `simp`). -/
theorem compl_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Sparkle.Core.Signal.Signal dom (BitVec n)) (s : Nat) :
    (~~~a).val s = ~~~(a.val s) := rfl

/-- `Operator.and/or/xor` on in-range operands (any width). -/
theorem evalOp_and_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) : evalOp we .and xs [a, b] w = some (a &&& b) := by
  simp only [evalOp, mask]
  rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ hb)]

theorem evalOp_or_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) : evalOp we .or xs [a, b] w = some (a ||| b) := by
  simp only [evalOp, mask]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem evalOp_xor_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) : evalOp we .xor xs [a, b] w = some (a ^^^ b) := by
  simp only [evalOp, mask]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]

open Sparkle.Core.Signal in
theorem and_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a &&& b).val s = a.val s &&& b.val s := rfl

open Sparkle.Core.Signal in
theorem or_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a ||| b).val s = a.val s ||| b.val s := rfl

open Sparkle.Core.Signal in
theorem xor_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a ^^^ b).val s = a.val s ^^^ b.val s := rfl

/-- `Operator.add` (mod `2 ^ w`, no range hypothesis needed). -/
theorem evalOp_add_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .add xs [a, b] w = some ((a + b) % 2 ^ w) := rfl

open Sparkle.Core.Signal in
theorem add_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a + b).val s = a.val s + b.val s := rfl

/-- `Operator.sub` on in-range operands: `(a + (2^w - b)) % 2^w`. -/
theorem evalOp_sub_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat)
    (hb : b < 2 ^ w) : evalOp we .sub xs [a, b] w = some ((a + (2 ^ w - b)) % 2 ^ w) := by
  simp only [evalOp, mask]
  rw [Nat.mod_eq_of_lt hb]

open Sparkle.Core.Signal in
theorem sub_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a - b).val s = a.val s - b.val s := rfl

end Tools.VedU1Lemmas
