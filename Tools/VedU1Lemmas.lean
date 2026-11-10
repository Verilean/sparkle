import Sparkle.IR.Semantics

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

end Tools.VedU1Lemmas
