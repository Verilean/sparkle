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

open Sparkle.Core.Signal in
/-- `a ++ b` on `BitVec` signals is the lifted append.  The result type `m + n` is
`no_index`: `simp` normalises it to a literal (`1 + 16` to `17`), which the discrimination
tree would otherwise not match against `m + n`. -/
theorem append_def {dom : Sparkle.Core.Domain.DomainConfig} {m n : Nat}
    (a : Signal dom (BitVec m)) (b : Signal dom (BitVec n)) :
    (a ++ b : Signal dom (BitVec (no_index (m + n)))) = (· ++ ·) <$> a <*> b := rfl

/-- `toNat` of a `BitVec` concatenation, arithmetic form (the core `<<<`/`|||` form is opaque
to `omega`).  `no_index` as in `append_def`. -/
theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y : BitVec (no_index (m + n))).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq, Nat.mul_comm]

/-- `Operator.sub` on in-range operands: `(a + (2^w - b)) % 2^w`. -/
theorem evalOp_sub_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat)
    (hb : b < 2 ^ w) : evalOp we .sub xs [a, b] w = some ((a + (2 ^ w - b)) % 2 ^ w) := by
  simp only [evalOp, mask]
  rw [Nat.mod_eq_of_lt hb]

open Sparkle.Core.Signal in
theorem sub_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a - b).val s = a.val s - b.val s := rfl

/-- `Operator.mux` (condition nonzero selects the first value). -/
theorem evalOp_mux_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (c a b w : Nat) :
    evalOp we .mux xs [c, a, b] w = some (if c ≠ 0 then a else b) := rfl

open Sparkle.Core.Signal in
theorem mux_val {dom : Sparkle.Core.Domain.DomainConfig} {α : Type}
    (c : Signal dom Bool) (a b : Signal dom α) (s : Nat) :
    (Signal.mux c a b).val s = if c.val s then a.val s else b.val s := rfl

/-- `Operator.eq` (a 1-bit result). -/
theorem evalOp_eq_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .eq xs [a, b] w = some (if a = b then 1 else 0) := rfl

/-- `Signal.pure` is constant in time (`.const v w` and a constant output). -/
theorem pure_val {dom : Sparkle.Core.Domain.DomainConfig} {α : Type} (a : α) (s : Nat) :
    (Sparkle.Core.Signal.Signal.pure (dom := dom) a).val s = a := rfl

/-- `Operator.mul`/`shl`/`shr` (mod `2 ^ w`; no range hypothesis). -/
theorem evalOp_mul_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .mul xs [a, b] w = some ((a * b) % 2 ^ w) := rfl

theorem evalOp_shl_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .shl xs [a, b] w = some ((a <<< b) % 2 ^ w) := rfl

theorem evalOp_shr_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .shr xs [a, b] w = some (a >>> b) := rfl

theorem evalOp_lt_u_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .lt_u xs [a, b] w = some (if a < b then 1 else 0) := rfl

theorem evalOp_le_u_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .le_u xs [a, b] w = some (if a ≤ b then 1 else 0) := rfl

theorem evalOp_gt_u_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .gt_u xs [a, b] w = some (if b < a then 1 else 0) := rfl

theorem evalOp_ge_u_lit (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .ge_u xs [a, b] w = some (if b ≤ a then 1 else 0) := rfl

theorem evalOp_lt_s_lit (we : WEnv) (x y : Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .lt_s [x, y] [a, b] w =
      some (if toSigned (max (widthOf we x) (widthOf we y)) a < toSigned (max (widthOf we x) (widthOf we y)) b then 1 else 0) := rfl

open Sparkle.Core.Signal in
theorem mul_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a * b).val s = a.val s * b.val s := rfl

open Sparkle.Core.Signal in
theorem shl_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a <<< b).val s = a.val s <<< b.val s := rfl

open Sparkle.Core.Signal in
theorem shr_val {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (s : Nat) : (a >>> b).val s = a.val s >>> b.val s := rfl

open Sparkle.Core.Signal in
theorem bool_and_val {dom : Sparkle.Core.Domain.DomainConfig}
    (a b : Signal dom Bool) (s : Nat) : (a &&& b).val s = (a.val s && b.val s) := rfl

open Sparkle.Core.Signal in
theorem bool_or_val {dom : Sparkle.Core.Domain.DomainConfig}
    (a b : Signal dom Bool) (s : Nat) : (a ||| b).val s = (a.val s || b.val s) := rfl

open Sparkle.Core.Signal in
theorem bool_xor_val {dom : Sparkle.Core.Domain.DomainConfig}
    (a b : Signal dom Bool) (s : Nat) : (a ^^^ b).val s = xor (a.val s) (b.val s) := rfl

open Sparkle.Core.Signal in
theorem bool_compl_val {dom : Sparkle.Core.Domain.DomainConfig}
    (a : Signal dom Bool) (s : Nat) : (~~~a).val s = !(a.val s) := rfl

/-- Fallbacks without a range hypothesis (tried after the range-guarded forms): the value
stays an expression, which the finite input domain closes. -/
theorem evalOp_not_raw (we : WEnv) (x : Sparkle.IR.AST.Expr) (a w : Nat) :
    evalOp we .not [x] [a] w = some ((a ^^^ (2 ^ widthOf we x - 1)) % 2 ^ widthOf we x) := rfl

theorem evalOp_and_raw (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .and xs [a, b] w = some ((a &&& b) % 2 ^ w) := rfl

theorem evalOp_or_raw (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .or xs [a, b] w = some ((a ||| b) % 2 ^ w) := rfl

theorem evalOp_xor_raw (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .xor xs [a, b] w = some ((a ^^^ b) % 2 ^ w) := rfl

theorem evalOp_sub_raw (we : WEnv) (xs : List Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .sub xs [a, b] w = some ((a + (2 ^ w - b % 2 ^ w)) % 2 ^ w) := rfl

end Tools.VedU1Lemmas
