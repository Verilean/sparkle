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

theorem evalOp_asr_lit (we : WEnv) (x y : Sparkle.IR.AST.Expr) (a b w : Nat) :
    evalOp we .asr [x, y] [a, b] w =
      some (mask (widthOf we x) (Int.toNat ((toSigned (widthOf we x) a >>> b) % (2 ^ widthOf we x : Nat)))) := rfl

/-- The signed reading of the IR (`toSigned`) is `BitVec.toInt`. -/
theorem toSigned_toInt (w : Nat) (hw : 0 < w) (x : BitVec w) : toSigned w x.toNat = x.toInt := by
  unfold toSigned BitVec.toInt
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  simp only [Nat.add_sub_cancel]
  by_cases h : x.toNat < 2 ^ k
  · have h2 : 2 * x.toNat < 2 ^ (k+1) := by omega
    simp [h, h2]
  · have h2 : ¬ 2 * x.toNat < 2 ^ (k+1) := by omega
    simp [h, h2]

theorem toInt_ofNat_toSigned (w : Nat) (hw : 0 < w) (a : Nat) (ha : a < 2 ^ w) :
    (BitVec.ofNat w a).toInt = toSigned w a := by
  rw [← toSigned_toInt w hw]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem toNat_sshiftRight' {w : Nat} (x : BitVec w) (n : Nat) :
    (x.sshiftRight n).toNat = ((x.toInt >>> n) % ((2 ^ w : Nat) : Int)).toNat := by
  have h := BitVec.toInt_sshiftRight (x := x) (n := n)
  rw [← BitVec.toNat_ofInt, ← h, BitVec.ofInt_toInt]

theorem mask_emod (s : Int) (w : Nat) : (s % ((2 ^ w : Nat) : Int)).toNat % 2 ^ w = (s % ((2 ^ w : Nat) : Int)).toNat := by
  have h1 : 0 < ((2 ^ w : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos w
  have h2 := Int.emod_nonneg s (Int.ne_of_gt h1)
  have h3 := Int.emod_lt_of_pos s h1
  apply Nat.mod_eq_of_lt
  omega

theorem slt_eq {w : Nat} (x y : BitVec w) : BitVec.slt x y = decide (x.toInt < y.toInt) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.slt_iff_toInt_lt]

theorem ult_eq {w : Nat} (x y : BitVec w) : BitVec.ult x y = decide (x.toNat < y.toNat) := by
  simp [BitVec.ult]

theorem and_mod_r (x y m : Nat) (h : y < m) : (x &&& y) % m = x &&& y :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right h)

theorem and_mod_l (x y m : Nat) (h : x < m) : (x &&& y) % m = x &&& y :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left h)

open Sparkle.Core.Signal in
theorem add_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a + b).val s = a.val s + b := rfl

open Sparkle.Core.Signal in
theorem add_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a + b).val s = a + b.val s := rfl

open Sparkle.Core.Signal in
theorem sub_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a - b).val s = a.val s - b := rfl

open Sparkle.Core.Signal in
theorem sub_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a - b).val s = a - b.val s := rfl

open Sparkle.Core.Signal in
theorem mul_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a * b).val s = a.val s * b := rfl

open Sparkle.Core.Signal in
theorem mul_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a * b).val s = a * b.val s := rfl

open Sparkle.Core.Signal in
theorem and_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a &&& b).val s = a.val s &&& b := rfl

open Sparkle.Core.Signal in
theorem and_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a &&& b).val s = a &&& b.val s := rfl

open Sparkle.Core.Signal in
theorem or_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a ||| b).val s = a.val s ||| b := rfl

open Sparkle.Core.Signal in
theorem or_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a ||| b).val s = a ||| b.val s := rfl

open Sparkle.Core.Signal in
theorem xor_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a ^^^ b).val s = a.val s ^^^ b := rfl

open Sparkle.Core.Signal in
theorem xor_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a ^^^ b).val s = a ^^^ b.val s := rfl

open Sparkle.Core.Signal in
theorem shl_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a <<< b).val s = a.val s <<< b := rfl

open Sparkle.Core.Signal in
theorem shl_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a <<< b).val s = a <<< b.val s := rfl

open Sparkle.Core.Signal in
theorem shr_val_sc {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : Signal dom (BitVec n)) (b : BitVec n) (s : Nat) : (a >>> b).val s = a.val s >>> b := rfl

open Sparkle.Core.Signal in
theorem shr_val_cs {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat}
    (a : BitVec n) (b : Signal dom (BitVec n)) (s : Nat) : (a >>> b).val s = a >>> b.val s := rfl

open Sparkle.Core.Signal in
theorem append_def_sc {dom : Sparkle.Core.Domain.DomainConfig} {m n : Nat}
    (a : Signal dom (BitVec m)) (b : BitVec n) :
    (a ++ b : Signal dom (BitVec (no_index (m + n)))) = (· ++ ·) <$> a <*> Signal.pure b := rfl

open Sparkle.Core.Signal in
theorem append_def_cs {dom : Sparkle.Core.Domain.DomainConfig} {m n : Nat}
    (a : BitVec m) (b : Signal dom (BitVec n)) :
    (a ++ b : Signal dom (BitVec (no_index (m + n)))) = (· ++ ·) <$> Signal.pure a <*> b := rfl

/-- A high constant (multiple of `2^w`) or-ed with a `w`-bit value is their sum. -/
theorem or_hi (c x w : Nat) (hx : x < 2 ^ w) (hc : c % 2 ^ w = 0) : c ||| x = c + x := by
  have e : (c / 2 ^ w) <<< w = c := by
    rw [Nat.shiftLeft_eq]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc)
  have := Nat.shiftLeft_add_eq_or_of_lt hx (c / 2 ^ w)
  rw [e] at this
  exact this.symm

theorem or_hi_8 (c x : Nat) (hx : x < 2 ^ 8) (hc : c % 2 ^ 8 = 0) : c ||| x = c + x := or_hi c x 8 hx hc

theorem or_hi_16 (c x : Nat) (hx : x < 2 ^ 16) (hc : c % 2 ^ 16 = 0) : c ||| x = c + x := or_hi c x 16 hx hc

theorem or_hi_24 (c x : Nat) (hx : x < 2 ^ 24) (hc : c % 2 ^ 24 = 0) : c ||| x = c + x := or_hi c x 24 hx hc

theorem or_hi_32 (c x : Nat) (hx : x < 2 ^ 32) (hc : c % 2 ^ 32 = 0) : c ||| x = c + x := or_hi c x 32 hx hc

theorem or_hi_40 (c x : Nat) (hx : x < 2 ^ 40) (hc : c % 2 ^ 40 = 0) : c ||| x = c + x := or_hi c x 40 hx hc

theorem or_hi_48 (c x : Nat) (hx : x < 2 ^ 48) (hc : c % 2 ^ 48 = 0) : c ||| x = c + x := or_hi c x 48 hx hc

theorem or_hi_64 (c x : Nat) (hx : x < 2 ^ 64) (hc : c % 2 ^ 64 = 0) : c ||| x = c + x := or_hi c x 64 hx hc

theorem bit1_eq {w : Nat} (x : BitVec w) (i : Nat) :
    (BitVec.extractLsb' i 1 x = 1#1) ↔ x.toNat >>> i % 2 = 1 := by
  rw [BitVec.toNat_eq]; simp [BitVec.extractLsb'_toNat]

/-- `==` between two `BitVec.ofNat` values of one width is a `decide` on the residues. -/
theorem beq_ofNat (w a b : Nat) :
    (BitVec.ofNat w a == BitVec.ofNat w b) = decide (a % 2 ^ w = b % 2 ^ w) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.toNat_eq, BitVec.toNat_ofNat]

/-- `Bool.toNat` of a `decide`: a Prop-level `if` (what `split` and `omega` handle). -/
theorem toNat_decide_ite (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 :=
  apply_ite Bool.toNat p true false

theorem toNat_not_decide_ite (p : Prop) [Decidable p] : (!decide p).toNat = if p then 0 else 1 := by
  by_cases h : p <;> simp [h]

/-- literal xor on single bits (`Bool` ports lowered through `^^^ 1`) -/
theorem xor_one_one : (1 : Nat) ^^^ 1 = 0 := rfl

/-- `Bool.toNat` as a Prop-level `if` (then `Bool.and_eq_true`, `Bool.or_eq_true`, `decide_eq_true_eq`
turn a combination of `decide`s into Prop connectives for `split` / `omega`). -/
theorem toNat_ite_true (b : Bool) : b.toNat = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem ule_decide {n : Nat} (x y : BitVec n) : x.ule y = decide (x.toNat ≤ y.toNat) := rfl

theorem ult_decide {n : Nat} (x y : BitVec n) : x.ult y = decide (x.toNat < y.toNat) := rfl

/-- an equation `BitVec.ofNat w a = y` is a residue equation on `Nat` (for `omega`). -/
theorem ofNat_eq_iff {w : Nat} (a : Nat) (y : BitVec w) :
    BitVec.ofNat w a = y ↔ a % 2 ^ w = y.toNat := by
  rw [BitVec.toNat_eq]; simp [BitVec.toNat_ofNat]

end Tools.VedU1Lemmas
