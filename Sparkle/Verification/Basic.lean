/-
  Basic Verification Lemmas for Hardware

  This file contains fundamental theorems and lemmas about
  BitVec operations that are useful for proving hardware correctness.

  These lemmas establish properties like commutativity, associativity,
  and identity elements for fixed-width integer arithmetic.
-/

namespace Sparkle.Verification.Basic

/-- BitVec addition is commutative -/
theorem bitvec_add_comm {n : Nat} (a b : BitVec n) :
    a + b = b + a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]
  omega

/-- BitVec addition is associative -/
theorem bitvec_add_assoc {n : Nat} (a b c : BitVec n) :
    (a + b) + c = a + (b + c) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]
  omega

/-- Zero is the additive identity for BitVec -/
theorem bitvec_add_zero {n : Nat} (a : BitVec n) :
    a + 0 = a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- BitVec AND is commutative -/
theorem bitvec_and_comm {n : Nat} (a b : BitVec n) :
    a &&& b = b &&& a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega

/-- BitVec AND is associative -/
theorem bitvec_and_assoc {n : Nat} (a b c : BitVec n) :
    (a &&& b) &&& c = a &&& (b &&& c) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega

/-- BitVec AND with all ones is identity -/
theorem bitvec_and_ones {n : Nat} (a : BitVec n) :
    a &&& BitVec.allOnes n = a := by
  sorry  -- TODO: Prove using bit manipulation lemmas

/-- BitVec OR is commutative -/
theorem bitvec_or_comm {n : Nat} (a b : BitVec n) :
    a ||| b = b ||| a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_or]
  omega

/-- BitVec OR is associative -/
theorem bitvec_or_assoc {n : Nat} (a b c : BitVec n) :
    (a ||| b) ||| c = a ||| (b ||| c) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_or]
  omega

/-- BitVec OR with zero is identity -/
theorem bitvec_or_zero {n : Nat} (a : BitVec n) :
    a ||| 0 = a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_or]

/-- BitVec XOR is commutative -/
theorem bitvec_xor_comm {n : Nat} (a b : BitVec n) :
    a ^^^ b = b ^^^ a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_xor]
  omega

/-- BitVec XOR with itself is zero -/
theorem bitvec_xor_self {n : Nat} (a : BitVec n) :
    a ^^^ a = 0 := by
  sorry  -- TODO: Prove using bit manipulation lemmas

/-- Zero extension preserves the value for widths that fit -/
theorem bitvec_zero_extend_id {n : Nat} (x : BitVec n) :
    (x.zeroExtend n).truncate n = x := by
  sorry  -- TODO: Prove using extension lemmas

/-- Subtraction is the inverse of addition (without overflow) -/
theorem bitvec_sub_add_inv {n : Nat} (a b : BitVec n) :
    (a + b) - b = a := by
  sorry  -- TODO: Prove modulo arithmetic properties

/-- De Morgan's Law: NOT (a AND b) = (NOT a) OR (NOT b) -/
theorem bitvec_not_and {n : Nat} (a b : BitVec n) :
    ~~~(a &&& b) = (~~~a) ||| (~~~b) := by
  sorry  -- TODO: Prove bit-by-bit

/-- De Morgan's Law: NOT (a OR b) = (NOT a) AND (NOT b) -/
theorem bitvec_not_or {n : Nat} (a b : BitVec n) :
    ~~~(a ||| b) = (~~~a) &&& (~~~b) := by
  sorry  -- TODO: Prove bit-by-bit

/-- Double negation is identity -/
theorem bitvec_not_not {n : Nat} (a : BitVec n) :
    ~~~(~~~a) = a := by
  sorry  -- TODO: Prove bit-by-bit

/-- Shift left by 0 is identity -/
theorem bitvec_shl_zero {n : Nat} (a : BitVec n) :
    a <<< 0 = a := by
  simp [BitVec.shiftLeft_zero]

/-- Shift right by 0 is identity -/
theorem bitvec_shr_zero {n : Nat} (a : BitVec n) :
    a >>> 0 = a := by
  simp [HShiftRight.hShiftRight, ShiftRight.shiftRight]
  sorry  -- TODO: Complete with shiftRight lemmas

/-- Multiplication by zero is zero -/
theorem bitvec_mul_zero {n : Nat} (a : BitVec n) :
    a * 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]

/-- Multiplication by one is identity -/
theorem bitvec_mul_one {n : Nat} (a : BitVec n) :
    a * 1 = a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]
  omega

/-- Equality is reflexive -/
theorem bitvec_eq_refl {n : Nat} (a : BitVec n) :
    (a == a) = true := by
  simp [BEq.beq]

/-- Truncation after extension recovers original (if width matches) -/
theorem bitvec_extend_truncate {n m : Nat} (h : n ≤ m) (x : BitVec n) :
    (x.zeroExtend m).truncate n = x := by
  sorry  -- TODO: Prove using extension properties

/-- Overflow check: addition overflows iff result is less than either operand -/
theorem bitvec_add_overflow_check {n : Nat} (a b : BitVec n) :
    (a + b).toNat < a.toNat ∨ (a + b).toNat < b.toNat ↔
    a.toNat + b.toNat ≥ 2^n := by
  sorry  -- TODO: Prove using modular arithmetic

/-- Helper: Converting BitVec to Nat and back is identity (for values in range) -/
theorem bitvec_ofNat_toNat {n : Nat} (x : BitVec n) :
    BitVec.ofNat n x.toNat = x := by
  sorry  -- TODO: Prove using BitVec conversion lemmas

end Sparkle.Verification.Basic
