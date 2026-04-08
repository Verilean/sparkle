/-
  Basic Verification Lemmas for Hardware

  Re-exports and aliases for BitVec properties from Lean4 stdlib.
  Users can import this for convenient access to common lemmas.
-/

namespace Sparkle.Verification.Basic

-- Addition
theorem bitvec_add_comm {n : Nat} (a b : BitVec n) : a + b = b + a := BitVec.add_comm a b
theorem bitvec_add_assoc {n : Nat} (a b c : BitVec n) : (a + b) + c = a + (b + c) := BitVec.add_assoc a b c
theorem bitvec_add_zero {n : Nat} (a : BitVec n) : a + 0 = a := by simp

-- Bitwise AND
theorem bitvec_and_comm {n : Nat} (a b : BitVec n) : a &&& b = b &&& a := BitVec.and_comm a b
theorem bitvec_and_assoc {n : Nat} (a b c : BitVec n) : (a &&& b) &&& c = a &&& (b &&& c) := BitVec.and_assoc a b c
theorem bitvec_and_ones {n : Nat} (a : BitVec n) : a &&& BitVec.allOnes n = a := by simp

-- Bitwise OR
theorem bitvec_or_comm {n : Nat} (a b : BitVec n) : a ||| b = b ||| a := BitVec.or_comm a b
theorem bitvec_or_assoc {n : Nat} (a b c : BitVec n) : (a ||| b) ||| c = a ||| (b ||| c) := by ext i; simp [Bool.or_assoc]
theorem bitvec_or_zero {n : Nat} (a : BitVec n) : a ||| 0 = a := by simp

-- Bitwise XOR
theorem bitvec_xor_comm {n : Nat} (a b : BitVec n) : a ^^^ b = b ^^^ a := BitVec.xor_comm a b
theorem bitvec_xor_self {n : Nat} (a : BitVec n) : a ^^^ a = 0 := by ext i; simp

-- Shifts
theorem bitvec_shl_zero {n : Nat} (a : BitVec n) : a <<< 0 = a := by simp
theorem bitvec_shr_zero {n : Nat} (a : BitVec n) : a >>> 0 = a := by simp

-- Multiplication
theorem bitvec_mul_zero {n : Nat} (a : BitVec n) : a * 0 = 0 := by simp
theorem bitvec_mul_one {n : Nat} (a : BitVec n) : a * 1 = a := by simp [BitVec.mul_one]

-- Negation
theorem bitvec_not_not {n : Nat} (a : BitVec n) : ~~~(~~~a) = a := by ext i; simp

-- Equality
theorem bitvec_eq_refl {n : Nat} (a : BitVec n) : (a == a) = true := by simp

end Sparkle.Verification.Basic
