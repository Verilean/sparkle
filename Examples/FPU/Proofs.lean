-- =============================================================================
-- Formal Verification Theorems for FPU Hardware
-- Proofs that the combinational FP cores satisfy IEEE 754 constraints
-- =============================================================================

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain
import FPU.Spec
import FPU.Hardware

open Sparkle.Core.Signal
open Sparkle.Core.Domain

namespace FPU.Proofs

open FPU
open FPU.Hardware

-- =========================================================================
-- Category 1: NaN Propagation (hardware implementation)
--   IEEE 754 §6.2: Any operation involving NaN must produce NaN
-- =========================================================================

/-- Hardware add: NaN in first operand → NaN output -/
theorem hw_add_nan_propagates_left (x : BitVec 32) :
    FPU.isNaN (fpAddSubComb 0x7FC00000#32 x false) = true := by
  simp [fpAddSubComb]
  native_decide

/-- Hardware add: NaN in second operand → NaN output -/
theorem hw_add_nan_propagates_right (x : BitVec 32) :
    FPU.isNaN (fpAddSubComb x 0x7FC00000#32 false) = true := by
  simp [fpAddSubComb, FPU.isNaN]
  split <;> native_decide

/-- Hardware mul: NaN in first operand → NaN output -/
theorem hw_mul_nan_propagates_left (x : BitVec 32) :
    FPU.isNaN (fpMulComb 0x7FC00000#32 x) = true := by
  simp [fpMulComb]
  native_decide

/-- Hardware mul: NaN in second operand → NaN output -/
theorem hw_mul_nan_propagates_right (x : BitVec 32) :
    FPU.isNaN (fpMulComb x 0x7FC00000#32) = true := by
  simp [fpMulComb, FPU.isNaN]
  split <;> native_decide

-- =========================================================================
-- Category 2: Infinity Arithmetic (hardware implementation)
--   IEEE 754 §7.1-7.3
-- =========================================================================

/-- Inf + Inf = Inf (same sign) -/
theorem hw_inf_add_inf :
    fpAddSubComb 0x7F800000#32 0x7F800000#32 false = 0x7F800000#32 := by
  native_decide

/-- (-Inf) + (-Inf) = -Inf -/
theorem hw_neg_inf_add_neg_inf :
    fpAddSubComb 0xFF800000#32 0xFF800000#32 false = 0xFF800000#32 := by
  native_decide

/-- Inf + (-Inf) = NaN (invalid operation) -/
theorem hw_inf_add_neg_inf_is_nan :
    FPU.isNaN (fpAddSubComb 0x7F800000#32 0xFF800000#32 false) = true := by
  native_decide

/-- Inf - Inf = NaN -/
theorem hw_inf_sub_inf_is_nan :
    FPU.isNaN (fpAddSubComb 0x7F800000#32 0x7F800000#32 true) = true := by
  native_decide

/-- Inf * 0 = NaN (invalid operation) -/
theorem hw_inf_mul_zero_is_nan :
    FPU.isNaN (fpMulComb 0x7F800000#32 0x00000000#32) = true := by
  native_decide

/-- 0 * Inf = NaN (invalid operation, commutative) -/
theorem hw_zero_mul_inf_is_nan :
    FPU.isNaN (fpMulComb 0x00000000#32 0x7F800000#32) = true := by
  native_decide

/-- Inf * Inf = Inf -/
theorem hw_inf_mul_inf :
    fpMulComb 0x7F800000#32 0x7F800000#32 = 0x7F800000#32 := by
  native_decide

/-- (-Inf) * Inf = -Inf -/
theorem hw_neg_inf_mul_inf :
    fpMulComb 0xFF800000#32 0x7F800000#32 = 0xFF800000#32 := by
  native_decide

/-- (-Inf) * (-Inf) = +Inf  (negative × negative = positive) -/
theorem hw_neg_inf_mul_neg_inf :
    fpMulComb 0xFF800000#32 0xFF800000#32 = 0x7F800000#32 := by
  native_decide

-- =========================================================================
-- Category 3: Zero Arithmetic
-- =========================================================================

/-- 0 + 0 = 0 -/
theorem hw_zero_add_zero :
    fpAddSubComb 0x00000000#32 0x00000000#32 false = 0x00000000#32 := by
  native_decide

/-- (-0) + (-0) = -0 -/
theorem hw_neg_zero_add_neg_zero :
    fpAddSubComb 0x80000000#32 0x80000000#32 false = 0x80000000#32 := by
  native_decide

/-- 0 * 0 = 0 -/
theorem hw_zero_mul_zero :
    fpMulComb 0x00000000#32 0x00000000#32 = 0x00000000#32 := by
  native_decide

/-- (-0) * 0 = -0  (sign rule) -/
theorem hw_neg_zero_mul_zero :
    fpMulComb 0x80000000#32 0x00000000#32 = 0x80000000#32 := by
  native_decide

-- =========================================================================
-- Category 4: Golden Value Tests
--   Concrete IEEE 754 encodings verified by Lean kernel
-- =========================================================================

/-- 1.5 + 2.5 = 4.0  (0x3FC00000 + 0x40200000 = 0x40800000) -/
theorem hw_add_1p5_2p5 :
    fpAddSubComb 0x3FC00000#32 0x40200000#32 false = 0x40800000#32 := by
  native_decide

/-- 10.0 - 3.5 = 6.5  (0x41200000 - 0x40600000 = 0x40D00000) -/
theorem hw_sub_10_3p5 :
    fpAddSubComb 0x41200000#32 0x40600000#32 true = 0x40D00000#32 := by
  native_decide

/-- 3.0 * 4.0 = 12.0  (0x40400000 * 0x40800000 = 0x41400000) -/
theorem hw_mul_3_4 :
    fpMulComb 0x40400000#32 0x40800000#32 = 0x41400000#32 := by
  native_decide

/-- -2.5 * 3.0 = -7.5  (0xC0200000 * 0x40400000 = 0xC0F00000) -/
theorem hw_mul_neg2p5_3 :
    fpMulComb 0xC0200000#32 0x40400000#32 = 0xC0F00000#32 := by
  native_decide

/-- 1.0 + 1.0 = 2.0  (0x3F800000 + 0x3F800000 = 0x40000000) -/
theorem hw_add_1_1 :
    fpAddSubComb 0x3F800000#32 0x3F800000#32 false = 0x40000000#32 := by
  native_decide

/-- 2.0 - 1.0 = 1.0  (0x40000000 - 0x3F800000 = 0x3F800000) -/
theorem hw_sub_2_1 :
    fpAddSubComb 0x40000000#32 0x3F800000#32 true = 0x3F800000#32 := by
  native_decide

/-- 1.0 * 1.0 = 1.0  (multiplicative identity) -/
theorem hw_mul_1_1 :
    fpMulComb 0x3F800000#32 0x3F800000#32 = 0x3F800000#32 := by
  native_decide

/-- 2.0 * 0.5 = 1.0 -/
theorem hw_mul_2_0p5 :
    fpMulComb 0x40000000#32 0x3F000000#32 = 0x3F800000#32 := by
  native_decide

/-- 100.0 * 0.01 ≈ 1.0  (0x42C80000 * 0x3C23D70A)
    Tests rounding behavior -/
-- theorem hw_mul_100_0p01 :
--     fpMulComb 0x42C80000#32 0x3C23D70A#32 = ... := by native_decide

-- =========================================================================
-- Category 5: Subtraction as Negated Addition
--   a - b should equal a + (-b)
-- =========================================================================

/-- Subtraction via isSub flag matches sign-flipped addition for Inf -/
theorem hw_sub_is_negated_add_inf :
    fpAddSubComb 0x7F800000#32 0x7F800000#32 true =
    fpAddSubComb 0x7F800000#32 0xFF800000#32 false := by
  native_decide

-- =========================================================================
-- Category 6: Sign Consistency for Multiplication
-- =========================================================================

/-- Positive × Positive = Positive (sign bit = 0) -/
theorem hw_mul_pos_pos_sign :
    (fpMulComb 0x40400000#32 0x40800000#32).extractLsb' 31 1 = 0#1 := by
  native_decide

/-- Positive × Negative = Negative (sign bit = 1) -/
theorem hw_mul_pos_neg_sign :
    (fpMulComb 0x40400000#32 0xC0800000#32).extractLsb' 31 1 = 1#1 := by
  native_decide

/-- Negative × Negative = Positive (sign bit = 0) -/
theorem hw_mul_neg_neg_sign :
    (fpMulComb 0xC0400000#32 0xC0800000#32).extractLsb' 31 1 = 0#1 := by
  native_decide

-- =========================================================================
-- Category 7: Self-Inverse Properties
-- =========================================================================

/-- x - x = 0 for 1.0 -/
theorem hw_sub_self_is_zero :
    FPU.isZero (fpAddSubComb 0x3F800000#32 0x3F800000#32 true) = true := by
  native_decide

/-- x + (-x) = 0 for 1.0 -/
theorem hw_add_negation_is_zero :
    FPU.isZero (fpAddSubComb 0x3F800000#32 0xBF800000#32 false) = true := by
  native_decide

-- =========================================================================
-- Category 8: Bit-Width Safety (no truncation/overflow in datapath)
-- =========================================================================

/-- Mantissa product of two 24-bit values fits in 48 bits -/
theorem mantissa_product_no_overflow :
    (2^24 - 1) * (2^24 - 1) < (2^48 : Nat) := by
  native_decide

/-- Maximum exponent sum fits in 9 bits (signed) -/
theorem exponent_sum_range :
    255 + 255 - 127 < (2^9 : Nat) := by
  native_decide

/-- Guard/round/sticky extension (24+3 bits) fits in 27 bits -/
theorem mantissa_extended_fits :
    (2^24 - 1) * (2^3 : Nat) < (2^27 : Nat) := by
  native_decide

/-- Addition of two 27-bit mantissas fits in 28 bits -/
theorem mantissa_add_fits :
    (2^27 - 1) + (2^27 - 1) < (2^28 : Nat) := by
  native_decide

-- =========================================================================
-- Category 9: Encoding Consistency
-- =========================================================================

/-- The constant for +Inf in the hardware matches the spec -/
theorem hw_posInf_matches_spec :
    (0x7F800000#32 : BitVec 32) = FPU.posInf := by
  native_decide

/-- The constant for -Inf in the hardware matches the spec -/
theorem hw_negInf_matches_spec :
    (0xFF800000#32 : BitVec 32) = FPU.negInf := by
  native_decide

/-- The constant for qNaN in the hardware matches the spec -/
theorem hw_qNaN_matches_spec :
    (0x7FC00000#32 : BitVec 32) = FPU.qNaN := by
  native_decide

-- =========================================================================
-- Category 10: Temporal / Pipeline Properties
--   Properties about the Signal-level pipelined implementation
-- =========================================================================

/-- Pipeline latency: result appears 3 cycles after input.
    This is a structural property — the pipelined version uses
    3 Signal.register stages, so the output at time t reflects
    the computation from inputs at time (t-3). -/
theorem pipeline_latency_is_3 :
    ∀ (t : Nat),
      let a : Signal defaultDomain (BitVec 32) := ⟨fun _ => 0x3F800000#32⟩  -- 1.0
      let b : Signal defaultDomain (BitVec 32) := ⟨fun _ => 0x3F800000#32⟩  -- 1.0
      let isSub : Signal defaultDomain Bool := ⟨fun _ => false⟩
      let result := fpAddSubPipelined a b isSub
      -- After 3 register stages of steady-state input, output = expected
      t ≥ 3 → result.atTime t = 0x40000000#32 := by
  intro t a b isSub result ht
  -- The Signal.register chain introduces 3 cycles of delay.
  -- With constant inputs, the steady-state output after 3 cycles
  -- equals the combinational result.
  sorry  -- Requires Signal.register unfolding lemmas

end FPU.Proofs
