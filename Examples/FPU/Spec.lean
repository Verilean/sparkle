-- =============================================================================
-- IEEE 754 Single-Precision Floating Point Arithmetic Unit
-- Pure Lean 4 Specification (for formal verification)
-- =============================================================================

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain

open Sparkle.Core.Signal
open Sparkle.Core.Domain

namespace FPU

-- ---------------------------------------------------------------------------
-- IEEE 754 Single-Precision Format
--   [31]    Sign      (1 bit)
--   [30:23] Exponent  (8 bits, biased by 127)
--   [22:0]  Mantissa  (23 bits, implicit leading 1 for normal numbers)
-- ---------------------------------------------------------------------------

/-- Operation code for the FPU -/
inductive FPOp where
  | add : FPOp
  | sub : FPOp
  | mul : FPOp
deriving Repr, BEq, DecidableEq

-- =========================================================================
-- Field Extraction (pure functions on BitVec 32)
-- =========================================================================

/-- Extract the sign bit (bit 31) -/
def sign (x : BitVec 32) : BitVec 1 :=
  x.extractLsb' 31 1

/-- Extract the exponent field (bits 30:23) -/
def exponent (x : BitVec 32) : BitVec 8 :=
  x.extractLsb' 23 8

/-- Extract the mantissa field (bits 22:0) -/
def mantissa (x : BitVec 32) : BitVec 23 :=
  x.extractLsb' 0 23

/-- Full mantissa with implicit leading 1 (or 0 for denormals): 24 bits -/
def fullMantissa (x : BitVec 32) : BitVec 24 :=
  let exp := exponent x
  let mant := mantissa x
  if exp == 0#8 then
    (0#1 ++ mant)   -- denormal: 0.mantissa
  else
    (1#1 ++ mant)   -- normal:   1.mantissa

-- =========================================================================
-- Special Value Predicates
-- =========================================================================

/-- Check if a float is zero (±0) -/
def isZero (x : BitVec 32) : Bool :=
  exponent x == 0#8 && mantissa x == 0#23

/-- Check if a float is infinity (±Inf) -/
def isInf (x : BitVec 32) : Bool :=
  exponent x == 255#8 && mantissa x == 0#23

/-- Check if a float is NaN -/
def isNaN (x : BitVec 32) : Bool :=
  exponent x == 255#8 && mantissa x != 0#23

/-- Check if a float is a denormal (subnormal) -/
def isDenorm (x : BitVec 32) : Bool :=
  exponent x == 0#8 && mantissa x != 0#23

/-- Check if a float is a normal number -/
def isNormal (x : BitVec 32) : Bool :=
  exponent x != 0#8 && exponent x != 255#8

-- =========================================================================
-- Special Value Constants
-- =========================================================================

/-- Positive zero: 0x00000000 -/
def posZero : BitVec 32 := 0x00000000#32

/-- Negative zero: 0x80000000 -/
def negZero : BitVec 32 := 0x80000000#32

/-- Positive infinity: 0x7F800000 -/
def posInf : BitVec 32 := 0x7F800000#32

/-- Negative infinity: 0xFF800000 -/
def negInf : BitVec 32 := 0xFF800000#32

/-- Canonical quiet NaN: 0x7FC00000 -/
def qNaN : BitVec 32 := 0x7FC00000#32

-- =========================================================================
-- Packing
-- =========================================================================

/-- Pack sign, exponent, mantissa into a 32-bit IEEE 754 float -/
def pack (s : BitVec 1) (e : BitVec 8) (m : BitVec 23) : BitVec 32 :=
  (s ++ e ++ m)

-- =========================================================================
-- Pure Specification of FP Addition (for verification)
-- Simplified: handles special cases, does aligned add/sub, normalize, round
-- =========================================================================

/-- Pure FP addition specification (combinational, not pipelined) -/
def fpAdd (a b : BitVec 32) : BitVec 32 :=
  -- Special cases first
  if isNaN a || isNaN b then qNaN
  else if isInf a && isInf b then
    if sign a == sign b then a  -- same sign Inf
    else qNaN                    -- Inf + (-Inf) = NaN
  else if isInf a then a
  else if isInf b then b
  else if isZero a && isZero b then
    if sign a == 1#1 && sign b == 1#1 then negZero else posZero
  else if isZero a then b
  else if isZero b then a
  else
    -- General case: aligned addition of normal/denormal numbers
    -- (Simplified reference model — full implementation in Signal DSL below)
    sorry  -- The full algorithm is in the Signal DSL hardware implementation

/-- Pure FP subtraction: negate b's sign, then add -/
def fpSub (a b : BitVec 32) : BitVec 32 :=
  let bNeg := (~~~(sign b)) ++ exponent b ++ mantissa b
  fpAdd a bNeg

/-- Pure FP multiplication specification -/
def fpMul (a b : BitVec 32) : BitVec 32 :=
  let resultSign := sign a ^^^ sign b
  -- Special cases
  if isNaN a || isNaN b then qNaN
  else if (isInf a && isZero b) || (isInf b && isZero a) then qNaN  -- Inf * 0 = NaN
  else if isInf a || isInf b then
    if resultSign == 1#1 then negInf else posInf
  else if isZero a || isZero b then
    if resultSign == 1#1 then negZero else posZero
  else
    sorry  -- Full algorithm in Signal DSL

-- =========================================================================
-- FORMAL THEOREMS: Properties that IEEE 754 floating point must satisfy
-- =========================================================================
-- -------------------------------------------------------------------------
-- 1. NaN Propagation
-- -------------------------------------------------------------------------
--
-- Problem
-- fpAdd, isNaN, or qNaN are opaque (not @[reducible] or @[inline]), so simp can't unfold them before native_decide takes over.
---

/-- NaN is absorbing for addition: NaN + x = NaN -/
theorem nan_add_left (x : BitVec 32) :
    isNaN (fpAdd qNaN x) = true := by
  have hq : isNaN qNaN = true := by native_decide
  simp [fpAdd, hq]

/-- NaN is absorbing for addition: x + NaN = NaN -/
theorem nan_add_right (x : BitVec 32) :
    isNaN qNaN = true → isNaN (fpAdd x qNaN) = true := by
  intro hq
  simp [fpAdd, hq]

/-- NaN is absorbing for multiplication: NaN * x = NaN -/
theorem nan_mul_left (x : BitVec 32) :
    isNaN (fpMul qNaN x) = true := by
  have hq : isNaN qNaN = true := by native_decide
  simp [fpMul, hq]

-- -------------------------------------------------------------------------
-- 2. Identity Elements
-- -------------------------------------------------------------------------

/-- Zero is the identity for addition (right): x + 0 = x when x is normal -/
theorem add_zero_right (x : BitVec 32) (hx : isNaN x = false)
    (hx_inf : isInf x = false) (hx_nz : isZero x = false) :
    fpAdd x posZero = x := by
  have h0_nan : isNaN posZero = false := by native_decide
  have h0_inf : isInf posZero = false := by native_decide
  have h0_zero : isZero posZero = true := by native_decide
  simp [fpAdd, hx, hx_inf, hx_nz, h0_nan, h0_inf, h0_zero]

/-- Zero is the identity for addition (left): 0 + x = x when x is normal -/
theorem add_zero_left (x : BitVec 32) (hx : isNaN x = false)
    (hx_inf : isInf x = false) (hx_nz : isZero x = false) :
    fpAdd posZero x = x := by
  have h0_nan : isNaN posZero = false := by native_decide
  have h0_inf : isInf posZero = false := by native_decide
  have h0_zero : isZero posZero = true := by native_decide
  simp [fpAdd, hx, hx_inf, hx_nz, h0_nan, h0_inf, h0_zero]

-- -------------------------------------------------------------------------
-- 3. Infinity Arithmetic
-- -------------------------------------------------------------------------

/-- Inf + Inf = Inf -/
theorem inf_add_inf : fpAdd posInf posInf = posInf := by
  have hnan : isNaN posInf = false := by native_decide
  have hinf : isInf posInf = true := by native_decide
  simp [fpAdd, hnan, hinf]

/-- Inf + (-Inf) = NaN -/
theorem inf_add_neg_inf : isNaN (fpAdd posInf negInf) = true := by
  have hp_nan : isNaN posInf = false := by native_decide
  have hn_nan : isNaN negInf = false := by native_decide
  have hp_inf : isInf posInf = true := by native_decide
  have hn_inf : isInf negInf = true := by native_decide
  have hsign : (sign posInf == sign negInf) = false := by native_decide
  have hq : isNaN qNaN = true := by native_decide
  simp [fpAdd, hp_nan, hn_nan, hp_inf, hn_inf, hsign, hq]

/-- Inf * 0 = NaN -/
theorem inf_mul_zero : isNaN (fpMul posInf posZero) = true := by
  have hi_nan : isNaN posInf = false := by native_decide
  have h0_nan : isNaN posZero = false := by native_decide
  have hi_inf : isInf posInf = true := by native_decide
  have h0_zero : isZero posZero = true := by native_decide
  have hq : isNaN qNaN = true := by native_decide
  simp [fpMul, hi_nan, h0_nan, hi_inf, h0_zero, hq]

/-- Inf * Inf = Inf -/
theorem inf_mul_inf : fpMul posInf posInf = posInf := by
  have hnan : isNaN posInf = false := by native_decide
  have hinf : isInf posInf = true := by native_decide
  have hzero : isZero posInf = false := by native_decide
  simp [fpMul, hnan, hinf, hzero]

/-- (-Inf) * Inf = -Inf  (sign rule) -/
theorem neg_inf_mul_inf : fpMul negInf posInf = negInf := by
  have hn_nan : isNaN negInf = false := by native_decide
  have hp_nan : isNaN posInf = false := by native_decide
  have hn_inf : isInf negInf = true := by native_decide
  have hp_inf : isInf posInf = true := by native_decide
  have hn_zero : isZero negInf = false := by native_decide
  have hp_zero : isZero posInf = false := by native_decide
  have hsign : (sign negInf ^^^ sign posInf == 1#1) = true := by native_decide
  simp [fpMul, hn_nan, hp_nan, hn_inf, hp_inf, hn_zero, hp_zero, hsign]

-- -------------------------------------------------------------------------
-- 4. Zero Arithmetic
-- -------------------------------------------------------------------------

/-- 0 * x = 0 for any normal x -/
theorem zero_mul_normal (x : BitVec 32)
    (hx : isNaN x = false) (hx_inf : isInf x = false) (hx_nz : isZero x = false) :
    isZero (fpMul posZero x) = true := by
  have h0_nan : isNaN posZero = false := by native_decide
  have h0_inf : isInf posZero = false := by native_decide
  have h0_zero : isZero posZero = true := by native_decide
  have hn_zero : isZero negZero = true := by native_decide
  by_cases hsign : (sign posZero ^^^ sign x == 1#1)
  · simp [fpMul, hx, hx_inf, hx_nz, h0_nan, h0_inf, h0_zero, hn_zero, hsign]
  · simp [fpMul, hx, hx_inf, hx_nz, h0_nan, h0_inf, h0_zero, hsign]

/-- 0 + 0 = 0 -/
theorem zero_add_zero : fpAdd posZero posZero = posZero := by
  have hnan : isNaN posZero = false := by native_decide
  have hinf : isInf posZero = false := by native_decide
  have hzero : isZero posZero = true := by native_decide
  have hsign : (sign posZero == 1#1) = false := by native_decide
  simp [fpAdd, hnan, hinf, hzero, hsign]

/-- (-0) + (-0) = -0 -/
theorem neg_zero_add_neg_zero : fpAdd negZero negZero = negZero := by
  have hnan : isNaN negZero = false := by native_decide
  have hinf : isInf negZero = false := by native_decide
  have hzero : isZero negZero = true := by native_decide
  have hsign : (sign negZero == 1#1) = true := by native_decide
  simp [fpAdd, hnan, hinf, hzero, hsign]

-- -------------------------------------------------------------------------
-- 5. NaN Predicate Consistency
-- -------------------------------------------------------------------------

/-- qNaN is recognized as NaN -/
theorem qNaN_isNaN : isNaN qNaN = true := by
  native_decide

/-- Positive infinity is not NaN -/
theorem posInf_not_NaN : isNaN posInf = false := by
  native_decide

/-- Zero is not NaN -/
theorem posZero_not_NaN : isNaN posZero = false := by
  native_decide

/-- Positive infinity is infinity -/
theorem posInf_isInf : isInf posInf = true := by
  native_decide

/-- Negative infinity is infinity -/
theorem negInf_isInf : isInf negInf = true := by
  native_decide

/-- Zero is zero -/
theorem posZero_isZero : isZero posZero = true := by
  native_decide

/-- NaN is not zero -/
theorem qNaN_not_zero : isZero qNaN = false := by
  native_decide

/-- NaN is not infinity -/
theorem qNaN_not_inf : isInf qNaN = false := by
  native_decide

-- -------------------------------------------------------------------------
-- 6. Sign Rules for Multiplication
-- -------------------------------------------------------------------------

/-- Sign of product: positive * positive = positive sign -/
theorem mul_sign_pos_pos :
    sign posInf ^^^ sign posInf = 0#1 := by
  native_decide

/-- Sign of product: positive * negative = negative sign -/
theorem mul_sign_pos_neg :
    sign posInf ^^^ sign negInf = 1#1 := by
  native_decide

/-- Sign of product: negative * negative = positive sign -/
theorem mul_sign_neg_neg :
    sign negInf ^^^ sign negInf = 0#1 := by
  native_decide

-- -------------------------------------------------------------------------
-- 7. Pack/Unpack Roundtrip
-- -------------------------------------------------------------------------

/-- Packing then extracting sign recovers the original sign -/
theorem pack_sign (s : BitVec 1) (e : BitVec 8) (m : BitVec 23) :
    sign (pack s e m) = s := by
  simp [sign, pack]
  sorry  -- Requires BitVec concat/extract lemmas

/-- Packing then extracting exponent recovers the original exponent -/
theorem pack_exponent (s : BitVec 1) (e : BitVec 8) (m : BitVec 23) :
    exponent (pack s e m) = e := by
  simp [exponent, pack]
  sorry  -- Requires BitVec concat/extract lemmas

/-- Packing then extracting mantissa recovers the original mantissa -/
theorem pack_mantissa (s : BitVec 1) (e : BitVec 8) (m : BitVec 23) :
    mantissa (pack s e m) = m := by
  simp [mantissa, pack]
  sorry  -- Requires BitVec concat/extract lemmas

-- -------------------------------------------------------------------------
-- 8. Bit-Width Sufficiency (overflow safety)
-- -------------------------------------------------------------------------

/-- 24-bit × 24-bit mantissa product fits in 48 bits -/
theorem mantissa_product_fits_48 :
    (2^24 - 1) * (2^24 - 1) < (2^48 : Nat) := by
  native_decide

/-- Exponent sum (8-bit + 8-bit - 127) fits in signed 10 bits -/
theorem exponent_sum_fits_10 :
    (255 + 255 : Nat) < (2^9 : Nat) := by
  native_decide

/-- Aligned mantissa with guard bits fits in 28 bits -/
theorem aligned_mantissa_fits_28 :
    (2^24 - 1 : Nat) * 8 < (2^28 : Nat) := by
  native_decide

-- -------------------------------------------------------------------------
-- 9. Concrete Value Tests (golden values, checked by Lean kernel)
-- -------------------------------------------------------------------------

/-- 1.0 in IEEE 754 = 0x3F800000 -/
theorem one_encoding : (0x3F800000#32 : BitVec 32) =
    pack 0#1 127#8 0#23 := by
  native_decide

/-- 2.0 in IEEE 754 = 0x40000000 -/
theorem two_encoding : (0x40000000#32 : BitVec 32) =
    pack 0#1 128#8 0#23 := by
  native_decide

/-- -1.0 in IEEE 754 = 0xBF800000 -/
theorem neg_one_encoding : (0xBF800000#32 : BitVec 32) =
    pack 1#1 127#8 0#23 := by
  native_decide

/-- Sign of 1.0 is 0 (positive) -/
theorem sign_of_one : sign 0x3F800000#32 = 0#1 := by
  native_decide

/-- Exponent of 1.0 is 127 -/
theorem exponent_of_one : exponent 0x3F800000#32 = 127#8 := by
  native_decide

/-- Mantissa of 1.0 is 0 -/
theorem mantissa_of_one : mantissa 0x3F800000#32 = 0#23 := by
  native_decide

/-- fullMantissa of 1.0 is 0x800000 (implicit 1 bit) -/
theorem full_mantissa_of_one :
    fullMantissa 0x3F800000#32 = 0x800000#24 := by
  native_decide

end FPU
