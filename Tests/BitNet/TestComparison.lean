/-
  Hespera RTL vs GPU Comparison Tests

  Compares fixed-point RTL outputs against floating-point reference values
  to verify numerical accuracy within tolerance.

  Q16.16 ↔ Float conversion utilities and tolerance-based comparison.
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Tests.Comparison

open Sparkle.Examples.BitNet

-- ============================================================================
-- Q16.16 ↔ Float Conversion Utilities
-- ============================================================================

/-- Convert Q16.16 fixed-point to Float -/
def q16_16_to_float (x : Activation) : Float :=
  let xi := x.toInt
  Float.ofInt xi / Float.ofNat (2^16)

/-- Convert Float to Q16.16 fixed-point -/
def float_to_q16_16 (f : Float) : Activation :=
  let scaled := f * Float.ofNat (2^16)
  if scaled ≥ 0.0 then
    BitVec.ofInt 32 (Int.ofNat scaled.toUInt64.toNat)
  else
    -- For negative: negate, convert, then negate result
    let posScaled := (-scaled)
    BitVec.ofInt 32 (-(Int.ofNat posScaled.toUInt64.toNat))

/-- Check if two floats are within relative tolerance -/
def withinTolerance (actual expected : Float) (relTol : Float := 0.001) : Bool :=
  if expected == 0.0 then
    Float.abs actual < relTol
  else
    let relErr := Float.abs (actual - expected) / Float.abs expected
    relErr < relTol

/-- Simple test harness -/
def checkCmp (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  PASS: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"

-- ============================================================================
-- Conversion Round-trip Tests
-- ============================================================================

def testConversions : IO Unit := do
  IO.println "--- Q16.16 ↔ Float Conversion Tests ---"

  -- 1.0
  let v1 := float_to_q16_16 1.0
  let f1 := q16_16_to_float v1
  checkCmp "roundtrip 1.0" (withinTolerance f1 1.0)

  -- -1.0
  let vm1 := float_to_q16_16 (-1.0)
  let fm1 := q16_16_to_float vm1
  checkCmp "roundtrip -1.0" (withinTolerance fm1 (-1.0))

  -- 0.5
  let v05 := float_to_q16_16 0.5
  let f05 := q16_16_to_float v05
  checkCmp "roundtrip 0.5" (withinTolerance f05 0.5)

  -- 0.0
  let v0 := float_to_q16_16 0.0
  let f0 := q16_16_to_float v0
  checkCmp "roundtrip 0.0" (f0 == 0.0)

  -- 100.0
  let v100 := float_to_q16_16 100.0
  let f100 := q16_16_to_float v100
  checkCmp "roundtrip 100.0" (withinTolerance f100 100.0)

-- ============================================================================
-- Spec vs Float Reference Comparison
-- ============================================================================

def testReLUSqComparison : IO Unit := do
  IO.println "--- ReLU² RTL vs Float Comparison ---"

  -- Test: relu²(2.0) should be 4.0
  let input := float_to_q16_16 2.0
  let result := reluSquared input
  let resultFloat := q16_16_to_float result
  checkCmp "relu²(2.0) ≈ 4.0" (withinTolerance resultFloat 4.0)

  -- Test: relu²(0.5) should be 0.25
  let input2 := float_to_q16_16 0.5
  let result2 := reluSquared input2
  let result2Float := q16_16_to_float result2
  checkCmp "relu²(0.5) ≈ 0.25" (withinTolerance result2Float 0.25)

  -- Test: relu²(-3.0) should be 0.0
  let input3 := float_to_q16_16 (-3.0)
  let result3 := reluSquared input3
  let result3Float := q16_16_to_float result3
  checkCmp "relu²(-3.0) ≈ 0.0" (result3Float == 0.0)

  -- Test: relu²(1.5) should be 2.25
  let input4 := float_to_q16_16 1.5
  let result4 := reluSquared input4
  let result4Float := q16_16_to_float result4
  checkCmp "relu²(1.5) ≈ 2.25" (withinTolerance result4Float 2.25)

def testElemMulComparison : IO Unit := do
  IO.println "--- ElemMul RTL vs Float Comparison ---"

  -- Test: 2.5 × 3.0 = 7.5
  let a := float_to_q16_16 2.5
  let b := float_to_q16_16 3.0
  let result := elemMul a b
  let resultFloat := q16_16_to_float result
  checkCmp "2.5×3.0 ≈ 7.5" (withinTolerance resultFloat 7.5)

  -- Test: -1.5 × 2.0 = -3.0
  let a2 := float_to_q16_16 (-1.5)
  let b2 := float_to_q16_16 2.0
  let result2 := elemMul a2 b2
  let result2Float := q16_16_to_float result2
  checkCmp "-1.5×2.0 ≈ -3.0" (withinTolerance result2Float (-3.0))

  -- Test: 0.1 × 0.1 = 0.01
  let a3 := float_to_q16_16 0.1
  let b3 := float_to_q16_16 0.1
  let result3 := elemMul a3 b3
  let result3Float := q16_16_to_float result3
  checkCmp "0.1×0.1 ≈ 0.01" (withinTolerance result3Float 0.01 0.02)  -- Wider tolerance for small values

def testResidualAddComparison : IO Unit := do
  IO.println "--- ResidualAdd RTL vs Float Comparison ---"

  -- Test: 1.5 + 2.5 = 4.0
  let a := float_to_q16_16 1.5
  let b := float_to_q16_16 2.5
  let result := residualAdd a b
  let resultFloat := q16_16_to_float result
  checkCmp "1.5+2.5 ≈ 4.0" (withinTolerance resultFloat 4.0)

  -- Test: -1.0 + 0.5 = -0.5
  let a2 := float_to_q16_16 (-1.0)
  let b2 := float_to_q16_16 0.5
  let result2 := residualAdd a2 b2
  let result2Float := q16_16_to_float result2
  checkCmp "-1.0+0.5 ≈ -0.5" (withinTolerance result2Float (-0.5))

def testScaleComparison : IO Unit := do
  IO.println "--- Scale Multiply RTL vs Float Comparison ---"

  -- Test: acc=128.0, scale=0.5 → 64.0
  -- acc in Q16.16: 128.0 = 0x800000 (fits in 48 bits)
  -- scale in Q8.24: 0.5 = 0x00800000
  let acc : Accumulator := BitVec.ofNat 48 0x800000
  let scale : ScaleFactor := BitVec.ofNat 32 0x00800000
  let result := fixedPointScale acc scale
  let resultFloat := q16_16_to_float result
  checkCmp "scale: 128.0×0.5 ≈ 64.0" (withinTolerance resultFloat 64.0)

  -- Test: acc=1.0, scale=2.0
  -- acc Q16.16: 0x10000
  -- scale Q8.24: 2.0 = 0x02000000
  let acc2 : Accumulator := BitVec.ofNat 48 0x10000
  let scale2 : ScaleFactor := BitVec.ofNat 32 0x02000000
  let result2 := fixedPointScale acc2 scale2
  let result2Float := q16_16_to_float result2
  checkCmp "scale: 1.0×2.0 ≈ 2.0" (withinTolerance result2Float 2.0)

def runAll : IO Unit := do
  IO.println "=== RTL vs Float Comparison Tests ==="
  IO.println ""
  testConversions
  testReLUSqComparison
  testElemMulComparison
  testResidualAddComparison
  testScaleComparison
  IO.println ""
  IO.println "=== Comparison tests complete ==="

end Sparkle.Examples.BitNet.Tests.Comparison
