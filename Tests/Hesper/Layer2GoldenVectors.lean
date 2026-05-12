/-
  Sparkle ↔ Hesper Equivalence — Layer 2 (concrete v1a golden vectors).

  Layer 1 (in `BitLinearEquivalence.lean`) closed the **datapath
  shape** Sparkle ↔ Hesper bridge over `Int`. Layer 2 grounds it in
  the actual numerics by exercising the **8 BitNet v1a golden vectors**
  from `Tests/Integration/BitNetSoCTest.lean:43-51`.

  ## Why no Hesper `forwardRow` here

  Hesper's `forwardRow` uses i2_s packing, which assumes the input
  dimension is a multiple of 128 (one packed group spans 32 bytes,
  4 codes per byte). Sparkle's BitNet **v1a** config uses `dim = 4`
  with hardwired ternary weights — that doesn't fit the i2_s shape
  at all. So Layer 2's role is not "run Hesper's kernel on the v1a
  fixture" (impossible) but to **pin Sparkle's BitVec output, the
  `Int` reference, and the high-level math `y = x + 64x³` together
  on the same 8 inputs**.

  ## The v1a math

  With dim=4, 1 layer, all-+1 ternary weights, unit scales:

    activations = [x, x, x, x]
    gateAcc     = x + x + x + x = 4x
    gateScaled  = 4x  (unit Q8.24 scale)
    gateActivated = (4x)²    via ReLU²
    upScaled    = 4x         (same as gate path, no ReLU²)
    elemResult  = (4x)² * (4x) = 64 x³  (after fixed-point arithmetic)
    downAcc     = 64 x³
    downScaled  = 64 x³
    output      = x + 64 x³  (residual)

  This is the function we cross-check Sparkle's hardware output
  against, in `Int` arithmetic for the integer-valued v1a inputs
  (the hardware uses Q16.16, so `x = 1.0` is `0x00010000` etc.).

  Per `feedback_hesper_float_bridge.md`: we use `native_decide`,
  not axioms about `Float`.
-/

import IP.RV32.BitNetPeripheral

namespace Sparkle.Tests.Hesper.Layer2GoldenVectors

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.BitNetPeripheral

/-! ## High-level math reference

`refMath x_q16_16` returns the expected output of `bitNetPeripheral`
when the input is a 32-bit pattern interpreted as Q16.16 fixed-point.

Specifically: `output_q16_16 = x_q16_16 + 64 * x_int^3` where the cube
is computed in Q16.16 form (with Q-style multiplication, i.e. shifting
right by 16 after each multiply). For integer-valued inputs in the
v1a fixture, the cube-then-shift is exact. -/

/-- Evaluate Sparkle's `bitNetPeripheral` on a constant input,
    returning the output as a `Nat` (so `native_decide` can chew it). -/
def runPeripheral (x : Nat) : Nat :=
  let inputSig : Signal defaultDomain (BitVec 32) :=
    Signal.pure (BitVec.ofNat 32 x)
  let outSig := bitNetPeripheral inputSig
  (outSig.atTime 0).toNat

/-! ## The 8 golden vectors (verbatim from BitNetSoCTest.lean) -/

/-- Each pair: (Q16.16 input, expected Q16.16 output). -/
def goldenVectors : Array (Nat × Nat) := #[
  (0x00010000, 0x00410000),
  (0x00020000, 0x02020000),
  (0x00030000, 0x06C30000),
  (0x00040000, 0x10040000),
  (0x00080000, 0x80080000),
  (0x00000100, 0x00000100),
  (0x12345678, 0x5AD1BC9A),
  (0x00000000, 0x00000000)
]

/-! ## Layer 2 cross-checks

We discharge each vector with `native_decide`. Each line proves
that running `bitNetPeripheral` on the input produces the expected
output bit pattern. This is the per-vector data-equivalence claim. -/

theorem golden_v1 : runPeripheral 0x00010000 = 0x00410000 := by native_decide
theorem golden_v2 : runPeripheral 0x00020000 = 0x02020000 := by native_decide
theorem golden_v3 : runPeripheral 0x00030000 = 0x06C30000 := by native_decide
theorem golden_v4 : runPeripheral 0x00040000 = 0x10040000 := by native_decide
theorem golden_v5 : runPeripheral 0x00080000 = 0x80080000 := by native_decide
theorem golden_v6 : runPeripheral 0x00000100 = 0x00000100 := by native_decide
theorem golden_v7 : runPeripheral 0x12345678 = 0x5AD1BC9A := by native_decide
theorem golden_v8 : runPeripheral 0x00000000 = 0x00000000 := by native_decide

/-! ## All-vectors theorem

A single `native_decide` over the array — fails fast on any
divergence; serves as the headline "Layer 2 closed" theorem. -/

theorem all_golden_vectors_pass :
    ∀ (i : Fin goldenVectors.size),
      let (input, expected) := goldenVectors[i]
      runPeripheral input = expected := by
  native_decide

/-! ## Integer-arithmetic cross-check: y = x + 64·x³ for v1a small ints

For `x = 1, 2, 3, 4` (Q16.16-encoded), the expected output equals
`x + 64 x³` interpreted directly in Q16.16. We discharge this as a
sanity check that our high-level math matches the Sparkle hardware. -/

/-- Q16.16 encoding of a small natural number. -/
def q16_16 (n : Nat) : Nat := n * 0x10000

/-- Decode a Q16.16 integer-valued bit pattern back to its underlying
    natural (assumes the fractional part is zero, i.e. low 16 bits 0). -/
def fromQ16_16 (q : Nat) : Nat := q / 0x10000

/-- The v1a math `y = x + 64 x³` agrees with the golden output for
    the small-int inputs `x ∈ {1, 2, 3, 4, 8}`. -/
theorem v1a_math_int_x1 : 1 + 64 * 1^3 = fromQ16_16 0x00410000 := by native_decide
theorem v1a_math_int_x2 : 2 + 64 * 2^3 = fromQ16_16 0x02020000 := by native_decide
theorem v1a_math_int_x3 : 3 + 64 * 3^3 = fromQ16_16 0x06C30000 := by native_decide
theorem v1a_math_int_x4 : 4 + 64 * 4^3 = fromQ16_16 0x10040000 := by native_decide
theorem v1a_math_int_x8 : 8 + 64 * 8^3 = fromQ16_16 0x80080000 := by native_decide

end Sparkle.Tests.Hesper.Layer2GoldenVectors
