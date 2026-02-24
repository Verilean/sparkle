/-
  Sparkle Examples — BitNet Dot Product Specification

  Pure-Lean reference implementations and properties for the INT8 dot product
  used in the attention Q·K^T computation.
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Spec

open Sparkle.Examples.BitNet

/-- The maximum absolute value of an INT8 dot product element contribution.
    |q_i × k_i| ≤ 128 × 128 = 16384 -/
def maxProductMagnitude : Nat := 128 * 128

/-- The maximum absolute value of a dot product sum over `n` elements.
    |sum| ≤ n × 16384 -/
def maxDotMagnitude (n : Nat) : Nat := n * maxProductMagnitude

/-- Required bit width for a signed dot product sum over `n` INT8 elements.
    Need to hold values in [-maxDotMagnitude, +maxDotMagnitude].
    productBits + ceil(log2(n)) bits. -/
def dotProductWidth (n : Nat) : Nat := productBits + ceilLog2 n

/-- INT8 dot product is equivalent to sum of element-wise products -/
theorem int8DotProduct_def (a b : Array QActivation) :
    int8DotProduct a b = Id.run do
      let n := min a.size b.size
      let mut sum : Int := 0
      for i in [:n] do
        let ai := if h : i < a.size then a[i].toInt else 0
        let bi := if h : i < b.size then b[i].toInt else 0
        sum := sum + ai * bi
      return sum := by
  rfl

/-- Scaled score divides the dot product by 2^shift -/
theorem scaledScore_def (a b : Array QActivation) (shift : Nat) :
    scaledScore a b shift = int8DotProduct a b / (2 ^ shift : Int) := by
  rfl

/-- Dot product of empty arrays is zero -/
theorem dot_empty :
    int8DotProduct #[] #[] = 0 := by
  native_decide

end Sparkle.Examples.BitNet.Spec
