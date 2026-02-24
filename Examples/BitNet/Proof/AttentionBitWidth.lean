/-
  Sparkle Examples — BitNet Attention Bit-Width Sufficiency Proofs
-/

import Examples.BitNet.Config

namespace Sparkle.Examples.BitNet.Proof

open Sparkle.Examples.BitNet

theorem int8_product_fits_16 : 128 * 128 < (2^15 : Nat) := by
  native_decide

theorem dot64_fits_22 : headDim * (128 * 128) < (2^21 : Nat) := by
  native_decide

theorem dot4_fits_18 : 4 * (128 * 128) < (2^17 : Nat) := by
  native_decide

theorem scaled_dot64_fits_22 : headDim * (128 * 128) / 8 < (2^21 : Nat) := by
  native_decide

theorem product_width_sufficient : productBits = 16 := by
  rfl

theorem dot64_width : productBits + ceilLog2 headDim = 22 := by
  native_decide

theorem quant_shift10_range : (2 * (2^16 : Nat)) / 2^10 = 128 := by
  native_decide

end Sparkle.Examples.BitNet.Proof
