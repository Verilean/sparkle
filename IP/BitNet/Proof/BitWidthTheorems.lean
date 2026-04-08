/-
  Sparkle Examples — BitNet Bit-Width Sufficiency Theorems
-/

import IP.BitNet.Config

namespace Sparkle.IP.BitNet.Proof

open Sparkle.IP.BitNet

theorem squared_fits_64 : (2^31 - 1) * (2^31 - 1) < (2^63 : Nat) := by
  native_decide

theorem sq_sum_fits_76 : ffnDim * ((2^31 - 1) * (2^31 - 1)) < (2^75 : Nat) := by
  native_decide

theorem scale_prod_fits_80 : (2^47 - 1) * (2^31 - 1) < (2^79 : Nat) := by
  native_decide

theorem elem_mul_fits_64 : (2^31 - 1) * (2^31 - 1) < (2^63 : Nat) := by
  native_decide

theorem resadd_fits_33 : (2^31 - 1) + (2^31 - 1) < (2^32 : Nat) := by
  native_decide

theorem acc_fits_in_mul : accBits ≤ mulProductBits := by
  native_decide

theorem scale_fits_in_mul : scaleTotalBits ≤ mulProductBits := by
  native_decide

end Sparkle.IP.BitNet.Proof
