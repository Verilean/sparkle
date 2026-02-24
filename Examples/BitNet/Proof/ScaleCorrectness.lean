/-
  Sparkle Examples — BitNet Scale Multiply Correctness Proof
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Proof

open Sparkle.Examples.BitNet

/-- The scale multiplication spec computes correctly for 1.0 × 1.0 -/
theorem scale_1_0_times_1_0 :
    fixedPointScale (BitVec.ofNat 48 0x10000) (BitVec.ofNat 32 0x01000000)
    = BitVec.ofNat 32 0x10000 := by
  native_decide

/-- The scale multiplication spec computes correctly for 2.0 × 0.5 -/
theorem scale_2_0_times_0_5 :
    fixedPointScale (BitVec.ofNat 48 0x20000) (BitVec.ofNat 32 0x00800000)
    = BitVec.ofNat 32 0x10000 := by
  native_decide

/-- Scale multiply with zero accumulator gives zero -/
theorem scale_zero_acc :
    fixedPointScale (BitVec.ofNat 48 0) (BitVec.ofNat 32 0x01000000)
    = BitVec.ofNat 32 0 := by
  native_decide

/-- Scale multiply with zero scale gives zero -/
theorem scale_zero_scale :
    fixedPointScale (BitVec.ofNat 48 0x10000) (BitVec.ofNat 32 0)
    = BitVec.ofNat 32 0 := by
  native_decide

/-- Scale multiply preserves sign (negative acc × positive scale = negative) -/
theorem scale_neg_acc : fixedPointScale
    (BitVec.ofInt 48 (-0x10000)) (BitVec.ofNat 32 0x01000000)
    = BitVec.ofInt 32 (-0x10000) := by
  native_decide

end Sparkle.Examples.BitNet.Proof
