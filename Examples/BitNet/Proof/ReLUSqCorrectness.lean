/-
  Sparkle Examples — BitNet ReLU² Correctness Proof
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Proof

open Sparkle.Examples.BitNet

theorem relu_sq_negative :
    reluSquared (BitVec.ofInt 32 (-0x10000)) = BitVec.ofNat 32 0 := by
  native_decide

theorem relu_sq_zero :
    reluSquared (BitVec.ofNat 32 0) = BitVec.ofNat 32 0 := by
  native_decide

theorem relu_sq_one :
    reluSquared (BitVec.ofNat 32 0x10000) = BitVec.ofNat 32 0x10000 := by
  native_decide

theorem relu_sq_two :
    reluSquared (BitVec.ofNat 32 0x20000) = BitVec.ofNat 32 0x40000 := by
  native_decide

theorem relu_sq_half :
    reluSquared (BitVec.ofNat 32 0x8000) = BitVec.ofNat 32 0x4000 := by
  native_decide

theorem relu_sq_nonneg_minus2 :
    reluSquared (BitVec.ofInt 32 (-0x20000)) = BitVec.ofNat 32 0 := by
  native_decide

end Sparkle.Examples.BitNet.Proof
