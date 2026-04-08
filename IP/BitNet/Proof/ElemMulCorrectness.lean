/-
  Sparkle Examples — BitNet Element-wise Multiply Correctness Proof
-/

import IP.BitNet.Config
import IP.BitNet.Types

namespace Sparkle.IP.BitNet.Proof

open Sparkle.IP.BitNet

theorem elem_mul_1_times_1 :
    elemMul (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0x10000)
    = BitVec.ofNat 32 0x10000 := by
  native_decide

theorem elem_mul_2_times_3 :
    elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0x30000)
    = BitVec.ofNat 32 0x60000 := by
  native_decide

theorem elem_mul_2_times_0_5 :
    elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0x8000)
    = BitVec.ofNat 32 0x10000 := by
  native_decide

theorem elem_mul_zero :
    elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0)
    = BitVec.ofNat 32 0 := by
  native_decide

theorem elem_mul_neg_pos :
    elemMul (BitVec.ofInt 32 (-0x20000)) (BitVec.ofNat 32 0x30000)
    = BitVec.ofInt 32 (-0x60000) := by
  native_decide

theorem elem_mul_neg_neg :
    elemMul (BitVec.ofInt 32 (-0x20000)) (BitVec.ofInt 32 (-0x30000))
    = BitVec.ofNat 32 0x60000 := by
  native_decide

end Sparkle.IP.BitNet.Proof
