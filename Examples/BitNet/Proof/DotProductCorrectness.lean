/-
  Sparkle Examples — BitNet Dot Product Correctness Proofs
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Proof

open Sparkle.Examples.BitNet

theorem dot_1x1_pos :
    int8DotProduct #[BitVec.ofInt 8 1] #[BitVec.ofInt 8 1] = 1 := by
  native_decide

theorem dot_mixed_zero :
    int8DotProduct
      #[BitVec.ofInt 8 1, BitVec.ofInt 8 0, BitVec.ofInt 8 (-1)]
      #[BitVec.ofInt 8 1, BitVec.ofInt 8 1, BitVec.ofInt 8 1]
    = 0 := by
  native_decide

theorem dot_2elem :
    int8DotProduct
      #[BitVec.ofInt 8 2, BitVec.ofInt 8 3]
      #[BitVec.ofInt 8 4, BitVec.ofInt 8 5]
    = 23 := by
  native_decide

theorem dot_4elem :
    int8DotProduct
      #[BitVec.ofInt 8 1, BitVec.ofInt 8 2, BitVec.ofInt 8 3, BitVec.ofInt 8 4]
      #[BitVec.ofInt 8 4, BitVec.ofInt 8 3, BitVec.ofInt 8 2, BitVec.ofInt 8 1]
    = 20 := by
  native_decide

theorem dot_extreme_neg :
    int8DotProduct #[BitVec.ofInt 8 (-128)] #[BitVec.ofInt 8 127]
    = -16256 := by
  native_decide

theorem dot_extreme_pos :
    int8DotProduct #[BitVec.ofInt 8 127] #[BitVec.ofInt 8 127]
    = 16129 := by
  native_decide

theorem dot_neg_neg :
    int8DotProduct #[BitVec.ofInt 8 (-10)] #[BitVec.ofInt 8 (-20)]
    = 200 := by
  native_decide

theorem scaled_score_basic :
    scaledScore
      #[BitVec.ofInt 8 8, BitVec.ofInt 8 8]
      #[BitVec.ofInt 8 8, BitVec.ofInt 8 8]
      3
    = 16 := by
  native_decide

theorem scaled_score_no_shift :
    scaledScore
      #[BitVec.ofInt 8 2, BitVec.ofInt 8 3]
      #[BitVec.ofInt 8 4, BitVec.ofInt 8 5]
      0
    = 23 := by
  native_decide

theorem quantize_one :
    quantizeToInt8 (BitVec.ofNat 32 0x10000) 10 = BitVec.ofInt 8 64 := by
  native_decide

theorem quantize_zero :
    quantizeToInt8 (BitVec.ofNat 32 0) 10 = BitVec.ofInt 8 0 := by
  native_decide

theorem quantize_pos_sat :
    quantizeToInt8 (BitVec.ofNat 32 0x7FFFFFFF) 10 = BitVec.ofNat 8 127 := by
  native_decide

theorem quantize_neg_sat :
    quantizeToInt8 (BitVec.ofInt 32 (-0x7FFFFFFF)) 10
    = BitVec.ofInt 8 (-128) := by
  native_decide

theorem quantize_neg_one :
    quantizeToInt8 (BitVec.ofInt 32 (-0x10000)) 10
    = BitVec.ofInt 8 (-64) := by
  native_decide

end Sparkle.Examples.BitNet.Proof
