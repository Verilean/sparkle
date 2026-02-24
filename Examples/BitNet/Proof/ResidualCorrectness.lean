/-
  Sparkle Examples — BitNet Residual Addition Correctness Proof
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Proof

open Sparkle.Examples.BitNet

theorem resadd_1_plus_1 :
    residualAdd (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0x10000)
    = BitVec.ofNat 32 0x20000 := by
  native_decide

theorem resadd_2_minus_1 :
    residualAdd (BitVec.ofNat 32 0x20000) (BitVec.ofInt 32 (-0x10000))
    = BitVec.ofNat 32 0x10000 := by
  native_decide

theorem resadd_identity :
    residualAdd (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0)
    = BitVec.ofNat 32 0x10000 := by
  native_decide

theorem resadd_pos_overflow :
    residualAdd (BitVec.ofNat 32 0x7FFFFFFF) (BitVec.ofNat 32 1)
    = BitVec.ofNat 32 0x7FFFFFFF := by
  native_decide

theorem resadd_neg_overflow :
    residualAdd (BitVec.ofInt 32 (-(2^31))) (BitVec.ofInt 32 (-1))
    = BitVec.ofInt 32 (-(2^31)) := by
  native_decide

theorem resadd_neg_neg :
    residualAdd (BitVec.ofInt 32 (-0x10000)) (BitVec.ofInt 32 (-0x10000))
    = BitVec.ofInt 32 (-0x20000) := by
  native_decide

end Sparkle.Examples.BitNet.Proof
