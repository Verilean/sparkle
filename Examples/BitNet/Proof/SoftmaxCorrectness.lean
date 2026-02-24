/-
  Sparkle Examples — BitNet Softmax Correctness Proofs
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Proof

open Sparkle.Examples.BitNet

theorem exp_zero_is_one : expQ8_24 0 = (2^softmaxFracBits : Nat) := by
  native_decide

theorem exp_neg_less_one : expQ8_24 (-1) < (2^softmaxFracBits : Nat) := by
  native_decide

theorem max_score_basic : maxScore #[3, 1, 4, 1] = 4 := by
  native_decide

theorem max_score_negative : maxScore #[-5, -3, -1] = -1 := by
  native_decide

theorem softmax_equal_weights :
    let ws := softmaxRef #[5, 5, 5, 5]
    ws.size == 4 ∧ ws[0]! == ws[1]! ∧ ws[1]! == ws[2]! ∧ ws[2]! == ws[3]! := by
  native_decide

theorem weight_v_product_fits_40 :
    (2^softmaxFracBits : Nat) * 128 < 2^39 := by
  native_decide

theorem weighted_sum_fits_42 :
    4 * ((2^softmaxFracBits : Nat) * 128) < 2^41 := by
  native_decide

theorem exp_sum_fits_27 :
    4 * (2^softmaxFracBits : Nat) < 2^27 := by
  native_decide

end Sparkle.Examples.BitNet.Proof
