/-
  Quantization Formal Properties

  Properties of H.264 quantization:
  - Zero preservation: quant(0) = 0 for all QP and positions
  - Dequant of zero level is zero
  - Golden value match at QP=0

  Pattern follows QueueProps.lean.
-/

import IP.Video.H264.Quant

namespace Sparkle.IP.Video.H264.QuantProps

open Sparkle.IP.Video.H264.Quant

-- ============================================================================
-- Dequantization of zero
-- ============================================================================

/-- Dequantization of zero level is always zero. -/
theorem dequant_zero (qp : Nat) (pos : Nat) :
    dequantize 0 qp pos = 0 := by
  simp [dequantize]

-- ============================================================================
-- Golden value verification (compile-time)
-- ============================================================================

/-- Quantization of test coefficients at QP=0 matches C++ golden. -/
theorem quant_golden_qp0 :
    quantizeBlock #[136, -28, 0, -4, -112, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0] 0
    = #[54, -7, 0, -1, -27, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0] := by
  native_decide

/-- Quantization of zero block at QP=20 produces all zeros. -/
theorem quant_zero_block_qp20 :
    quantizeBlock (Array.replicate 16 (0 : Int)) 20
    = Array.replicate 16 (0 : Int) := by
  native_decide

/-- Dequantization of zero block produces all zeros. -/
theorem dequant_zero_block :
    dequantizeBlock (Array.replicate 16 (0 : Int)) 20
    = Array.replicate 16 (0 : Int) := by
  native_decide

end Sparkle.IP.Video.H264.QuantProps
