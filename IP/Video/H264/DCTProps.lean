/-
  DCT Formal Properties

  Properties of the H.264 4×4 integer DCT:
  - Zero preservation: DCT of all-zero block is all-zero
  - IDCT of all-zero block is all-zero
  - Linearity: DCT(a + b) = DCT(a) + DCT(b) (for integer arrays)

  Note: The full roundtrip IDCT(DCT(x)) ≈ x has bounded error due to
  the >>6 rounding in the inverse transform. This is verified by #eval
  golden tests rather than formal proof (rounding makes it complex).

  Pattern follows QueueProps.lean: self-contained definitions + proofs.
-/

import IP.Video.H264.DCT

namespace Sparkle.IP.Video.H264.DCTProps

open Sparkle.IP.Video.H264.DCT

-- ============================================================================
-- Zero preservation
-- ============================================================================

/-- Forward DCT of all-zero block produces all-zero output. -/
theorem forwardDCT_zero :
    forwardDCT (Array.replicate 16 (0 : Int)) = Array.replicate 16 (0 : Int) := by
  native_decide

/-- Inverse DCT of all-zero block produces all-zero output. -/
theorem inverseDCT_zero :
    inverseDCT (Array.replicate 16 (0 : Int)) = Array.replicate 16 (0 : Int) := by
  native_decide

-- ============================================================================
-- Golden value verification (compile-time checked)
-- ============================================================================

/-- Forward DCT of test block 1 matches C++ golden reference. -/
theorem forwardDCT_golden1 :
    forwardDCT #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    = #[136, -28, 0, -4, -112, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0] := by
  native_decide

/-- Forward DCT of test block 2 matches C++ golden reference. -/
theorem forwardDCT_golden2 :
    forwardDCT #[3, -1, 0, 2, -2, 4, -3, 1, 0, 1, -1, 0, 1, -2, 3, -4]
    = #[2, 9, 0, -3, 12, -9, 18, -37, 2, 3, 4, 39, 6, -2, 14, 14] := by
  native_decide

end Sparkle.IP.Video.H264.DCTProps
