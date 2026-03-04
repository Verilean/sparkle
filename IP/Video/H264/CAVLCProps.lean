/-
  CAVLC Formal Properties

  Key property: Encode-decode roundtrip correctness.
  cavlcDecode(cavlcEncode(coeffs)) should reconstruct the original
  coefficients for valid inputs.

  Verified via native_decide on concrete test vectors.

  Pattern follows QueueProps.lean.
-/

import IP.Video.H264.CAVLC
import IP.Video.H264.CAVLCDecode

namespace Sparkle.IP.Video.H264.CAVLCProps

open Sparkle.IP.Video.H264.CAVLC
open Sparkle.IP.Video.H264.CAVLCDecode

-- ============================================================================
-- Zero block roundtrip
-- ============================================================================

/-- Encoding then decoding an all-zero block produces all zeros. -/
theorem cavlc_zero_roundtrip :
    let (bs, bl) := cavlcEncodeFull (Array.replicate 16 (0 : Int))
    cavlcDecode bs bl = Array.replicate 16 (0 : Int) := by
  native_decide

-- ============================================================================
-- Non-zero block roundtrips
-- ============================================================================

/-- Encode-decode roundtrip for a block with mixed non-zero coefficients.
    Tests: TC=3, T1=2, non-T1 level (3), multiple run-before values. -/
theorem cavlc_nonzero_roundtrip :
    let coeffs : Array Int := #[0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    let (bs, bl) := cavlcEncodeFull coeffs
    cavlcDecode bs bl = coeffs := by
  native_decide

/-- Encode-decode roundtrip for a DC-only block (single coefficient at position 0).
    Tests: TC=1, T1=0, level decoding, totalZeros=0. -/
theorem cavlc_single_coeff_roundtrip :
    let coeffs : Array Int := #[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    let (bs, bl) := cavlcEncodeFull coeffs
    cavlcDecode bs bl = coeffs := by
  native_decide

/-- Encode-decode roundtrip for a block with only trailing ones (±1 values).
    Tests: TC=2, T1=2, no level decoding needed. -/
theorem cavlc_trailing_ones_roundtrip :
    let coeffs : Array Int := #[-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    let (bs, bl) := cavlcEncodeFull coeffs
    cavlcDecode bs bl = coeffs := by
  native_decide

end Sparkle.IP.Video.H264.CAVLCProps
