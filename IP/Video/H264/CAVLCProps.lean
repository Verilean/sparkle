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

end Sparkle.IP.Video.H264.CAVLCProps
