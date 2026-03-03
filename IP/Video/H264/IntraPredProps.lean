/-
  Intra Prediction Formal Properties

  Key property: residual roundtrip correctness.
  reconstruct(predicted, original - predicted) = original
  (when values are in valid pixel range [0, 255])

  Golden value verification for all supported modes.

  Pattern follows QueueProps.lean.
-/

import IP.Video.H264.IntraPred

namespace Sparkle.IP.Video.H264.IntraPredProps

open Sparkle.IP.Video.H264.IntraPred

-- ============================================================================
-- Golden value verification (compile-time)
-- ============================================================================

private def testN : Neighbors :=
  { above := #[10, 20, 30, 40, 50, 60, 70, 80]
  , left := #[15, 25, 35, 45]
  , aboveLeft := 5
  , hasAbove := true
  , hasLeft := true }

/-- Vertical prediction matches golden. -/
theorem vertical_golden :
    predict 0 testN =
    #[10, 20, 30, 40, 10, 20, 30, 40, 10, 20, 30, 40, 10, 20, 30, 40] := by
  native_decide

/-- Horizontal prediction matches golden. -/
theorem horizontal_golden :
    predict 1 testN =
    #[15, 15, 15, 15, 25, 25, 25, 25, 35, 35, 35, 35, 45, 45, 45, 45] := by
  native_decide

/-- DC prediction matches golden. -/
theorem dc_golden :
    predict 2 testN =
    #[28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28] := by
  native_decide

/-- Diagonal down-left prediction matches golden. -/
theorem ddl_golden :
    predict 3 testN =
    #[20, 30, 40, 50, 30, 40, 50, 60, 40, 50, 60, 70, 50, 60, 70, 78] := by
  native_decide

/-- Residual roundtrip: reconstruct(predicted, original - predicted) = original
    for a concrete test case where all values are in [0, 255]. -/
theorem residual_roundtrip_concrete :
    let original : Block4x4 := #[100, 110, 120, 130, 105, 115, 125, 135,
                                  110, 120, 130, 140, 115, 125, 135, 145]
    let predicted := predict 0 testN
    let residual := computeResidual original predicted
    reconstruct predicted residual = original := by
  native_decide

end Sparkle.IP.Video.H264.IntraPredProps
