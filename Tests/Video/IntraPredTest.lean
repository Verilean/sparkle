/-
  Test: Intra Prediction
  Verifies all supported prediction modes and residual roundtrip.
-/

import LSpec
import IP.Video.H264.IntraPred

open Sparkle.IP.Video.H264.IntraPred

namespace Sparkle.Tests.Video.IntraPredTest

private def testN : Neighbors :=
  { above := #[10, 20, 30, 40, 50, 60, 70, 80]
  , left := #[15, 25, 35, 45]
  , aboveLeft := 5
  , hasAbove := true
  , hasLeft := true }

def testPredictionModes : IO LSpec.TestSeq := do
  let vert := predict 0 testN
  let horiz := predict 1 testN
  let dc := predict 2 testN
  let ddl := predict 3 testN

  pure $ LSpec.group "Prediction Modes" (
    LSpec.test "vertical matches golden" (vert ==
      #[10, 20, 30, 40, 10, 20, 30, 40, 10, 20, 30, 40, 10, 20, 30, 40]) ++
    LSpec.test "horizontal matches golden" (horiz ==
      #[15, 15, 15, 15, 25, 25, 25, 25, 35, 35, 35, 35, 45, 45, 45, 45]) ++
    LSpec.test "DC matches golden" (dc ==
      #[28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28]) ++
    LSpec.test "DDL matches golden" (ddl ==
      #[20, 30, 40, 50, 30, 40, 50, 60, 40, 50, 60, 70, 50, 60, 70, 78])
  )

def testResidualRoundtrip : IO LSpec.TestSeq := do
  let original : Block4x4 := #[100, 110, 120, 130, 105, 115, 125, 135,
                                 110, 120, 130, 140, 115, 125, 135, 145]
  let predicted := predict 0 testN
  let residual := computeResidual original predicted
  let reconstructed := reconstruct predicted residual

  pure $ LSpec.group "Residual Roundtrip" (
    LSpec.test "reconstruct(pred, orig - pred) = orig" (reconstructed == original)
  )

def testModeDecision : IO LSpec.TestSeq := do
  -- Vertical pattern: constant columns
  let vertBlock : Block4x4 := #[10, 20, 30, 40, 10, 20, 30, 40,
                                  10, 20, 30, 40, 10, 20, 30, 40]
  let bestV := bestMode vertBlock testN

  -- Horizontal pattern: constant rows
  let horizBlock : Block4x4 := #[15, 15, 15, 15, 25, 25, 25, 25,
                                   35, 35, 35, 35, 45, 45, 45, 45]
  let bestH := bestMode horizBlock testN

  pure $ LSpec.group "Mode Decision" (
    LSpec.test "vertical pattern picks mode 0" (bestV == 0) ++
    LSpec.test "horizontal pattern picks mode 1" (bestH == 1)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- Intra Prediction Tests ---"
  let t1 ← testPredictionModes
  let t2 ← testResidualRoundtrip
  let t3 ← testModeDecision
  return LSpec.group "Intra Prediction" (t1 ++ t2 ++ t3)

end Sparkle.Tests.Video.IntraPredTest
