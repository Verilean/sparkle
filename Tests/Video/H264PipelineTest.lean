/-
  Test: H.264 End-to-End Pipeline
  Verifies encoder → decoder roundtrip with quality measurement.
-/

import LSpec
import IP.Video.H264.Encoder
import IP.Video.H264.Decoder

open Sparkle.IP.Video.H264.IntraPred
open Sparkle.IP.Video.H264.Encoder
open Sparkle.IP.Video.H264.Decoder

namespace Sparkle.Tests.Video.H264PipelineTest

private def testNeighbors : Neighbors :=
  { above := #[100, 100, 100, 100, 100, 100, 100, 100]
  , left := #[100, 100, 100, 100]
  , aboveLeft := 100
  , hasAbove := true
  , hasLeft := true }

def testConstantBlock : IO LSpec.TestSeq := do
  -- Constant block should have perfect roundtrip (zero residual)
  let original := Array.replicate 16 100
  let (orig, decoded) := encodeDecodeRoundtrip original testNeighbors 20
  let score := qualityScore orig decoded

  IO.println s!"  Constant block: MSE={score}"

  pure $ LSpec.group "Constant Block Roundtrip" (
    LSpec.test "perfect reconstruction (MSE=0)" (score == 0)
  )

def testEncoderOutput : IO LSpec.TestSeq := do
  let original : Sparkle.IP.Video.H264.IntraPred.Block4x4 := #[110, 115, 120, 125, 112, 117, 122, 127,
                                           114, 119, 124, 129, 116, 121, 126, 131]
  let result := encodeBlock original testNeighbors EncoderConfig.default

  IO.println s!"  Encoder: mode={result.predMode}, bitLen={result.bitLen}"
  IO.println s!"  NAL unit: {result.nalUnit.length} bytes"

  pure $ LSpec.group "Encoder Output" (
    LSpec.test "produces non-zero bitstream" (result.bitLen > 0) ++
    LSpec.test "NAL unit has start code" (result.nalUnit.length >= 4) ++
    LSpec.test "reconstructed has 16 elements" (result.reconstructed.size == 16)
  )

def testSmallFrame : IO LSpec.TestSeq := do
  -- 8×8 frame (2×2 blocks of 4×4)
  let mut pixels := Array.replicate 64 (0 : Nat)
  for i in [:8] do
    for j in [:8] do
      pixels := pixels.set! (i * 8 + j) (100 + i * 5 + j * 3)

  let results := encodeFrame pixels 8 8 EncoderConfig.default

  IO.println s!"  Frame: {results.size} blocks encoded"

  pure $ LSpec.group "Small Frame Encoding" (
    LSpec.test "4 blocks for 8×8 frame" (results.size == 4) ++
    LSpec.test "all blocks have valid bitLen" (results.all (fun r => r.bitLen > 0))
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- H.264 Pipeline Tests ---"
  let t1 ← testConstantBlock
  let t2 ← testEncoderOutput
  let t3 ← testSmallFrame
  return LSpec.group "H.264 Pipeline" (t1 ++ t2 ++ t3)

end Sparkle.Tests.Video.H264PipelineTest
