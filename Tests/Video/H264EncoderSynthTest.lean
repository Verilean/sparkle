/-
  H.264 Encoder Pipeline — Synthesizable Module Tests

  Tests the pure reference functions for each encoder sub-module:
  1. Forward DCT: residual → DCT coefficients
  2. Forward Quant: DCT coefficients → quantized levels (QP=20)
  3. Encoder Pipeline: residual → DCT → quant

  Each test compares the reference function output with expected values.

  Usage:
    import Tests.Video.H264EncoderSynthTest
    (runs as part of `lake test`)
-/

import IP.Video.H264.ForwardDCTSynth
import IP.Video.H264.QuantSynth
import IP.Video.H264.EncoderSynth
import IP.Video.H264.DecoderSynth
import IP.Video.H264.DCT
import IP.Video.H264.Quant
import LSpec

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.Tests.Video.H264EncoderSynthTest

open LSpec
open Sparkle.IP.Video.H264.ForwardDCTSynth
open Sparkle.IP.Video.H264.QuantSynth
open Sparkle.IP.Video.H264.EncoderSynth
open Sparkle.IP.Video.H264.DecoderSynth
open Sparkle.IP.Video.H264.DCT
open Sparkle.IP.Video.H264.Quant

-- ============================================================================
-- Test data
-- ============================================================================

/-- Test input block: sequential 1..16 -/
private def testBlock : Array Int := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

/-- Test original pixels for encoder pipeline -/
private def testOriginal : Array Nat := #[129, 130, 131, 132, 133, 134, 135, 136,
                                           137, 138, 139, 140, 141, 142, 143, 144]

/-- Test predicted pixels (DC prediction with value 128) -/
private def testPredicted : Array Nat := Array.replicate 16 128

-- ============================================================================
-- Forward DCT reference tests
-- ============================================================================

def testFwdDCTRef : TestSeq :=
  let result := fwdDCTRef testBlock
  -- Known golden: DC coefficient = 136 (sum of 1..16 = 136)
  let dc := if h : 0 < result.size then result[0] else 0
  test "result has 16 elements" (result.size == 16) $
  test "DC coefficient = 136" (dc == 136)

def testFwdDCTMatchesPure : TestSeq :=
  let synth := fwdDCTRef testBlock
  let pure := forwardDCT testBlock
  test "fwdDCTRef matches DCT.forwardDCT" (synth == pure)

def testFwdDCTZeroBlock : TestSeq :=
  let zeroBlock : Array Int := Array.replicate 16 0
  let result := fwdDCTRef zeroBlock
  let allZero := result.all (· == 0)
  test "zero block → all-zero DCT" allZero

-- ============================================================================
-- Forward quant reference tests
-- ============================================================================

def testQuantRef : TestSeq :=
  let dctCoeffs := fwdDCTRef testBlock
  let result := quantBlockRef dctCoeffs
  -- DC=136 at pos 0: level = (136 * 10082 + 87381) >> 18 = (1371152 + 87381) >> 18
  --                         = 1458533 >> 18 = 5 (approximately)
  let dc := if h : 0 < result.size then result[0] else 0
  test "result has 16 elements" (result.size == 16) $
  test "DC level is positive" (dc > 0)

def testQuantMatchesPure : TestSeq :=
  let dctCoeffs := forwardDCT testBlock
  let synth := quantBlockRef dctCoeffs
  let pure := quantizeBlock dctCoeffs 20
  test "quantBlockRef matches Quant.quantizeBlock at QP=20" (synth == pure)

def testQuantZeroBlock : TestSeq :=
  let zeroCoeffs : Array Int := Array.replicate 16 0
  let result := quantBlockRef zeroCoeffs
  let allZero := result.all (· == 0)
  test "zero coeffs → all-zero quant" allZero

-- ============================================================================
-- Full pipeline reference test
-- ============================================================================

def testPipelineRef : TestSeq :=
  let result := encoderPipelineRef testOriginal testPredicted
  -- Step-by-step computation
  let residual := residualRef testOriginal testPredicted
  let dctCoeffs := fwdDCTRef residual
  let expected := quantBlockRef dctCoeffs
  test "pipeline matches step-by-step" (result == expected) $
  test "result has 16 elements" (result.size == 16)

-- ============================================================================
-- Encoder → Decoder roundtrip test
-- ============================================================================

def testRoundtrip : TestSeq :=
  -- Encode: original, predicted → quantized levels
  let quantLevels := encoderPipelineRef testOriginal testPredicted
  -- Decode: quantized levels, predicted → reconstructed pixels
  let decoded := decoderPipelineRef quantLevels testPredicted
  -- All decoded pixels should be in [0, 255]
  let allInRange := decoded.all (· <= 255)
  let nonUniform := decoded.toList.eraseDups.length > 1
  test "roundtrip decoded has 16 elements" (decoded.size == 16) $
  test "all decoded values in [0, 255]" allInRange $
  test "decoded result is not uniform" nonUniform

-- ============================================================================
-- All tests
-- ============================================================================

def allTests : IO TestSeq := do
  IO.println "--- H.264 Encoder Synth Tests ---"
  return group "H.264 Encoder Synth" (
    group "Forward DCT Reference" testFwdDCTRef ++
    group "Forward DCT vs Pure" testFwdDCTMatchesPure ++
    group "Forward DCT Zero" testFwdDCTZeroBlock ++
    group "Quant Reference" testQuantRef ++
    group "Quant vs Pure" testQuantMatchesPure ++
    group "Quant Zero" testQuantZeroBlock ++
    group "Pipeline Reference" testPipelineRef ++
    group "Encoder-Decoder Roundtrip" testRoundtrip
  )

end Sparkle.Tests.Video.H264EncoderSynthTest
