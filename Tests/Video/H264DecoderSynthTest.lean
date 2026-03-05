/-
  H.264 Decoder Pipeline — Synthesizable Module Tests

  Tests the pure reference functions for each decoder sub-module:
  1. Dequant: quantized levels → dequantized coefficients (QP=20)
  2. IDCT: dequantized coefficients → decoded residual
  3. Reconstruct: predicted + residual → clamped pixels

  Each test compares the reference function output with expected values.

  Usage:
    import Tests.Video.H264DecoderSynthTest
    (runs as part of `lake test`)
-/

import IP.Video.H264.DequantSynth
import IP.Video.H264.IDCTSynth
import IP.Video.H264.ReconstructSynth
import IP.Video.H264.DecoderSynth
import LSpec

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.Tests.Video.H264DecoderSynthTest

open LSpec
open Sparkle.IP.Video.H264.DequantSynth
open Sparkle.IP.Video.H264.IDCTSynth
open Sparkle.IP.Video.H264.ReconstructSynth
open Sparkle.IP.Video.H264.DecoderSynth

-- ============================================================================
-- Test data
-- ============================================================================

/-- Test quantized levels (from forward DCT of sequential block 1..16, then quantize at QP=20) -/
private def testQuantLevels : Array Int := #[10, -2, 0, 0, -8, 0, 0, 0,
                                               0, 0, 0, 0, -1, 0, 0, 0]

/-- Test predicted pixels (DC prediction with value 128) -/
private def testPredicted : Array Nat := Array.replicate 16 128

-- ============================================================================
-- Dequant reference tests
-- ============================================================================

def testDequantRef : TestSeq :=
  let result := dequantBlockRef testQuantLevels
  -- pos 0: level=10, V=13*8=104 → 1040
  -- pos 1: level=-2, V=16*8=128 → -256
  -- pos 4: level=-8, V=16*8=128 → -1024
  -- pos 12: level=-1, V=16*8=128 → -128
  let r0 := if h : 0 < result.size then result[0] else 0
  let r1 := if h : 1 < result.size then result[1] else 0
  let r4 := if h : 4 < result.size then result[4] else 0
  let r12 := if h : 12 < result.size then result[12] else 0
  test "pos0 = 10*104 = 1040" (r0 == 1040) $
  test "pos1 = -2*128 = -256" (r1 == -256) $
  test "pos4 = -8*128 = -1024" (r4 == -1024) $
  test "pos12 = -1*128 = -128" (r12 == -128) $
  test "result has 16 elements" (result.size == 16)

-- ============================================================================
-- IDCT reference tests
-- ============================================================================

def testIDCTRef : TestSeq :=
  let dequantized := dequantBlockRef testQuantLevels
  let result := idctRef dequantized
  let nonZero := result.foldl (fun acc v => if v != 0 then acc + 1 else acc) 0
  test "result has 16 elements" (result.size == 16) $
  test "has non-zero values" (nonZero > 0)

-- ============================================================================
-- Reconstruct reference tests
-- ============================================================================

def testReconstructRef : TestSeq :=
  let dequantized := dequantBlockRef testQuantLevels
  let residual := idctRef dequantized
  let result := reconstructRef testPredicted residual
  let allInRange := result.all (· <= 255)
  let nonUniform := result.toList.eraseDups.length > 1
  test "result has 16 elements" (result.size == 16) $
  test "all values in [0, 255]" allInRange $
  test "result is not uniform" nonUniform

-- ============================================================================
-- Full pipeline reference test
-- ============================================================================

def testPipelineRef : TestSeq :=
  let result := decoderPipelineRef testQuantLevels testPredicted
  let dequantized := dequantBlockRef testQuantLevels
  let residual := idctRef dequantized
  let expected := reconstructRef testPredicted residual
  test "pipeline matches step-by-step" (result == expected) $
  test "result has 16 elements" (result.size == 16)

-- ============================================================================
-- Clamp edge cases
-- ============================================================================

def testClampEdgeCases : TestSeq :=
  let negResidual : Array Int := Array.replicate 16 (-200)
  let r1 := reconstructRef testPredicted negResidual
  let allZero := r1.all (· == 0)
  let posResidual : Array Int := Array.replicate 16 200
  let r2 := reconstructRef testPredicted posResidual
  let all255 := r2.all (· == 255)
  test "large negative residual clamps to 0" allZero $
  test "large positive residual clamps to 255" all255

-- ============================================================================
-- Zero block test
-- ============================================================================

def testZeroBlock : TestSeq :=
  let zeroLevels : Array Int := Array.replicate 16 0
  let result := decoderPipelineRef zeroLevels testPredicted
  let allPred := result.all (· == 128)
  test "zero levels → pure prediction" allPred

-- ============================================================================
-- All tests
-- ============================================================================

def allTests : IO TestSeq := do
  IO.println "--- H.264 Decoder Synth Tests ---"
  return group "H.264 Decoder Synth" (
    group "Dequant Reference" testDequantRef ++
    group "IDCT Reference" testIDCTRef ++
    group "Reconstruct Reference" testReconstructRef ++
    group "Pipeline Reference" testPipelineRef ++
    group "Clamp Edge Cases" testClampEdgeCases ++
    group "Zero Block" testZeroBlock
  )

end Sparkle.Tests.Video.H264DecoderSynthTest
