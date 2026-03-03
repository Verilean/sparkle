/-
  H.264 Baseline Encoder — Top-Level Pipeline

  Encoder pipeline for a single 4×4 block (I-frame only):
    Input pixels → Intra Pred → Residual → DCT → Quant → CAVLC → NAL → Bitstream

  Reconstruction path (for reference frame):
    Quantized → Dequant → IDCT → + Predicted → Reconstructed

  This module provides:
  1. Pure Lean encoding function (for simulation and golden comparison)
  2. Block-level pipeline that chains all stages

  Reference: ITU-T H.264 Section 7, 8
-/

import IP.Video.H264.IntraPred
import IP.Video.H264.DCT
import IP.Video.H264.Quant
import IP.Video.H264.CAVLC
import IP.Video.H264.NAL

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.Encoder

open Sparkle.IP.Video.H264.IntraPred
open Sparkle.IP.Video.H264.DCT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.CAVLC
open Sparkle.IP.Video.H264.NAL

-- ============================================================================
-- Encoder configuration
-- ============================================================================

structure EncoderConfig where
  qp : Nat        -- Quantization parameter (0-51)
  nalRefIdc : BitVec 8  -- NAL reference IDC
  nalType : BitVec 8    -- NAL unit type
  deriving Repr

def EncoderConfig.default : EncoderConfig :=
  { qp := 20, nalRefIdc := 3#8, nalType := NAL_SLICE_IDR }

-- ============================================================================
-- Encoder result
-- ============================================================================

structure EncoderResult where
  bitstream : BitVec 32       -- CAVLC encoded bitstream
  bitLen : Nat                -- Number of valid bits
  nalUnit : List (BitVec 8)   -- NAL-packed bitstream
  reconstructed : IntraPred.Block4x4    -- Reconstructed pixels (for reference)
  predMode : Nat              -- Selected prediction mode
  residual : Array Int        -- Residual before DCT
  dctCoeffs : Array Int       -- DCT coefficients
  quantLevels : Array Int     -- Quantized levels
  deriving Repr

-- ============================================================================
-- Pure encoder pipeline (single 4×4 block)
-- ============================================================================

/-- Encode a single 4×4 pixel block.
    Input: 16 pixel values (0-255), neighbor pixels for prediction.
    Output: EncoderResult with bitstream, reconstructed block, etc. -/
def encodeBlock (original : IntraPred.Block4x4) (neighbors : Neighbors) (cfg : EncoderConfig)
    : EncoderResult :=
  -- 1. Intra prediction: choose best mode and compute prediction
  let predMode := bestMode original neighbors
  let predicted := predict predMode neighbors

  -- 2. Compute residual: original - predicted
  let residual := computeResidual original predicted

  -- 3. Forward DCT on residual
  let dctCoeffs := forwardDCT residual

  -- 4. Quantization
  let quantLevels := quantizeBlock dctCoeffs cfg.qp

  -- 5. CAVLC encoding (uses raster-order input)
  let (bitstream, bitLen) := cavlcEncodeFull quantLevels

  -- 6. NAL packing
  -- Convert bitstream to bytes for NAL packing
  let bitstreamBytes := Id.run do
    let mut bytes : List (BitVec 8) := []
    let numBytes := (bitLen + 7) / 8
    for i in [:numBytes] do
      let shift := 24 - i * 8
      let byte := (bitstream >>> shift) &&& 0xFF#32
      bytes := bytes ++ [BitVec.extractLsb' 0 8 byte]
    bytes
  let nalUnit := nalPack bitstreamBytes cfg.nalType cfg.nalRefIdc

  -- 7. Reconstruction path: dequant → IDCT → + predicted → clamp
  let dequantLevels := dequantizeBlock quantLevels cfg.qp
  let idctResult := inverseDCT dequantLevels
  let reconstructed := reconstruct predicted idctResult

  { bitstream, bitLen, nalUnit, reconstructed, predMode,
    residual, dctCoeffs, quantLevels }

-- ============================================================================
-- Frame-level encoder (processes all 4×4 blocks in raster order)
-- ============================================================================

/-- Encode a full frame as a sequence of 4×4 blocks.
    Frame is stored as a flat array of pixels, width×height.
    Returns (encoded blocks, reconstructed frame for reference). -/
def encodeFrame (pixels : Array Nat) (width height : Nat) (cfg : EncoderConfig)
    : Array EncoderResult := Id.run do
  let blocksW := width / 4
  let blocksH := height / 4
  let mut results : Array EncoderResult := #[]
  let mut reconFrame := Array.replicate (width * height) 0

  for by_ in [:blocksH] do
    for bx in [:blocksW] do
      -- Extract 4×4 block
      let mut block := Array.replicate 16 0
      for i in [:4] do
        for j in [:4] do
          let py := by_ * 4 + i
          let px := bx * 4 + j
          let idx := py * width + px
          if h : idx < pixels.size then
            block := block.set! (i * 4 + j) pixels[idx]

      -- Build neighbor pixels from reconstructed frame
      let mut abovePixels := Array.replicate 8 128
      let mut leftPixels := Array.replicate 4 128
      let mut aboveLeftPx := 128
      let hasAbove := by_ > 0
      let hasLeft := bx > 0

      if hasAbove then
        for j in [:8] do
          let px := bx * 4 + j
          let py := by_ * 4 - 1
          let idx := py * width + px
          if h : idx < reconFrame.size then
            abovePixels := abovePixels.set! j reconFrame[idx]

      if hasLeft then
        for i in [:4] do
          let py := by_ * 4 + i
          let px := bx * 4 - 1
          let idx := py * width + px
          if h : idx < reconFrame.size then
            leftPixels := leftPixels.set! i reconFrame[idx]

      if hasAbove && hasLeft then
        let idx := (by_ * 4 - 1) * width + (bx * 4 - 1)
        if h : idx < reconFrame.size then
          aboveLeftPx := reconFrame[idx]

      let neighbors : Neighbors :=
        { above := abovePixels
        , left := leftPixels
        , aboveLeft := aboveLeftPx
        , hasAbove := hasAbove
        , hasLeft := hasLeft }

      -- Encode block
      let result := encodeBlock block neighbors cfg
      results := results.push result

      -- Write reconstructed pixels back to frame
      for i in [:4] do
        for j in [:4] do
          let py := by_ * 4 + i
          let px := bx * 4 + j
          let idx := py * width + px
          if idx < reconFrame.size then
            let blockIdx := i * 4 + j
            reconFrame := reconFrame.set! idx (result.reconstructed[blockIdx]!)

  results

-- ============================================================================
-- Verification
-- ============================================================================

#eval do
  let neighbors : Neighbors :=
    { above := #[100, 100, 100, 100, 100, 100, 100, 100]
    , left := #[100, 100, 100, 100]
    , aboveLeft := 100
    , hasAbove := true
    , hasLeft := true }

  let original : IntraPred.Block4x4 := #[110, 115, 120, 125, 112, 117, 122, 127,
                                 114, 119, 124, 129, 116, 121, 126, 131]

  let result := encodeBlock original neighbors EncoderConfig.default

  IO.println s!"Prediction mode: {result.predMode}"
  IO.println s!"Residual: {result.residual}"
  IO.println s!"DCT coeffs: {result.dctCoeffs}"
  IO.println s!"Quant levels: {result.quantLevels}"
  IO.println s!"Bitstream: 0x{String.ofList (Nat.toDigits 16 result.bitstream.toNat)} ({result.bitLen} bits)"
  IO.println s!"Reconstructed: {result.reconstructed}"
  IO.println s!"NAL unit length: {result.nalUnit.length} bytes"

end Sparkle.IP.Video.H264.Encoder
