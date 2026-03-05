/-
  H.264 Baseline Decoder — Top-Level Pipeline

  Decoder pipeline for a single 4×4 block (I-frame only):
    Bitstream → NAL Parse → CAVLC Decode → Dequant → IDCT → + Intra Pred → Pixels

  This module provides:
  1. Pure Lean decoding function (for simulation and golden comparison)
  2. Block-level pipeline that chains all stages

  Reference: ITU-T H.264 Section 7, 8
-/

import IP.Video.H264.IntraPred
import IP.Video.H264.DCT
import IP.Video.H264.Quant
import IP.Video.H264.CAVLCDecode
import IP.Video.H264.NAL

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.Decoder

open Sparkle.IP.Video.H264.IntraPred
open Sparkle.IP.Video.H264.DCT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.CAVLCDecode
open Sparkle.IP.Video.H264.NAL

-- ============================================================================
-- Decoder configuration
-- ============================================================================

structure DecoderConfig where
  qp : Nat  -- Quantization parameter (must match encoder)
  deriving Repr

-- ============================================================================
-- Decoder result
-- ============================================================================

structure DecoderResult where
  pixels : IntraPred.Block4x4          -- Decoded pixel values
  quantLevels : Array Int    -- Decoded quantized levels
  dequantCoeffs : Array Int  -- Dequantized coefficients
  idctResidual : Array Int   -- IDCT output (decoded residual)
  deriving Repr

-- ============================================================================
-- Pure decoder pipeline (single 4×4 block)
-- ============================================================================

/-- Decode a single 4×4 block from CAVLC bitstream.
    Input: bitstream data, prediction mode + neighbors, QP.
    Output: DecoderResult with decoded pixels. -/
def decodeBlock (bitstream : BitVec 64) (bitLen : Nat)
    (predMode : Nat) (neighbors : Neighbors) (cfg : DecoderConfig)
    : DecoderResult :=
  -- 1. CAVLC decode: bitstream → quantized levels
  let quantLevels := cavlcDecode bitstream bitLen

  -- 2. Dequantize
  let dequantCoeffs := dequantizeBlock quantLevels cfg.qp

  -- 3. Inverse DCT → decoded residual
  let idctResidual := inverseDCT dequantCoeffs

  -- 4. Intra prediction (same mode as encoder)
  let predicted := predict predMode neighbors

  -- 5. Reconstruct: predicted + decoded_residual
  let pixels := reconstruct predicted idctResidual

  { pixels, quantLevels, dequantCoeffs, idctResidual }

/-- Decode from NAL unit (includes NAL parsing step).
    Input: NAL unit bytes, prediction mode + neighbors, QP.
    Output: DecoderResult with decoded pixels. -/
def decodeFromNAL (nalUnit : List (BitVec 8))
    (predMode : Nat) (neighbors : Neighbors) (cfg : DecoderConfig)
    : DecoderResult :=
  -- 1. NAL parse: remove start code + emulation prevention
  let payload := nalParsePayload nalUnit

  -- 2. Reconstruct bitstream from payload bytes
  let (bitstream, bitLen) := Id.run do
    let mut buf : BitVec 32 := 0#32
    let mut pos := 0
    for byte in payload do
      let byte32 := BitVec.zeroExtend 32 byte
      if pos + 8 <= 32 then
        buf := buf ||| (byte32 <<< (24 - pos))
        pos := pos + 8
    (buf, pos)

  -- 3. Decode block
  decodeBlock bitstream bitLen predMode neighbors cfg

-- ============================================================================
-- End-to-end encode-decode pipeline
-- ============================================================================

/-- Encode a block, then decode it, and return both results for comparison.
    This is the main verification function. -/
def encodeDecodeRoundtrip (original : IntraPred.Block4x4) (neighbors : Neighbors) (qp : Nat)
    : IntraPred.Block4x4 × IntraPred.Block4x4 :=
  -- Encode
  let predMode := bestMode original neighbors
  let predicted := predict predMode neighbors
  let residual := computeResidual original predicted
  let dctCoeffs := forwardDCT residual
  let quantLevels := quantizeBlock dctCoeffs qp
  let (bitstream, bitLen) := CAVLC.cavlcEncodeFull quantLevels

  -- Decode (using same prediction mode and neighbors)
  let decodedLevels := cavlcDecode bitstream bitLen
  let dequantCoeffs := dequantizeBlock decodedLevels qp
  let idctResidual := inverseDCT dequantCoeffs
  let decoded := reconstruct predicted idctResidual

  (original, decoded)

-- ============================================================================
-- PSNR computation for quality measurement
-- ============================================================================

/-- Compute Mean Squared Error between two blocks -/
def computeMSE (a b : IntraPred.Block4x4) : Nat := Id.run do
  let mut sumSqErr : Nat := 0
  for i in [:16] do
    let va := if h : i < a.size then a[i] else 0
    let vb := if h : i < b.size then b[i] else 0
    let diff := if va >= vb then va - vb else vb - va
    sumSqErr := sumSqErr + diff * diff
  sumSqErr / 16

/-- Compute approximate PSNR in integer form: 10 * log10(255^2 / MSE).
    Returns 0 for perfect match, otherwise MSE value for comparison. -/
def qualityScore (a b : IntraPred.Block4x4) : Nat :=
  let mse := computeMSE a b
  if mse == 0 then 0 else mse  -- 0 = perfect, higher = worse

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

  let (orig, decoded) := encodeDecodeRoundtrip original neighbors 20
  let score := qualityScore orig decoded

  IO.println s!"Original:    {orig}"
  IO.println s!"Decoded:     {decoded}"
  IO.println s!"Quality (MSE, 0=perfect): {score}"

  -- Test with all-zero residual (DC prediction should be near-perfect)
  let allSame : IntraPred.Block4x4 := Array.replicate 16 100
  let (orig2, decoded2) := encodeDecodeRoundtrip allSame neighbors 20
  let score2 := qualityScore orig2 decoded2
  IO.println s!"All-same original: {orig2}"
  IO.println s!"All-same decoded:  {decoded2}"
  IO.println s!"All-same quality (MSE, 0=perfect): {score2}"

end Sparkle.IP.Video.H264.Decoder
