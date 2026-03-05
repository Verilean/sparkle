/-
  H.264 Annex-B Bitstream End-to-End Test

  Produces a valid .h264 file from a 16×16 test image:
  1. Compute DC prediction (all 128 for no-neighbor case)
  2. For each 4×4 block (4 blocks):
     a. Run encoderPipeline JIT → get quantized levels
     b. Run cavlcSynthModule JIT → get CAVLC bitstream
  3. Assemble NAL unit: SPS + PPS + slice header + CAVLC data
  4. Write to IP/Video/H264/gen/test_output.h264
  5. Verify bitstream bytes against pure Lean reference

  Usage:
    lake exe h264-bitstream-test
-/

import Sparkle.Core.JIT
import IP.Video.H264.Quant
import IP.Video.H264.EncoderSynth
import IP.Video.H264.CAVLCSynth
import IP.Video.H264.VLCTables
import IP.Video.H264.CAVLC
import IP.Video.H264.SPSPPSData
import IP.Video.H264.Encoder
import IP.Video.H264.NAL

open Sparkle.Core.JIT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.EncoderSynth
open Sparkle.IP.Video.H264.CAVLCSynth
open Sparkle.IP.Video.H264.VLCTables
open Sparkle.IP.Video.H264.CAVLC
open Sparkle.IP.Video.H264.SPSPPSData
open Sparkle.IP.Video.H264.Encoder
open Sparkle.IP.Video.H264.NAL

/-- Resolve a wire index by name, throwing if not found -/
private def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

/-- Convert signed Int to unsigned 16-bit representation (2's complement) -/
private def intToU16 (v : Int) : UInt32 :=
  if v < 0 then (65536 + v).toNat.toUInt32
  else v.toNat.toUInt32

/-- Convert unsigned 16-bit value back to signed Int -/
private def u16ToInt (val : UInt32) : Int :=
  if val.toNat >= 32768 then (val.toNat : Int) - 65536
  else (val.toNat : Int)

-- ============================================================================
-- Test image: 16×16 constant gradient
-- ============================================================================

/-- Generate a 16×16 test image with gradient pattern -/
def testImage16x16 : Array Nat := Id.run do
  let mut pixels : Array Nat := #[]
  for row in [:16] do
    for col in [:16] do
      -- Gradient: value increases with row and column
      let val := 100 + row * 4 + col
      pixels := pixels.push (min val 255)
  pixels

/-- Extract a 4×4 block from 16×16 image at block position (bx, by) -/
def extractBlock (image : Array Nat) (bx by_ : Nat) : Array Nat := Id.run do
  let mut block : Array Nat := #[]
  for i in [:4] do
    for j in [:4] do
      let idx := (by_ * 4 + i) * 16 + (bx * 4 + j)
      let val := if h : idx < image.size then image[idx] else 128
      block := block.push val
  block

-- ============================================================================
-- End-to-end test
-- ============================================================================

def testBitstreamGeneration : IO Bool := do
  IO.println "\n=== H.264 Annex-B Bitstream Generation Test ==="

  let image := testImage16x16
  IO.println s!"  Image size: {image.size} pixels (16×16)"

  -- Prediction: DC prediction with value 128 (no neighbors)
  let predicted : Array Nat := Array.replicate 16 128

  -- Step 1: Encode each 4×4 block using encoder pipeline JIT
  IO.println "  Compiling encoder pipeline..."
  let encHandle ← JIT.compileAndLoad "IP/Video/H264/gen/encoder_pipeline_jit.cpp"
  let encDoneIdx ← resolveWire encHandle "_gen_done"

  -- Set QP=20
  let (mf0, mf1, mf2, f, qbits) := quantParams 20
  JIT.setInput encHandle 7 mf0.toUInt64
  JIT.setInput encHandle 8 mf1.toUInt64
  JIT.setInput encHandle 9 mf2.toUInt64
  JIT.setInput encHandle 10 f.toUInt64
  JIT.setInput encHandle 11 qbits.toUInt64

  let mut allQuantLevels : Array (Array Int) := #[]

  -- Process 4 blocks in raster order (2×2 blocks for simplicity)
  -- For a 16×16 image, there are 4×4 = 16 blocks of 4×4
  -- But for MVP, encode just 4 blocks (first row)
  for blockIdx in [:4] do
    let bx := blockIdx % 4
    let by_ := blockIdx / 4
    let block := extractBlock image bx by_

    -- Reset encoder
    JIT.reset encHandle

    -- Load original pixels into memIdx=0
    for i in [:16] do
      let val := if h : i < block.size then block[i] else 0
      JIT.setMem encHandle 0 i.toUInt32 val.toUInt32
    -- Load prediction into memIdx=1
    for i in [:16] do
      let val := if h : i < predicted.size then predicted[i] else 0
      JIT.setMem encHandle 1 i.toUInt32 val.toUInt32

    -- Re-set QP after reset
    JIT.setInput encHandle 7 mf0.toUInt64
    JIT.setInput encHandle 8 mf1.toUInt64
    JIT.setInput encHandle 9 mf2.toUInt64
    JIT.setInput encHandle 10 f.toUInt64
    JIT.setInput encHandle 11 qbits.toUInt64

    -- Assert start
    JIT.setInput encHandle 0 1
    JIT.eval encHandle
    JIT.tick encHandle
    JIT.setInput encHandle 0 0

    -- Run until done
    for _ in [:200] do
      JIT.eval encHandle
      let doneVal ← JIT.getWire encHandle encDoneIdx
      if doneVal != 0 then break
      JIT.tick encHandle

    -- Read quantized levels
    let mut levels : Array Int := #[]
    for i in [:16] do
      let val ← JIT.getMem encHandle 6 i.toUInt32
      levels := levels.push (u16ToInt val)

    IO.println s!"  Block {blockIdx}: levels = {levels}"
    allQuantLevels := allQuantLevels.push levels

  JIT.destroy encHandle

  -- Step 2: CAVLC encode each block
  IO.println "  Compiling CAVLC synth..."
  let cavlcHandle ← JIT.compileAndLoad "IP/Video/H264/gen/cavlc_synth_jit.cpp"
  let cavlcDoneIdx ← resolveWire cavlcHandle "_gen_done"

  -- Load VLC tables into correct JIT memory indices:
  --   memIdx 0 = zigzag table, memIdx 2 = coeff_token, memIdx 3 = total_zeros, memIdx 4 = run_before
  let zzTable := zigzagTable
  for i in [:zzTable.size] do
    if h : i < zzTable.size then
      JIT.setMem cavlcHandle 0 i.toUInt32 zzTable[i]

  let ctTable := buildCoeffTokenTable
  for i in [:ctTable.size] do
    if h : i < ctTable.size then
      JIT.setMem cavlcHandle 2 i.toUInt32 ctTable[i]

  let tzTable := buildTotalZerosTable
  for i in [:tzTable.size] do
    if h : i < tzTable.size then
      JIT.setMem cavlcHandle 3 i.toUInt32 tzTable[i]

  let rbTable := buildRunBeforeTable
  for i in [:rbTable.size] do
    if h : i < rbTable.size then
      JIT.setMem cavlcHandle 4 i.toUInt32 rbTable[i]

  let mut allBitstreams : Array (BitVec 32 × Nat) := #[]

  for blockIdx in [:4] do
    if h : blockIdx < allQuantLevels.size then
      let levels := allQuantLevels[blockIdx]

      -- Reset CAVLC encoder
      JIT.reset cavlcHandle

      -- Reload VLC tables after reset (correct memory indices)
      for i in [:zzTable.size] do
        if h2 : i < zzTable.size then
          JIT.setMem cavlcHandle 0 i.toUInt32 zzTable[i]
      for i in [:ctTable.size] do
        if h2 : i < ctTable.size then
          JIT.setMem cavlcHandle 2 i.toUInt32 ctTable[i]
      for i in [:tzTable.size] do
        if h2 : i < tzTable.size then
          JIT.setMem cavlcHandle 3 i.toUInt32 tzTable[i]
      for i in [:rbTable.size] do
        if h2 : i < rbTable.size then
          JIT.setMem cavlcHandle 4 i.toUInt32 rbTable[i]

      -- Load coefficients into memIdx 1
      for i in [:16] do
        let val := if h2 : i < levels.size then levels[i] else 0
        JIT.setMem cavlcHandle 1 i.toUInt32 (intToU16 val)

      -- Assert start, nCTableSelect=0 (port 1)
      JIT.setInput cavlcHandle 0 1  -- start
      JIT.setInput cavlcHandle 1 0  -- nCTableSelect = 0
      JIT.eval cavlcHandle
      JIT.tick cavlcHandle
      JIT.setInput cavlcHandle 0 0

      -- Run until done
      for _ in [:200] do
        JIT.eval cavlcHandle
        let doneVal ← JIT.getWire cavlcHandle cavlcDoneIdx
        if doneVal != 0 then break
        JIT.tick cavlcHandle

      -- Read bitstream
      let bsIdx ← resolveWire cavlcHandle "_gen_bitBuffer"
      let bpIdx ← resolveWire cavlcHandle "_gen_bitPos"
      let bsData ← JIT.getWire cavlcHandle bsIdx
      let bpData ← JIT.getWire cavlcHandle bpIdx

      -- Compare with reference
      let (refBits, refLen) := cavlcEncodeFull levels
      IO.println s!"  Block {blockIdx} CAVLC: 0x{String.ofList (Nat.toDigits 16 bsData.toNat)} ({bpData} bits)"
      IO.println s!"    Reference:    0x{String.ofList (Nat.toDigits 16 refBits.toNat)} ({refLen} bits)"

      allBitstreams := allBitstreams.push (BitVec.ofNat 32 bsData.toNat, bpData.toNat)

  JIT.destroy cavlcHandle

  -- Step 3: Assemble Annex-B bitstream
  IO.println "  Assembling Annex-B bitstream..."

  let mut outputBytes : Array UInt8 := #[]

  -- Write SPS NAL unit
  for byte in spsNALUnit do
    outputBytes := outputBytes.push byte.toNat.toUInt8

  -- Write PPS NAL unit
  for byte in ppsNALUnit do
    outputBytes := outputBytes.push byte.toNat.toUInt8

  -- Write IDR slice NAL unit header
  for byte in idrSliceNALHeader do
    outputBytes := outputBytes.push byte.toNat.toUInt8

  -- Write slice header bits
  -- Combine slice header + MB header + CAVLC data into byte-aligned payload
  let mut bitAccum : Nat := 0
  let mut bitCount : Nat := 0

  -- Pack slice header bits
  for byte in sliceHeaderBits do
    bitAccum := (bitAccum <<< 8) ||| byte.toNat
    bitCount := bitCount + 8

  -- Pack MB header bits
  for byte in mbHeaderBits do
    bitAccum := (bitAccum <<< 8) ||| byte.toNat
    bitCount := bitCount + 8

  -- Note: sliceHeaderBitLen + mbHeaderBitLen = 16 + 20 = 36 bits
  -- We've loaded 5 bytes (40 bits), so 4 extra padding bits
  let headerBitLen := sliceHeaderBitLen + mbHeaderBitLen

  -- Pack CAVLC bitstreams for each block
  -- For simplicity, we'll pack the first 4 blocks
  let mut cavlcTotalBits := 0
  for entry in allBitstreams do
    let (bs, blen) := entry
    cavlcTotalBits := cavlcTotalBits + blen
    -- Shift bitstream MSB-aligned into accumulator
    bitAccum := (bitAccum <<< blen) ||| (bs.toNat >>> (32 - blen))
    bitCount := bitCount + blen

  -- Byte-align with rbsp_stop_one_bit + trailing zeros
  let totalPayloadBits := headerBitLen + cavlcTotalBits
  let alignBits := (8 - (totalPayloadBits % 8)) % 8
  if alignBits > 0 then
    -- Add stop bit (1) + trailing zeros
    bitAccum := (bitAccum <<< alignBits) ||| (1 <<< (alignBits - 1))
    bitCount := bitCount + alignBits

  -- Flush bit accumulator to bytes
  let numBytes := bitCount / 8
  for i in [:numBytes] do
    let shift := bitCount - (i + 1) * 8
    let byte := (bitAccum >>> shift) &&& 0xFF
    outputBytes := outputBytes.push byte.toUInt8

  IO.println s!"  Total output: {outputBytes.size} bytes"
  IO.println s!"  Header bits: {headerBitLen}, CAVLC bits: {cavlcTotalBits}, align: {alignBits}"

  -- Step 4: Write .h264 file
  let outputPath := "IP/Video/H264/gen/test_output.h264"
  let byteArray := ByteArray.mk outputBytes
  IO.FS.writeBinFile outputPath byteArray
  IO.println s!"  Written to {outputPath}"

  -- Step 5: Verify CAVLC outputs match pure reference
  let mut pass := true
  for blockIdx in [:allBitstreams.size] do
    if h : blockIdx < allBitstreams.size then
      if h2 : blockIdx < allQuantLevels.size then
        let (jitBits, jitLen) := allBitstreams[blockIdx]
        let (refBits, refLen) := cavlcEncodeFull allQuantLevels[blockIdx]
        if jitBits.toNat != refBits.toNat || jitLen != refLen then
          IO.eprintln s!"  MISMATCH block {blockIdx}: JIT=0x{String.ofList (Nat.toDigits 16 jitBits.toNat)}({jitLen}) ref=0x{String.ofList (Nat.toDigits 16 refBits.toNat)}({refLen})"
          pass := false

  if pass then
    IO.println "  PASS: All CAVLC outputs match pure Lean reference"
  else
    IO.eprintln "  FAIL: CAVLC output mismatch"

  return pass

-- ============================================================================
-- Main
-- ============================================================================

def main : IO UInt32 := do
  IO.println "H.264 Annex-B Bitstream Test"
  IO.println "============================"

  let r1 ← testBitstreamGeneration

  IO.println "\n============================"
  if r1 then
    IO.println "ALL TESTS PASSED"
    return 0
  else
    IO.eprintln "SOME TESTS FAILED"
    return 1
