/-
  H.264 Frame Encoder — JIT End-to-End Test

  Tests the autonomous frame encoder by:
  1. Compile frame encoder JIT
  2. Load VLC tables into CAVLC memories
  3. Load 16×16 test image into frame buffer
  4. Set QP parameters
  5. Pulse start
  6. Collect output bytes until done
  7. Compare per-block CAVLC output against pure Lean reference
  8. Wrap in MP4

  Usage:
    lake build h264-frame-encoder-test && lake exe h264-frame-encoder-test
-/

import Sparkle.Core.JIT
import IP.Video.H264.Quant
import IP.Video.H264.FrameEncoderSynth
import IP.Video.H264.VLCTables
import IP.Video.H264.CAVLCSynth
import IP.Video.H264.SPSPPSData
import IP.Video.H264.MP4Mux
import IP.Video.H264.Encoder
import IP.Video.H264.CAVLC

open Sparkle.Core.JIT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.FrameEncoder
open Sparkle.IP.Video.H264.VLCTables
open Sparkle.IP.Video.H264.CAVLCSynth
open Sparkle.IP.Video.H264.SPSPPSData
open Sparkle.IP.Video.H264.MP4Mux
open Sparkle.IP.Video.H264.Encoder
open Sparkle.IP.Video.H264.CAVLC

-- ============================================================================
-- Helpers
-- ============================================================================

private def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

-- Scan order: scanIdx → raster block index (by*4+bx)
-- scanBx = {idx[2], idx[0]}, scanBy = {idx[3], idx[1]}
private def scanToRaster : Array Nat :=
  #[0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]

-- ============================================================================
-- Test image: 16×16 gradient
-- ============================================================================

private def testImage16x16 : Array Nat := Id.run do
  let mut pixels : Array Nat := #[]
  for row in [:16] do
    for col in [:16] do
      let val := 100 + row * 4 + col
      pixels := pixels.push (min val 255)
  pixels

-- ============================================================================
-- Main test
-- ============================================================================

def testFrameEncoder : IO Bool := do
  IO.println "\n=== H.264 Frame Encoder JIT Test ==="

  let image := testImage16x16
  let qp := 20
  IO.println s!"  Image: 16×16, QP={qp}"

  -- Compile JIT
  IO.println "  Compiling frame_encoder_jit.cpp..."
  let handle ← JIT.compileAndLoad "IP/Video/H264/gen/frame_encoder_jit.cpp"
  IO.println "  Loaded frame encoder JIT module"

  -- Load VLC tables
  IO.println "  Loading VLC tables..."
  let ctTableFull := buildCoeffTokenTableFull
  for i in [:ctTableFull.size] do
    if h : i < ctTableFull.size then
      JIT.setInput handle 12 1
      JIT.setInput handle 13 i.toUInt64
      JIT.setInput handle 14 ctTableFull[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle 12 0

  let tzTable := buildTotalZerosTable
  for i in [:tzTable.size] do
    if h : i < tzTable.size then
      JIT.setInput handle 15 1
      JIT.setInput handle 16 i.toUInt64
      JIT.setInput handle 17 tzTable[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle 15 0

  let rbTable := buildRunBeforeTable
  for i in [:rbTable.size] do
    if h : i < rbTable.size then
      JIT.setInput handle 18 1
      JIT.setInput handle 19 i.toUInt64
      JIT.setInput handle 20 rbTable[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle 18 0

  let zzTable := zigzagTable
  for i in [:zzTable.size] do
    if h : i < zzTable.size then
      JIT.setInput handle 21 1
      JIT.setInput handle 22 i.toUInt64
      JIT.setInput handle 23 zzTable[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle 21 0
  IO.println "  VLC tables loaded"

  -- Load test image
  IO.println "  Loading 16×16 image..."
  for i in [:256] do
    let val := if h : i < image.size then image[i] else 128
    JIT.setInput handle 1 1
    JIT.setInput handle 2 i.toUInt64
    JIT.setInput handle 3 val.toUInt64
    JIT.eval handle
    JIT.tick handle
  JIT.setInput handle 1 0

  -- Set QP parameters
  let (mf0, mf1, mf2, f, qbits) := quantParams qp
  let (vs0, vs1, vs2) := dequantScales qp
  JIT.setInput handle 4 mf0.toUInt64
  JIT.setInput handle 5 mf1.toUInt64
  JIT.setInput handle 6 mf2.toUInt64
  JIT.setInput handle 7 f.toUInt64
  JIT.setInput handle 8 qbits.toUInt64
  JIT.setInput handle 9 vs0.toUInt64
  JIT.setInput handle 10 vs1.toUInt64
  JIT.setInput handle 11 vs2.toUInt64

  -- Pulse start
  IO.println "  Starting frame encoder..."
  JIT.setInput handle 0 1
  JIT.eval handle
  JIT.tick handle
  JIT.setInput handle 0 0

  -- Resolve wires
  let phaseIdx ← resolveWire handle "_gen_mainPhase"
  let scanIdxW ← resolveWire handle "_gen_scanIdx"
  let cavlcBitBufW ← resolveWire handle "_gen_cavlcBitBuffer"
  let cavlcBitPosW ← resolveWire handle "_gen_cavlcBitPos"

  -- Collect output bytes and per-scan-block CAVLC outputs
  let mut outputBytes : Array UInt8 := #[]
  let mut totalCycles := 0
  let maxCycles := 20000
  let mut lastPhase : UInt64 := 255
  -- Collect CAVLC {buf_hi32, pos} for each scan block
  let mut cavlcBufs : Array UInt64 := Array.replicate 16 0
  let mut cavlcPoss : Array UInt64 := Array.replicate 16 0

  for cycle in [:maxCycles] do
    JIT.eval handle
    let outPacked ← JIT.getOutput handle 0
    let doneVal := outPacked &&& 1
    let validVal := (outPacked >>> 1) &&& 1
    let byteVal := (outPacked >>> 2) &&& 0xFF
    let phase ← JIT.getWire handle phaseIdx
    let scnIdx ← JIT.getWire handle scanIdxW

    -- Capture CAVLC output when entering EMIT_CAVLC_BITS (phase 16)
    if phase == 16 && phase != lastPhase then
      let cavBuf ← JIT.getWire handle cavlcBitBufW
      let cavPos ← JIT.getWire handle cavlcBitPosW
      let si := scnIdx.toNat
      if si < 16 then
        cavlcBufs := cavlcBufs.set! si cavBuf
        cavlcPoss := cavlcPoss.set! si cavPos

    -- Print phase transitions (minimal)
    if phase != lastPhase then
      if phase == 12 && scnIdx == 0 then
        IO.println s!"  [cycle {cycle}] Scan phase started"
      if phase == 18 then
        IO.println s!"  [cycle {cycle}] Trailing bits"
      lastPhase := phase

    if validVal != 0 then
      outputBytes := outputBytes.push byteVal.toNat.toUInt8

    if doneVal != 0 then
      totalCycles := cycle + 1
      break

    JIT.tick handle
    totalCycles := cycle + 1

  -- Read all 256 quantized levels from quantStoreMem (memory index 8)
  IO.println "  Reading quantized levels from memory..."
  let mut allQuantLevels : Array (Array Int) := #[]
  for blk in [:16] do
    let mut levels : Array Int := #[]
    for j in [:16] do
      let v ← JIT.getMem handle 8 (blk * 16 + j).toUInt32
      let v16 : Int := if v > 32767 then (v.toNat : Int) - 65536 else v.toNat
      levels := levels.push v16
    allQuantLevels := allQuantLevels.push levels

  -- Read tcMap to compute correct nC per block
  IO.println "  Reading totalCoeff map from memory..."
  let mut tcMap : Array Nat := #[]
  for j in [:16] do
    let v ← JIT.getMem handle 26 j.toUInt32
    tcMap := tcMap.push v.toNat
  IO.println s!"  tcMap = {tcMap}"

  JIT.destroy handle

  if totalCycles >= maxCycles then
    IO.eprintln s!"  FAIL: Frame encoder did not complete within {maxCycles} cycles"
    return false

  IO.println s!"  Frame encoder completed in {totalCycles} cycles"
  IO.println s!"  Output: {outputBytes.size} bytes"

  -- ================================================================
  -- Compare per-block CAVLC output against pure Lean reference
  -- ================================================================
  IO.println "\n  === CAVLC Per-Block Comparison ==="
  let mut cavlcMatch := true
  for si in [:16] do
    -- Get raster block index for this scan block
    let rasterIdx := if h : si < scanToRaster.size then scanToRaster[si] else 0
    -- Get quantized levels for this raster block (in raster order, as expected by cavlcEncodeFull)
    let rasterLevels := if h : rasterIdx < allQuantLevels.size then allQuantLevels[rasterIdx] else #[]

    -- Compute nC from left/top neighbors' totalCoeff (H.264 Section 9.2.1)
    -- scan block position: bx, by
    let bx := rasterIdx % 4
    let by_ := rasterIdx / 4
    let leftTC := if bx > 0 then
      let idx := by_ * 4 + (bx - 1)
      if h : idx < tcMap.size then some tcMap[idx] else none
    else none
    let topTC := if by_ > 0 then
      let idx := (by_ - 1) * 4 + bx
      if h : idx < tcMap.size then some tcMap[idx] else none
    else none
    let nC := match leftTC, topTC with
      | some a, some b => (a + b + 1) / 2
      | some a, none => a
      | none, some b => b
      | none, none => 0

    -- Compute reference CAVLC with correct nC
    let (refBuf64, refPos) := cavlcEncodeFull rasterLevels (nC := nC)

    -- Hardware output: 64-bit MSB-aligned
    let hwBuf := if h : si < cavlcBufs.size then cavlcBufs[si] else 0
    let hwPos := if h : si < cavlcPoss.size then cavlcPoss[si] else 0

    -- Compare full 64-bit buffers
    let refBufNat := refBuf64.toNat

    if hwBuf.toNat != refBufNat || hwPos != refPos.toUInt64 then
      IO.println s!"  MISMATCH scan[{si}] raster[{rasterIdx}] ({bx},{by_}) nC={nC}:"
      IO.println s!"    levels = {rasterLevels}"
      IO.println s!"    hw:  buf=0x{String.ofList (Nat.toDigits 16 hwBuf.toNat)} pos={hwPos}"
      IO.println s!"    ref: buf=0x{String.ofList (Nat.toDigits 16 refBufNat)} pos={refPos}"
      cavlcMatch := false
    else
      IO.println s!"  OK scan[{si}] raster[{rasterIdx}] ({bx},{by_}) nC={nC} pos={hwPos}"

  if cavlcMatch then
    IO.println "  All 16 CAVLC blocks match reference!"
  else
    IO.eprintln "  CAVLC mismatch detected!"

  -- Basic validation
  let mut pass := true

  if outputBytes.size < 30 then
    IO.eprintln s!"  FAIL: Output too small ({outputBytes.size} bytes)"
    pass := false

  if outputBytes.size >= 5 then
    let sc := (outputBytes[0]!, outputBytes[1]!, outputBytes[2]!, outputBytes[3]!, outputBytes[4]!)
    if sc == (0, 0, 0, 1, 0x67) then
      IO.println "  SPS header: OK"
    else
      IO.eprintln "  FAIL: Bad SPS header"
      pass := false

  -- Write .h264 file
  let h264Path := "IP/Video/H264/gen/test_frame_encoder.h264"
  IO.FS.writeBinFile h264Path (ByteArray.mk outputBytes)
  IO.println s!"  Written to {h264Path}"

  -- Wrap in MP4
  if outputBytes.size > 28 then
    let spsBytes : ByteArray := Id.run do
      let mut ba : ByteArray := ByteArray.empty
      for i in [4:15] do
        if h : i < outputBytes.size then
          ba := ba.push outputBytes[i]
      ba
    let ppsBytes : ByteArray := Id.run do
      let mut ba : ByteArray := ByteArray.empty
      for i in [19:23] do
        if h : i < outputBytes.size then
          ba := ba.push outputBytes[i]
      ba
    let idrBytes : ByteArray := Id.run do
      let mut ba : ByteArray := ByteArray.empty
      for i in [27:outputBytes.size] do
        if h : i < outputBytes.size then
          ba := ba.push outputBytes[i]
      ba
    let mp4 := muxSingleFrame spsBytes ppsBytes idrBytes 16 16
    let mp4Path := "IP/Video/H264/gen/test_frame_encoder.mp4"
    IO.FS.writeBinFile mp4Path mp4
    IO.println s!"  MP4 written: {mp4.size} bytes → {mp4Path}"

  if pass && cavlcMatch then
    IO.println "  PASS: Frame encoder produced valid output"
  else
    IO.eprintln "  FAIL: Frame encoder validation failed"
    pass := false

  return pass

-- ============================================================================
-- Main
-- ============================================================================

def main : IO UInt32 := do
  IO.println "H.264 Frame Encoder Test"
  IO.println "========================"

  let r1 ← testFrameEncoder

  IO.println "\n========================"
  if r1 then
    IO.println "TEST PASSED"
    return 0
  else
    IO.eprintln "TEST FAILED"
    return 1
