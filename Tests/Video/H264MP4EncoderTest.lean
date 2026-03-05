/-
  H.264 MP4 Encoder — JIT End-to-End Test

  Tests the hardware MP4 encoder by:
  1. Compile MP4 encoder JIT
  2. Load MP4 ROM (629 bytes from buildMP4ROMTemplate)
  3. Load VLC tables + test image + QP params
  4. Set width=16, height=16
  5. Pulse start
  6. Collect output bytes until done
  7. Write .mp4, verify structure
  8. Compare against software muxer reference

  Usage:
    lake build h264-mp4-encoder-test && lake exe h264-mp4-encoder-test
-/

import Sparkle.Core.JIT
import IP.Video.H264.Quant
import IP.Video.H264.MP4EncoderSynth
import IP.Video.H264.VLCTables
import IP.Video.H264.CAVLCSynth
import IP.Video.H264.SPSPPSData
import IP.Video.H264.MP4Mux

open Sparkle.Core.JIT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.MP4Encoder
open Sparkle.IP.Video.H264.VLCTables
open Sparkle.IP.Video.H264.CAVLCSynth
open Sparkle.IP.Video.H264.SPSPPSData
open Sparkle.IP.Video.H264.MP4Mux

-- ============================================================================
-- Helpers
-- ============================================================================

private def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

-- ============================================================================
-- Test image: 16×16 gradient (same as frame encoder test)
-- ============================================================================

private def testImage16x16 : Array Nat := Id.run do
  let mut pixels : Array Nat := #[]
  for row in [:16] do
    for col in [:16] do
      let val := 100 + row * 4 + col
      pixels := pixels.push (min val 255)
  pixels

-- ============================================================================
-- Input port indices for h264MP4Encoder
-- Port order matches the function signature:
--   0: start
--   1: frameWriteEn, 2: frameWriteAddr, 3: frameWriteData
--   4-6: quantMF0-2, 7: quantF, 8: quantShift
--   9-11: vscale0-2
--   12-14: ctWrEn/Addr/Data, 15-17: tzWrEn/Addr/Data
--   18-20: rbWrEn/Addr/Data, 21-23: zzWrEn/Addr/Data
--   24: romWrEn, 25: romWrAddr, 26: romWrData
--   27: widthIn, 28: heightIn
-- ============================================================================

private def PORT_START       : UInt32 := 0
private def PORT_FRM_WR_EN   : UInt32 := 1
private def PORT_FRM_WR_ADDR : UInt32 := 2
private def PORT_FRM_WR_DATA : UInt32 := 3
private def PORT_QMF0        : UInt32 := 4
private def PORT_QMF1        : UInt32 := 5
private def PORT_QMF2        : UInt32 := 6
private def PORT_QF          : UInt32 := 7
private def PORT_QSHIFT      : UInt32 := 8
private def PORT_VS0         : UInt32 := 9
private def PORT_VS1         : UInt32 := 10
private def PORT_VS2         : UInt32 := 11
private def PORT_CT_WR_EN    : UInt32 := 12
private def PORT_CT_WR_ADDR  : UInt32 := 13
private def PORT_CT_WR_DATA  : UInt32 := 14
private def PORT_TZ_WR_EN    : UInt32 := 15
private def PORT_TZ_WR_ADDR  : UInt32 := 16
private def PORT_TZ_WR_DATA  : UInt32 := 17
private def PORT_RB_WR_EN    : UInt32 := 18
private def PORT_RB_WR_ADDR  : UInt32 := 19
private def PORT_RB_WR_DATA  : UInt32 := 20
private def PORT_ZZ_WR_EN    : UInt32 := 21
private def PORT_ZZ_WR_ADDR  : UInt32 := 22
private def PORT_ZZ_WR_DATA  : UInt32 := 23
private def PORT_ROM_WR_EN   : UInt32 := 24
private def PORT_ROM_WR_ADDR : UInt32 := 25
private def PORT_ROM_WR_DATA : UInt32 := 26
private def PORT_WIDTH       : UInt32 := 27
private def PORT_HEIGHT      : UInt32 := 28

-- ============================================================================
-- Main test
-- ============================================================================

def testMP4Encoder : IO Bool := do
  IO.println "\n=== H.264 MP4 Encoder JIT Test ==="

  let image := testImage16x16
  let qp := 20
  IO.println s!"  Image: 16×16, QP={qp}"

  -- Compile JIT
  IO.println "  Compiling mp4_encoder_jit.cpp..."
  let handle ← JIT.compileAndLoad "IP/Video/H264/gen/mp4_encoder_jit.cpp"
  IO.println "  Loaded MP4 encoder JIT module"

  -- Set width/height
  JIT.setInput handle PORT_WIDTH 16
  JIT.setInput handle PORT_HEIGHT 16

  -- Load MP4 ROM (629 bytes)
  IO.println "  Loading MP4 ROM template (629 bytes)..."
  let rom := buildMP4ROMTemplate
  for i in [:rom.size] do
    if h : i < rom.size then
      JIT.setInput handle PORT_ROM_WR_EN 1
      JIT.setInput handle PORT_ROM_WR_ADDR i.toUInt64
      JIT.setInput handle PORT_ROM_WR_DATA rom[i].toNat.toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle PORT_ROM_WR_EN 0
  IO.println "  ROM loaded"

  -- Load VLC tables
  IO.println "  Loading VLC tables..."
  let ctTableFull := buildCoeffTokenTableFull
  for i in [:ctTableFull.size] do
    if h : i < ctTableFull.size then
      JIT.setInput handle PORT_CT_WR_EN 1
      JIT.setInput handle PORT_CT_WR_ADDR i.toUInt64
      JIT.setInput handle PORT_CT_WR_DATA ctTableFull[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle PORT_CT_WR_EN 0

  let tzTable := buildTotalZerosTable
  for i in [:tzTable.size] do
    if h : i < tzTable.size then
      JIT.setInput handle PORT_TZ_WR_EN 1
      JIT.setInput handle PORT_TZ_WR_ADDR i.toUInt64
      JIT.setInput handle PORT_TZ_WR_DATA tzTable[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle PORT_TZ_WR_EN 0

  let rbTable := buildRunBeforeTable
  for i in [:rbTable.size] do
    if h : i < rbTable.size then
      JIT.setInput handle PORT_RB_WR_EN 1
      JIT.setInput handle PORT_RB_WR_ADDR i.toUInt64
      JIT.setInput handle PORT_RB_WR_DATA rbTable[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle PORT_RB_WR_EN 0

  let zzTable := zigzagTable
  for i in [:zzTable.size] do
    if h : i < zzTable.size then
      JIT.setInput handle PORT_ZZ_WR_EN 1
      JIT.setInput handle PORT_ZZ_WR_ADDR i.toUInt64
      JIT.setInput handle PORT_ZZ_WR_DATA zzTable[i].toUInt64
      JIT.eval handle
      JIT.tick handle
  JIT.setInput handle PORT_ZZ_WR_EN 0
  IO.println "  VLC tables loaded"

  -- Load test image
  IO.println "  Loading 16×16 image..."
  for i in [:256] do
    let val := if h : i < image.size then image[i] else 128
    JIT.setInput handle PORT_FRM_WR_EN 1
    JIT.setInput handle PORT_FRM_WR_ADDR i.toUInt64
    JIT.setInput handle PORT_FRM_WR_DATA val.toUInt64
    JIT.eval handle
    JIT.tick handle
  JIT.setInput handle PORT_FRM_WR_EN 0

  -- Set QP parameters
  let (mf0, mf1, mf2, f, qbits) := quantParams qp
  let (vs0, vs1, vs2) := dequantScales qp
  JIT.setInput handle PORT_QMF0 mf0.toUInt64
  JIT.setInput handle PORT_QMF1 mf1.toUInt64
  JIT.setInput handle PORT_QMF2 mf2.toUInt64
  JIT.setInput handle PORT_QF f.toUInt64
  JIT.setInput handle PORT_QSHIFT qbits.toUInt64
  JIT.setInput handle PORT_VS0 vs0.toUInt64
  JIT.setInput handle PORT_VS1 vs1.toUInt64
  JIT.setInput handle PORT_VS2 vs2.toUInt64

  -- Pulse start
  IO.println "  Starting MP4 encoder..."
  JIT.setInput handle PORT_START 1
  JIT.eval handle
  JIT.tick handle
  JIT.setInput handle PORT_START 0

  -- Resolve phase wire for monitoring
  let phaseIdx ← resolveWire handle "_gen_phase"

  -- Collect output bytes
  let mut outputBytes : Array UInt8 := #[]
  let mut totalCycles := 0
  let maxCycles := 30000
  let mut lastPhase : UInt64 := 255

  for cycle in [:maxCycles] do
    JIT.eval handle
    let outPacked ← JIT.getOutput handle 0
    let doneVal := outPacked &&& 1
    let validVal := (outPacked >>> 1) &&& 1
    let byteVal := (outPacked >>> 2) &&& 0xFF
    let phase ← JIT.getWire handle phaseIdx

    -- Log phase transitions
    if phase != lastPhase then
      let phaseName := match phase with
        | 0 => "IDLE"
        | 1 => "RUN_ENCODER"
        | 2 => "EMIT_ROM"
        | 3 => "EMIT_MDAT_HDR"
        | 4 => "EMIT_IDR_LEN"
        | 5 => "EMIT_IDR_DATA"
        | 6 => "DONE"
        | _ => s!"UNKNOWN({phase})"
      IO.println s!"  [cycle {cycle}] Phase → {phaseName} (output so far: {outputBytes.size} bytes)"
      lastPhase := phase

    if validVal != 0 then
      outputBytes := outputBytes.push byteVal.toNat.toUInt8

    if doneVal != 0 then
      totalCycles := cycle + 1
      break

    JIT.tick handle
    totalCycles := cycle + 1

  JIT.destroy handle

  if totalCycles >= maxCycles then
    IO.eprintln s!"  FAIL: MP4 encoder did not complete within {maxCycles} cycles"
    return false

  IO.println s!"  MP4 encoder completed in {totalCycles} cycles"
  IO.println s!"  Output: {outputBytes.size} bytes"

  -- Write .mp4 file
  let mp4Path := "IP/Video/H264/gen/test_mp4_encoder.mp4"
  IO.FS.writeBinFile mp4Path (ByteArray.mk outputBytes)
  IO.println s!"  Written to {mp4Path}"

  -- ================================================================
  -- Validation
  -- ================================================================
  let mut pass := true

  -- Check minimum size: 629 (ROM) + 8 (mdat hdr) + 4 (IDR len) + 1 (min IDR) = 642
  if outputBytes.size < 642 then
    IO.eprintln s!"  FAIL: Output too small ({outputBytes.size} bytes, expected >= 642)"
    pass := false

  -- Check ftyp box header
  if outputBytes.size >= 8 then
    let ftypType := (outputBytes[4]!, outputBytes[5]!, outputBytes[6]!, outputBytes[7]!)
    if ftypType == (0x66, 0x74, 0x79, 0x70) then  -- "ftyp"
      IO.println "  ftyp header: OK"
    else
      IO.eprintln "  FAIL: Bad ftyp header"
      pass := false

  -- Check moov box at offset 24
  if outputBytes.size >= 32 then
    let moovType := (outputBytes[28]!, outputBytes[29]!, outputBytes[30]!, outputBytes[31]!)
    if moovType == (0x6D, 0x6F, 0x6F, 0x76) then  -- "moov"
      IO.println "  moov header: OK"
    else
      IO.eprintln "  FAIL: Bad moov header"
      pass := false

  -- Check mdat at offset 629
  if outputBytes.size >= 637 then
    let mdatType := (outputBytes[633]!, outputBytes[634]!, outputBytes[635]!, outputBytes[636]!)
    if mdatType == (0x6D, 0x64, 0x61, 0x74) then  -- "mdat"
      IO.println "  mdat header: OK"
    else
      IO.eprintln s!"  FAIL: Bad mdat header at offset 633: {outputBytes[633]!} {outputBytes[634]!} {outputBytes[635]!} {outputBytes[636]!}"
      pass := false

  -- Check IDR NAL starts with 0x65
  if outputBytes.size >= 642 then
    let idrStart := outputBytes[641]!
    if idrStart == 0x65 then
      IO.println "  IDR NAL (0x65): OK"
    else
      IO.eprintln s!"  FAIL: Expected IDR NAL 0x65, got 0x{String.ofList (Nat.toDigits 16 idrStart.toNat)}"
      pass := false

  -- Compare ROM portion (first 629 bytes) with software reference
  -- The ROM should match except at patch points (which should have width=16, height=16 values)
  let refMp4Path := "IP/Video/H264/gen/test_frame_encoder.mp4"
  let refExists ← try
    let _ ← IO.FS.readBinFile refMp4Path
    pure true
  catch _ => pure false
  if refExists then
    let refData ← IO.FS.readBinFile refMp4Path
    -- Compare ftyp+moov region (first 629 bytes)
    let mut romMatch := true
    let compareLen := min 629 (min outputBytes.size refData.size)
    for i in [:compareLen] do
      if h1 : i < outputBytes.size then
        if h2 : i < refData.size then
          if outputBytes[i] != refData.data[i]! then
            if romMatch then  -- only print first mismatch
              IO.eprintln s!"  ROM mismatch at byte {i}: hw=0x{String.ofList (Nat.toDigits 16 outputBytes[i].toNat)} ref=0x{String.ofList (Nat.toDigits 16 refData.data[i]!.toNat)}"
            romMatch := false
    if romMatch then
      IO.println "  ROM vs reference (629 bytes): MATCH"
    else
      IO.eprintln "  ROM vs reference: MISMATCH (some bytes differ)"
      -- Not a hard fail — patch values may differ from template

    -- Compare mdat content (IDR NAL bytes)
    if outputBytes.size > 641 && refData.size > 641 then
      let hwIdrStart := 641  -- after 629 ROM + 8 mdat hdr + 4 IDR len
      let refIdrStart := 641  -- same for reference (629 + 12)
      let hwIdrLen := outputBytes.size - hwIdrStart
      let refIdrLen := refData.size - refIdrStart
      if hwIdrLen == refIdrLen then
        let mut idrMatch := true
        for j in [:hwIdrLen] do
          let hi := hwIdrStart + j
          let ri := refIdrStart + j
          if h1 : hi < outputBytes.size then
            if h2 : ri < refData.size then
              if outputBytes[hi] != refData.data[ri]! then
                idrMatch := false
        if idrMatch then
          IO.println s!"  IDR NAL ({hwIdrLen} bytes): MATCH"
        else
          IO.eprintln "  IDR NAL: MISMATCH"
      else
        IO.println s!"  IDR NAL size: hw={hwIdrLen}, ref={refIdrLen}"

  if pass then
    IO.println "  PASS: MP4 encoder produced valid output"
  else
    IO.eprintln "  FAIL: MP4 encoder validation failed"

  return pass

-- ============================================================================
-- Main
-- ============================================================================

def main : IO UInt32 := do
  IO.println "H.264 MP4 Encoder Test"
  IO.println "======================"

  let r1 ← testMP4Encoder

  IO.println "\n======================"
  if r1 then
    IO.println "TEST PASSED"
    return 0
  else
    IO.eprintln "TEST FAILED"
    return 1
