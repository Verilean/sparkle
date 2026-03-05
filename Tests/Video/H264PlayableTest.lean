/-
  H.264 Playable Stream Test — Full 16-block Macroblock with nC-dependent CAVLC

  Produces a valid ffplay-playable .h264 file from hardware (JIT) output:
  1. Generate 16×16 gradient test image
  2. For each 4×4 block in raster order:
     a. Compute DC prediction from reconstructed neighbors
     b. Run encoder JIT → quantized levels
     c. Count totalCoeff, store in tcMap
     d. Run decoder JIT → reconstructed pixels
     e. Store reconstructed pixels for next block's neighbors
  3. For each block in H.264 scan order:
     a. Compute nC from left/top block's totalCoeff
     b. Set nCTableSelect on CAVLC JIT
     c. Run CAVLC JIT → bitstream
     d. Verify against cavlcEncodeFull(levels, nC)
  4. Assemble Annex-B: SPS + PPS + IDR slice header + MB header + 16 CAVLC blocks
  5. Write to IP/Video/H264/gen/test_playable.h264

  Usage:
    lake build h264-playable-test && lake exe h264-playable-test

  Verify:
    ffprobe -v error -show_streams IP/Video/H264/gen/test_playable.h264
    ffplay -vf "scale=256:256:flags=neighbor" IP/Video/H264/gen/test_playable.h264
-/

import Sparkle.Core.JIT
import IP.Video.H264.Quant
import IP.Video.H264.EncoderSynth
import IP.Video.H264.DecoderSynth
import IP.Video.H264.CAVLCSynth
import IP.Video.H264.VLCTables
import IP.Video.H264.CAVLC
import IP.Video.H264.SPSPPSData
import IP.Video.H264.Encoder
import IP.Video.H264.IntraPred
import IP.Video.H264.NAL
import IP.Video.H264.MP4Mux

open Sparkle.Core.JIT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.EncoderSynth
open Sparkle.IP.Video.H264.DecoderSynth
open Sparkle.IP.Video.H264.CAVLCSynth
open Sparkle.IP.Video.H264.VLCTables
open Sparkle.IP.Video.H264.CAVLC
open Sparkle.IP.Video.H264.SPSPPSData
open Sparkle.IP.Video.H264.Encoder
open Sparkle.IP.Video.H264.IntraPred
open Sparkle.IP.Video.H264.NAL
open Sparkle.IP.Video.H264.MP4Mux

-- ============================================================================
-- Helpers
-- ============================================================================

private def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

private def intToU16 (v : Int) : UInt32 :=
  if v < 0 then (65536 + v).toNat.toUInt32
  else v.toNat.toUInt32

private def u16ToInt (val : UInt32) : Int :=
  if val.toNat >= 32768 then (val.toNat : Int) - 65536
  else (val.toNat : Int)

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

private def extractBlock (image : Array Nat) (bx by_ : Nat) : Array Nat := Id.run do
  let mut block : Array Nat := #[]
  for i in [:4] do
    for j in [:4] do
      let idx := (by_ * 4 + i) * 16 + (bx * 4 + j)
      let val := if h : idx < image.size then image[idx] else 128
      block := block.push val
  block

-- ============================================================================
-- Count non-zero coefficients in a quantized level array
-- ============================================================================

private def countTotalCoeff (levels : Array Int) : Nat := Id.run do
  let mut count : Nat := 0
  for i in [:levels.size] do
    if h : i < levels.size then
      if levels[i] != 0 then count := count + 1
  return count

-- ============================================================================
-- Main test
-- ============================================================================

def testPlayableStream : IO Bool := do
  IO.println "\n=== H.264 Playable Stream Generation (16 blocks, nC-dependent CAVLC) ==="

  let image := testImage16x16
  let qp := 20
  IO.println s!"  Image: 16×16, QP={qp}"

  -- Compile JIT modules
  IO.println "  Compiling encoder pipeline..."
  let encHandle ← JIT.compileAndLoad "IP/Video/H264/gen/encoder_pipeline_jit.cpp"
  let encDoneIdx ← resolveWire encHandle "_gen_done"

  IO.println "  Compiling decoder pipeline..."
  let decHandle ← JIT.compileAndLoad "IP/Video/H264/gen/decoder_pipeline_jit.cpp"
  let decDoneIdx ← resolveWire decHandle "_gen_done"

  IO.println "  Compiling CAVLC synth..."
  let cavlcHandle ← JIT.compileAndLoad "IP/Video/H264/gen/cavlc_synth_jit.cpp"
  let cavlcDoneIdx ← resolveWire cavlcHandle "_gen_done"

  -- Set QP parameters
  let (mf0, mf1, mf2, f, qbits) := quantParams qp
  let (vs0, vs1, vs2) := dequantScales qp

  -- Load CAVLC VLC tables (full 272-entry coeff_token table for all nC ranges)
  IO.println "  Loading VLC tables (272-entry coeff_token + total_zeros + run_before + zigzag)..."
  let zzTable := zigzagTable
  let ctTableFull := buildCoeffTokenTableFull
  let tzTable := buildTotalZerosTable
  let rbTable := buildRunBeforeTable

  -- Storage for block results
  let mut allQuantLevels : Array (Array Int) := Array.replicate 16 #[]
  let mut tcMap : Array Nat := Array.replicate 16 0  -- totalCoeff per block (indexed by by_*4 + bx)
  let mut reconFrame : Array Nat := Array.replicate 256 128  -- 16×16 reconstructed pixels

  -- ================================================================
  -- Phase 1: Encode + Decode each block in raster order
  -- ================================================================
  IO.println "  Phase 1: Encode + Decode blocks in raster order..."

  for by_ in [:4] do
    for bx in [:4] do
      let blockIdx := by_ * 4 + bx
      let block := extractBlock image bx by_

      -- Build neighbor pixels from reconstructed frame for DC prediction
      let mut abovePixels := Array.replicate 8 128
      let mut leftPixels := Array.replicate 4 128
      let hasAbove := by_ > 0
      let hasLeft := bx > 0

      if hasAbove then
        for j in [:8] do
          let px := bx * 4 + j
          let py := by_ * 4 - 1
          let idx := py * 16 + px
          if h : idx < reconFrame.size then
            if px < 16 then
              abovePixels := abovePixels.set! j reconFrame[idx]

      if hasLeft then
        for i in [:4] do
          let py := by_ * 4 + i
          let px := bx * 4 - 1
          let idx := py * 16 + px
          if h : idx < reconFrame.size then
            leftPixels := leftPixels.set! i reconFrame[idx]

      -- DC prediction
      let neighbors : Neighbors :=
        { above := abovePixels, left := leftPixels, aboveLeft := 128,
          hasAbove := hasAbove, hasLeft := hasLeft }
      let predicted := predictDC neighbors

      -- === Run encoder JIT ===
      JIT.reset encHandle

      -- Load original pixels into memIdx=0
      for i in [:16] do
        let val := if h : i < block.size then block[i] else 0
        JIT.setMem encHandle 0 i.toUInt32 val.toUInt32
      -- Load prediction into memIdx=1
      for i in [:16] do
        let val := if h : i < predicted.size then predicted[i] else 128
        JIT.setMem encHandle 1 i.toUInt32 val.toUInt32

      -- Set QP parameters
      JIT.setInput encHandle 7 mf0.toUInt64
      JIT.setInput encHandle 8 mf1.toUInt64
      JIT.setInput encHandle 9 mf2.toUInt64
      JIT.setInput encHandle 10 f.toUInt64
      JIT.setInput encHandle 11 qbits.toUInt64

      -- Start encoder
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

      -- Read quantized levels from memIdx=6
      let mut levels : Array Int := #[]
      for i in [:16] do
        let val ← JIT.getMem encHandle 6 i.toUInt32
        levels := levels.push (u16ToInt val)

      allQuantLevels := allQuantLevels.set! blockIdx levels
      let tc := countTotalCoeff levels
      tcMap := tcMap.set! blockIdx tc

      -- === Run decoder JIT (reconstruct) ===
      JIT.reset decHandle

      -- Load quantized levels into memIdx=0
      for i in [:16] do
        let val := if h : i < levels.size then levels[i] else 0
        JIT.setMem decHandle 0 i.toUInt32 (intToU16 val)
      -- Load prediction into memIdx=5
      for i in [:16] do
        let val := if h : i < predicted.size then predicted[i] else 128
        JIT.setMem decHandle 5 i.toUInt32 val.toUInt32

      -- Set QP parameters
      JIT.setInput decHandle 7 vs0.toUInt64
      JIT.setInput decHandle 8 vs1.toUInt64
      JIT.setInput decHandle 9 vs2.toUInt64

      -- Start decoder
      JIT.setInput decHandle 0 1
      JIT.eval decHandle
      JIT.tick decHandle
      JIT.setInput decHandle 0 0

      -- Run until done
      for _ in [:200] do
        JIT.eval decHandle
        let doneVal ← JIT.getWire decHandle decDoneIdx
        if doneVal != 0 then break
        JIT.tick decHandle

      -- Read reconstructed pixels from memIdx=6
      for i in [:16] do
        let val ← JIT.getMem decHandle 6 i.toUInt32
        let py := by_ * 4 + i / 4
        let px := bx * 4 + i % 4
        let fidx := py * 16 + px
        if fidx < reconFrame.size then
          reconFrame := reconFrame.set! fidx val.toNat

      if blockIdx % 4 == 0 then
        IO.println s!"    Block {blockIdx}/16: tc={tc}, levels[0..3]={levels.toList.take 4}"

  -- ================================================================
  -- Phase 2: CAVLC encode each block in H.264 scan order with nC
  -- ================================================================
  IO.println "  Phase 2: CAVLC encode blocks with nC-dependent table selection..."

  let scanOrder := h264BlockScan
  let mut allBitstreams : Array (BitVec 32 × Nat) := #[]
  let mut pass := true

  for scanIdx in [:16] do
    if h : scanIdx < scanOrder.size then
      let (bx, by_) := scanOrder[scanIdx]
      let blockIdx := by_ * 4 + bx

      -- Compute nC from left and top block's totalCoeff
      let leftTC : Option Nat :=
        if bx > 0 then
          let leftIdx := by_ * 4 + (bx - 1)
          if h2 : leftIdx < tcMap.size then some tcMap[leftIdx] else none
        else none
      let topTC : Option Nat :=
        if by_ > 0 then
          let topIdx := (by_ - 1) * 4 + bx
          if h2 : topIdx < tcMap.size then some tcMap[topIdx] else none
        else none
      let nC := computeNC leftTC topTC
      let tableSel := nCToTableSelect nC

      -- Get quantized levels for this block
      let levels := if h2 : blockIdx < allQuantLevels.size then allQuantLevels[blockIdx] else #[]

      -- Reset CAVLC encoder
      JIT.reset cavlcHandle

      -- Reload VLC tables after reset
      for i in [:zzTable.size] do
        if h2 : i < zzTable.size then
          JIT.setMem cavlcHandle 0 i.toUInt32 zzTable[i]
      for i in [:ctTableFull.size] do
        if h2 : i < ctTableFull.size then
          JIT.setMem cavlcHandle 2 i.toUInt32 ctTableFull[i]
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

      -- Set nCTableSelect (port 1) and start (port 0)
      JIT.setInput cavlcHandle 1 tableSel.toUInt64  -- nCTableSelect
      JIT.setInput cavlcHandle 0 1  -- start
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

      allBitstreams := allBitstreams.push (BitVec.ofNat 32 bsData.toNat, bpData.toNat)

      -- Verify against pure reference with nC
      let (refBits, refLen) := cavlcEncodeFull levels (nC := nC)
      if bsData.toNat != refBits.toNat || bpData.toNat != refLen then
        IO.eprintln s!"    MISMATCH block scan={scanIdx} ({bx},{by_}): nC={nC} tableSel={tableSel}"
        IO.eprintln s!"      JIT: 0x{String.ofList (Nat.toDigits 16 bsData.toNat)} ({bpData} bits)"
        IO.eprintln s!"      Ref: 0x{String.ofList (Nat.toDigits 16 refBits.toNat)} ({refLen} bits)"
        pass := false
      else if scanIdx < 4 then
        IO.println s!"    Block scan={scanIdx} ({bx},{by_}): nC={nC} tableSel={tableSel} → {bpData} bits ✓"

  JIT.destroy encHandle
  JIT.destroy decHandle
  JIT.destroy cavlcHandle

  if pass then
    IO.println "  All 16 blocks verified against pure reference ✓"
  else
    IO.eprintln "  WARNING: Some blocks did not match reference"

  -- ================================================================
  -- Phase 3: Assemble Annex-B bitstream
  -- ================================================================
  IO.println "  Phase 3: Assembling Annex-B bitstream..."

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

  -- Build output one byte at a time using a bit buffer
  -- (Avoids Nat overflow from accumulating hundreds of bits)
  let mut outBitBuf : Nat := 0
  let mut outBitPos : Nat := 0  -- number of valid bits in outBitBuf (MSB-first)

  -- Helper: extract the top N bits from a byte array with known valid bit count
  -- For sliceHeaderBits: 4 bytes, 27 valid bits (MSB-aligned)
  -- For mbHeaderBits: 3 bytes, 21 valid bits (MSB-aligned)

  -- Write slice header bits (27 valid bits from MSB of sliceHeaderBits)
  let mut sliceBitsRemaining := sliceHeaderBitLen
  for byte in sliceHeaderBits do
    let bitsToWrite := min 8 sliceBitsRemaining
    if bitsToWrite > 0 then
      let topBits := byte.toNat >>> (8 - bitsToWrite)
      outBitBuf := (outBitBuf <<< bitsToWrite) ||| topBits
      outBitPos := outBitPos + bitsToWrite
      sliceBitsRemaining := sliceBitsRemaining - bitsToWrite
      -- Flush complete bytes
      while outBitPos >= 8 do
        let byteVal := (outBitBuf >>> (outBitPos - 8)) &&& 0xFF
        outputBytes := outputBytes.push byteVal.toUInt8
        outBitPos := outBitPos - 8
        outBitBuf := outBitBuf &&& ((1 <<< outBitPos) - 1)

  -- Write MB header bits (21 valid bits from MSB of mbHeaderBits)
  let mut mbBitsRemaining := mbHeaderBitLen
  for byte in mbHeaderBits do
    let bitsToWrite := min 8 mbBitsRemaining
    if bitsToWrite > 0 then
      let topBits := byte.toNat >>> (8 - bitsToWrite)
      outBitBuf := (outBitBuf <<< bitsToWrite) ||| topBits
      outBitPos := outBitPos + bitsToWrite
      mbBitsRemaining := mbBitsRemaining - bitsToWrite
      while outBitPos >= 8 do
        let byteVal := (outBitBuf >>> (outBitPos - 8)) &&& 0xFF
        outputBytes := outputBytes.push byteVal.toUInt8
        outBitPos := outBitPos - 8
        outBitBuf := outBitBuf &&& ((1 <<< outBitPos) - 1)

  let headerBitLen := sliceHeaderBitLen + mbHeaderBitLen

  -- Write CAVLC bitstreams for all 16 blocks (in H.264 scan order)
  let mut cavlcTotalBits := 0
  for entry in allBitstreams do
    let (bs, blen) := entry
    if blen > 0 then
      cavlcTotalBits := cavlcTotalBits + blen
      let topBits := bs.toNat >>> (32 - blen)
      outBitBuf := (outBitBuf <<< blen) ||| topBits
      outBitPos := outBitPos + blen
      while outBitPos >= 8 do
        let byteVal := (outBitBuf >>> (outBitPos - 8)) &&& 0xFF
        outputBytes := outputBytes.push byteVal.toUInt8
        outBitPos := outBitPos - 8
        outBitBuf := outBitBuf &&& ((1 <<< outBitPos) - 1)

  -- RBSP trailing bits: 1 bit followed by 0s to byte-align
  let totalPayloadBits := headerBitLen + cavlcTotalBits
  -- rbsp_stop_one_bit
  outBitBuf := (outBitBuf <<< 1) ||| 1
  outBitPos := outBitPos + 1
  -- Alignment zeros
  let alignZeros := (8 - ((totalPayloadBits + 1) % 8)) % 8
  if alignZeros > 0 then
    outBitBuf := outBitBuf <<< alignZeros
    outBitPos := outBitPos + alignZeros

  -- Flush remaining bits
  while outBitPos >= 8 do
    let byteVal := (outBitBuf >>> (outBitPos - 8)) &&& 0xFF
    outputBytes := outputBytes.push byteVal.toUInt8
    outBitPos := outBitPos - 8
    outBitBuf := outBitBuf &&& ((1 <<< outBitPos) - 1)

  IO.println s!"  Total output: {outputBytes.size} bytes"
  IO.println s!"  Header bits: {headerBitLen}, CAVLC bits: {cavlcTotalBits}, align: {alignZeros}+1 (rbsp trailing)"

  -- Write .h264 file
  let outputPath := "IP/Video/H264/gen/test_playable.h264"
  let byteArray := ByteArray.mk outputBytes
  IO.FS.writeBinFile outputPath byteArray
  IO.println s!"  Written to {outputPath}"

  -- ================================================================
  -- Phase 4: Wrap in MP4 container
  -- ================================================================
  IO.println "  Phase 4: Wrapping in MP4 container..."

  -- Extract SPS bytes without start code (skip first 4 bytes: 00 00 00 01)
  let spsBytes : ByteArray := Id.run do
    let mut ba : ByteArray := ByteArray.empty
    for i in [4:spsNALUnit.size] do
      if h : i < spsNALUnit.size then
        ba := ba.push spsNALUnit[i].toNat.toUInt8
    ba

  -- Extract PPS bytes without start code
  let ppsBytes : ByteArray := Id.run do
    let mut ba : ByteArray := ByteArray.empty
    for i in [4:ppsNALUnit.size] do
      if h : i < ppsNALUnit.size then
        ba := ba.push ppsNALUnit[i].toNat.toUInt8
    ba

  -- Extract IDR NAL bytes without start code:
  -- The IDR NAL = NAL header (0x65) + slice header bits + MB header bits + CAVLC data + RBSP trailing
  -- This is outputBytes starting after SPS NAL + PPS NAL + IDR start code (4 bytes)
  -- i.e., from the 0x65 byte onward
  let spsSize := spsNALUnit.size    -- 15 bytes (start code + SPS RBSP)
  let ppsSize := ppsNALUnit.size    -- 8 bytes (start code + PPS RBSP)
  let idrStartOffset := spsSize + ppsSize + 4  -- skip SPS + PPS + IDR start code (00 00 00 01)
  let idrBytes : ByteArray := Id.run do
    let mut ba : ByteArray := ByteArray.empty
    for i in [idrStartOffset:outputBytes.size] do
      if h : i < outputBytes.size then
        ba := ba.push outputBytes[i]
    ba

  let mp4 := muxSingleFrame spsBytes ppsBytes idrBytes 16 16
  let mp4Path := "IP/Video/H264/gen/test_playable.mp4"
  IO.FS.writeBinFile mp4Path mp4
  IO.println s!"  MP4 written: {mp4.size} bytes → {mp4Path}"
  IO.println s!"    SPS: {spsBytes.size} bytes, PPS: {ppsBytes.size} bytes, IDR: {idrBytes.size} bytes"

  -- Summary
  IO.println "\n  Summary:"
  IO.println s!"    Blocks encoded: 16 (4×4 in 16×16 macroblock)"
  IO.println s!"    nC-dependent CAVLC: yes (all 4 table ranges available)"
  IO.println s!"    Prediction: DC (mode 2) for all blocks"
  IO.println s!"    QP: {qp}"

  -- Print nC distribution
  let mut ncDist : Array Nat := Array.replicate 4 0
  for scanIdx in [:16] do
    if h : scanIdx < scanOrder.size then
      let (bx, by_) := scanOrder[scanIdx]
      let leftTC : Option Nat :=
        if bx > 0 then
          let leftIdx := by_ * 4 + (bx - 1)
          if h2 : leftIdx < tcMap.size then some tcMap[leftIdx] else none
        else none
      let topTC : Option Nat :=
        if by_ > 0 then
          let topIdx := (by_ - 1) * 4 + bx
          if h2 : topIdx < tcMap.size then some tcMap[topIdx] else none
        else none
      let nC := computeNC leftTC topTC
      let ts := nCToTableSelect nC
      if h2 : ts < ncDist.size then
        ncDist := ncDist.set! ts (ncDist[ts] + 1)

  IO.println s!"    nC table distribution: VLC0={ncDist[0]!} VLC1={ncDist[1]!} VLC2={ncDist[2]!} FLC={ncDist[3]!}"

  return pass

-- ============================================================================
-- Main
-- ============================================================================

def main : IO UInt32 := do
  IO.println "H.264 Playable Stream Test"
  IO.println "=========================="

  let r1 ← testPlayableStream

  IO.println "\n=========================="
  if r1 then
    IO.println "TEST PASSED — playable .h264 and .mp4 generated"
    IO.println "  ffplay -vf \"scale=256:256:flags=neighbor\" IP/Video/H264/gen/test_playable.h264"
    IO.println "  ffplay -vf \"scale=256:256:flags=neighbor\" IP/Video/H264/gen/test_playable.mp4"
    return 0
  else
    IO.eprintln "TEST FAILED"
    return 1
