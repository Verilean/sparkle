/-
  H.264 Autonomous Frame Encoder

  A single hardware module that takes a 16×16 frame and produces a complete
  H.264 Annex-B byte stream (SPS + PPS + IDR slice), ready for MP4 wrapping.

  Architecture:
    - Block sequencer FSM (20 major phases)
    - Bitstream packer (MSB-aligned bit buffer → byte output)
    - 3 nested sub-modules: encoderPipelineV2, decoderPipelineV2, cavlcSynthModule
    - Internal memories: frame, recon, quantized levels, totalCoeff map,
      CAVLC bitstream data, CAVLC bitstream lengths

  Bit buffer design (MSB-aligned, 64-bit):
    - 64-bit accumulator prevents overflow when packing up to 32 CAVLC bits
    - Top byte to emit is always at [63:56] — no variable-position extraction
    - Drain: when pos >= 8, emit buf[63:56], shift left 8, pos -= 8
    - Pack: when pos < 8, OR in new bits shifted right by pos

  Reference: ITU-T H.264 Annex B, Section 7, 8, 9
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.EncoderSynth
import IP.Video.H264.DecoderSynth
import IP.Video.H264.CAVLCSynth
import IP.Video.H264.VLCTables
import IP.Video.H264.SPSPPSData
import IP.Video.H264.Encoder
import IP.Video.H264.CAVLC

set_option maxRecDepth 8192
set_option maxHeartbeats 12800000

namespace Sparkle.IP.Video.H264.FrameEncoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.IP.Video.H264.EncoderSynth
open Sparkle.IP.Video.H264.DecoderSynth
open Sparkle.IP.Video.H264.CAVLCSynth

-- ============================================================================
-- State definition (~20 registers)
-- ============================================================================

declare_signal_state FrameEncoderState
  | mainPhase     : BitVec 5  := 0#5
  | blockIdx      : BitVec 5  := 0#5
  | pixIdx        : BitVec 5  := 0#5
  | subPhase      : BitVec 3  := 0#3
  | dcPred        : BitVec 16 := 128#16
  | curTotalCoeff : BitVec 5  := 0#5
  | scanIdx       : BitVec 5  := 0#5
  | outBitBuf     : BitVec 64 := 0#64   -- MSB-aligned, 64-bit to avoid overflow
  | outBitPos     : BitVec 7  := 0#7
  | headerIdx     : BitVec 7  := 0#7
  | done          : Bool      := false
  | outValid      : Bool      := false
  | outByte       : BitVec 8  := 0#8
  | encStartPulse : Bool      := false
  | decStartPulse : Bool      := false
  | cavlcStartPulse : Bool    := false
  | nCTableSel    : BitVec 2  := 0#2
  | dcSum         : BitVec 16 := 0#16
  | dcCount       : BitVec 4  := 0#4
  | waitCycles    : BitVec 2  := 0#2
  | leftTC        : BitVec 5  := 0#5

-- ============================================================================
-- FSM phase constants
-- ============================================================================

private def PH_IDLE              : BitVec 5 := 0#5
private def PH_EMIT_FIXED_HDR   : BitVec 5 := 1#5
private def PH_EMIT_SLICE_MB    : BitVec 5 := 2#5
private def PH_COMPUTE_DC       : BitVec 5 := 3#5
private def PH_LOAD_ENCODER     : BitVec 5 := 4#5
private def PH_RUN_ENCODER      : BitVec 5 := 5#5
private def PH_READ_QUANT       : BitVec 5 := 6#5
private def PH_COUNT_TC         : BitVec 5 := 7#5
private def PH_LOAD_DECODER     : BitVec 5 := 8#5
private def PH_RUN_DECODER      : BitVec 5 := 9#5
private def PH_READ_RECON       : BitVec 5 := 10#5
private def PH_NEXT_RASTER      : BitVec 5 := 11#5
private def PH_COMPUTE_NC       : BitVec 5 := 12#5
private def PH_LOAD_CAVLC       : BitVec 5 := 13#5
private def PH_RUN_CAVLC        : BitVec 5 := 14#5
private def PH_READ_CAVLC_BS    : BitVec 5 := 15#5
private def PH_EMIT_CAVLC_BITS  : BitVec 5 := 16#5
private def PH_NEXT_SCAN        : BitVec 5 := 17#5
private def PH_EMIT_TRAILING    : BitVec 5 := 18#5
private def PH_DONE             : BitVec 5 := 19#5

-- ============================================================================
-- Autonomous frame encoder
-- ============================================================================

def h264FrameEncoder {dom : DomainConfig}
    (start : Signal dom Bool)
    (frameWriteEn : Signal dom Bool)
    (frameWriteAddr : Signal dom (BitVec 8))
    (frameWriteData : Signal dom (BitVec 16))
    (quantMF0 quantMF1 quantMF2 : Signal dom (BitVec 32))
    (quantF : Signal dom (BitVec 32))
    (quantShift : Signal dom (BitVec 5))
    (vscale0 vscale1 vscale2 : Signal dom (BitVec 32))
    (ctWriteEn : Signal dom Bool) (ctWriteAddr : Signal dom (BitVec 9)) (ctWriteData : Signal dom (BitVec 32))
    (tzWriteEn : Signal dom Bool) (tzWriteAddr : Signal dom (BitVec 7)) (tzWriteData : Signal dom (BitVec 32))
    (rbWriteEn : Signal dom Bool) (rbWriteAddr : Signal dom (BitVec 6)) (rbWriteData : Signal dom (BitVec 32))
    (zzWriteEn : Signal dom Bool) (zzWriteAddr : Signal dom (BitVec 4)) (zzWriteData : Signal dom (BitVec 16))
    : Signal dom (BitVec 8 × Bool × Bool) :=
  let loopState := Signal.loop fun state =>
    -- Extract state registers
    let mainPhase := FrameEncoderState.mainPhase state
    let blockIdx  := FrameEncoderState.blockIdx state
    let pixIdx    := FrameEncoderState.pixIdx state
    let subPhase  := FrameEncoderState.subPhase state
    let dcPred    := FrameEncoderState.dcPred state
    let curTC     := FrameEncoderState.curTotalCoeff state
    let scanIdx   := FrameEncoderState.scanIdx state
    let outBitBuf := FrameEncoderState.outBitBuf state
    let outBitPos := FrameEncoderState.outBitPos state
    let headerIdx := FrameEncoderState.headerIdx state
    let nCTblSel  := FrameEncoderState.nCTableSel state
    let leftTC    := FrameEncoderState.leftTC state

    -- Phase comparisons
    let isIdle      := mainPhase === (PH_IDLE : Signal dom _)
    let isEmitHdr   := mainPhase === (PH_EMIT_FIXED_HDR : Signal dom _)
    let isEmitSlMb  := mainPhase === (PH_EMIT_SLICE_MB : Signal dom _)
    let isCompDC    := mainPhase === (PH_COMPUTE_DC : Signal dom _)
    let isLoadEnc   := mainPhase === (PH_LOAD_ENCODER : Signal dom _)
    let isRunEnc    := mainPhase === (PH_RUN_ENCODER : Signal dom _)
    let isReadQuant := mainPhase === (PH_READ_QUANT : Signal dom _)
    let isCountTC   := mainPhase === (PH_COUNT_TC : Signal dom _)
    let isLoadDec   := mainPhase === (PH_LOAD_DECODER : Signal dom _)
    let isRunDec    := mainPhase === (PH_RUN_DECODER : Signal dom _)
    let isReadRecon := mainPhase === (PH_READ_RECON : Signal dom _)
    let isNextRaster := mainPhase === (PH_NEXT_RASTER : Signal dom _)
    let isCompNC    := mainPhase === (PH_COMPUTE_NC : Signal dom _)
    let isLoadCAVLC := mainPhase === (PH_LOAD_CAVLC : Signal dom _)
    let isRunCAVLC  := mainPhase === (PH_RUN_CAVLC : Signal dom _)
    let isReadCBS   := mainPhase === (PH_READ_CAVLC_BS : Signal dom _)
    let isEmitCBits := mainPhase === (PH_EMIT_CAVLC_BITS : Signal dom _)
    let isNextScan  := mainPhase === (PH_NEXT_SCAN : Signal dom _)
    let isEmitTrail := mainPhase === (PH_EMIT_TRAILING : Signal dom _)
    let isDone      := mainPhase === (PH_DONE : Signal dom _)

    let startAndIdle := start &&& isIdle

    -- ================================================================
    -- Block position from raster index (all in 8-bit)
    -- bx = blockIdx & 3, by_ = (blockIdx >> 2) & 3
    -- ================================================================
    let bx2 := blockIdx.map (BitVec.extractLsb' 0 2 ·)   -- bits [1:0] = blockIdx & 3
    let by2 := blockIdx.map (BitVec.extractLsb' 2 2 ·)   -- bits [3:2] = (blockIdx >> 2) & 3
    let bx8 := 0#6 ++ bx2      -- 8-bit bx
    let by8 := 0#6 ++ by2      -- 8-bit by

    -- Scan order: H.264 4×4 block scan = bit interleave
    -- scanBx = {scanIdx[2], scanIdx[0]}, scanBy = {scanIdx[1], scanIdx[3]}
    let scanBx_b0 := scanIdx.map (BitVec.extractLsb' 0 1 ·)
    let scanBx_b1 := scanIdx.map (BitVec.extractLsb' 2 1 ·)
    let scanBx2 := scanBx_b1 ++ scanBx_b0  -- 2-bit
    let scanBy_b0 := scanIdx.map (BitVec.extractLsb' 1 1 ·)
    let scanBy_b1 := scanIdx.map (BitVec.extractLsb' 3 1 ·)
    let scanBy2 := scanBy_b1 ++ scanBy_b0  -- 2-bit
    let scanBx4 := 0#2 ++ scanBx2  -- 4-bit
    let scanBy4 := 0#2 ++ scanBy2  -- 4-bit
    let scanBx8 := 0#6 ++ scanBx2  -- 8-bit
    let scanBy8 := 0#6 ++ scanBy2  -- 8-bit

    -- ================================================================
    -- Frame buffer addressing (8-bit addr, 16×16 pixels)
    -- addr = (by*4 + pixRow) * 16 + (bx*4 + pixCol)
    -- ================================================================
    let pixRow := pixIdx.map (BitVec.extractLsb' 2 2 ·)
    let pixCol := pixIdx.map (BitVec.extractLsb' 0 2 ·)
    let pixRow8 := 0#6 ++ pixRow
    let pixCol8 := 0#6 ++ pixCol
    -- by*4: zero-extend by to 8 bits, multiply
    let by4_8 := by8 * 4#8
    let bx4_8 := bx8 * 4#8
    let row8 := by4_8 + pixRow8
    let col8 := bx4_8 + pixCol8
    let frameReadAddr := (row8 * 16#8) + col8

    let frameActiveRead := isLoadEnc ||| isCompDC
    let frameRdAddr := Signal.mux frameActiveRead frameReadAddr (Signal.pure 0#8)
    let frameData := Signal.memoryComboRead frameWriteAddr frameWriteData frameWriteEn frameRdAddr

    -- Recon buffer (256×16-bit)
    let reconWriteAddr := Signal.mux isReadRecon frameReadAddr (Signal.pure 0#8)
    let reconReadAddr := Signal.mux (isCompDC ||| isReadRecon) frameReadAddr (Signal.pure 0#8)

    -- Quantized levels storage (256×16-bit: 16 blocks × 16 coefficients)
    -- raster write addr: blockIdx*16 + pixIdx (in 8-bit)
    let blockIdx8 := 0#3 ++ blockIdx
    let pixIdx8 := 0#3 ++ pixIdx
    let quantStoreWriteAddr := (blockIdx8 * 16#8) + pixIdx8
    -- scan read addr: scanBlockIdx*16 + pixIdx
    let scanBlockIdx8 := (scanBy8 * 4#8) + scanBx8
    let quantStoreReadAddr := (scanBlockIdx8 * 16#8) + pixIdx8

    -- totalCoeff map (16×16-bit memory, 4-bit addr)
    let bx4 := 0#2 ++ bx2      -- 4-bit bx
    let by4 := 0#2 ++ by2      -- 4-bit by
    let tcMapAddr := (by4 * 4#4) + bx4

    -- Scan-order tcMap read addr for nC computation
    let tcMapScanAddr := (scanBy4 * 4#4) + scanBx4

    -- CAVLC bitstream storage (16-entry, 4-bit addr)
    let scanIdx4 := scanIdx.map (BitVec.extractLsb' 0 4 ·)

    -- ================================================================
    -- Sub-module instantiation
    -- ================================================================

    -- Encoder sub-module
    let encStartPulse := isRunEnc &&& (subPhase === (0#3 : Signal dom _))
    let encOrigWrEn := isLoadEnc
    let encOrigWrAddr := pixIdx.map (BitVec.extractLsb' 0 4 ·)
    let encOrigWrData := frameData
    let encPredWrEn := isLoadEnc
    let encPredWrAddr := pixIdx.map (BitVec.extractLsb' 0 4 ·)
    let encPredWrData := dcPred
    -- Pre-fetch: encoder V2 output has 1-cycle register latency, so read addr+1
    -- During RUN_ENCODER default addr=0 pre-fetches mem[0], so READ_QUANT starts correct
    let encQuantReadAddrP1 := (pixIdx.map (BitVec.extractLsb' 0 4 ·)) + 1#4
    let encQuantReadAddr := Signal.mux isReadQuant
      encQuantReadAddrP1 (Signal.pure 0#4)

    let encOutput := encoderPipelineV2
      encStartPulse encOrigWrEn encOrigWrAddr encOrigWrData
      encPredWrEn encPredWrAddr encPredWrData
      quantMF0 quantMF1 quantMF2 quantF quantShift
      encQuantReadAddr
    let encDone := projN! encOutput 3 0
    let encDoneFlag := ~~~(encDone === (0#32 : Signal dom _))
    let encQuantData := projN! encOutput 3 2

    -- Quantized levels storage memory (must be defined before decoder)
    let quantStoreWrEn := isReadQuant
    -- Read address: raster addressing for LOAD_DEC/COUNT_TC, scan addressing for LOAD_CAVLC
    let rasterRdAddr := quantStoreWriteAddr  -- blockIdx*16+pixIdx (raster order)
    let quantStoreRdAddr := Signal.mux isLoadCAVLC quantStoreReadAddr
      (Signal.mux (isLoadDec ||| isCountTC) rasterRdAddr (Signal.pure 0#8))
    let quantStoreMem := Signal.memoryComboRead quantStoreWriteAddr encQuantData quantStoreWrEn quantStoreRdAddr

    -- Decoder sub-module
    let decStartPulse := isRunDec &&& (subPhase === (0#3 : Signal dom _))
    let decCoeffWrEn := isLoadDec
    let decCoeffWrAddr := pixIdx.map (BitVec.extractLsb' 0 4 ·)
    let decPredWrEn := isLoadDec
    let decPredWrAddr := pixIdx.map (BitVec.extractLsb' 0 4 ·)
    let decPredWrData := dcPred
    -- Pre-fetch: decoder V2 output has 1-cycle register latency, so read addr+1
    let decReconReadAddrP1 := (pixIdx.map (BitVec.extractLsb' 0 4 ·)) + 1#4
    let decReconReadAddr := Signal.mux isReadRecon
      decReconReadAddrP1 (Signal.pure 0#4)

    let decOutput := decoderPipelineV2
      decStartPulse decCoeffWrEn decCoeffWrAddr quantStoreMem
      decPredWrEn decPredWrAddr decPredWrData
      vscale0 vscale1 vscale2
      decReconReadAddr
    let decDone := projN! decOutput 3 0
    let decDoneFlag := ~~~(decDone === (0#32 : Signal dom _))
    let decReconData := projN! decOutput 3 2

    -- Recon buffer memory
    let reconWrEn := isReadRecon
    let _reconData := Signal.memoryComboRead reconWriteAddr decReconData reconWrEn reconReadAddr

    -- CAVLC sub-module
    let cavlcStartPulse := isRunCAVLC &&& (subPhase === (0#3 : Signal dom _))
    let cavlcCoeffWrEn := isLoadCAVLC
    let cavlcCoeffWrAddr := pixIdx.map (BitVec.extractLsb' 0 4 ·)
    let cavlcCoeffWrData := quantStoreMem.map (BitVec.extractLsb' 0 16 ·)

    let cavlcOutput := cavlcSynthModule
      cavlcStartPulse nCTblSel
      cavlcCoeffWrEn cavlcCoeffWrAddr cavlcCoeffWrData
      ctWriteEn ctWriteAddr ctWriteData
      tzWriteEn tzWriteAddr tzWriteData
      rbWriteEn rbWriteAddr rbWriteData
      zzWriteEn zzWriteAddr zzWriteData
    let cavlcBitBuffer := projN! cavlcOutput 4 0
    let cavlcBitPos    := projN! cavlcOutput 4 1
    let cavlcDone      := projN! cavlcOutput 4 2
    let cavlcDoneFlag  := ~~~(cavlcDone === (0#32 : Signal dom _))

    -- CAVLC bitstream storage memories
    let cavlcBsWrEn := isReadCBS
    let cavlcBsData := Signal.memoryComboRead scanIdx4 cavlcBitBuffer cavlcBsWrEn scanIdx4
    let cavlcBsLen  := Signal.memoryComboRead scanIdx4 cavlcBitPos cavlcBsWrEn scanIdx4

    -- totalCoeff map memory
    let tcMapWrEn := isCountTC &&& (pixIdx === (16#5 : Signal dom _))
    let tcMapWrData := 0#11 ++ curTC
    -- nC: read left in subPhase 0, top in subPhase 1, then average per H.264 spec
    let hasLeft := ~~~(scanBx2 === (0#2 : Signal dom _))
    let hasTop  := ~~~(scanBy2 === (0#2 : Signal dom _))
    let leftNcAddr := tcMapScanAddr - 1#4
    let topNcAddr  := tcMapScanAddr - 4#4
    let isCompNCSub0 := isCompNC &&& (subPhase === (0#3 : Signal dom _))
    -- subPhase 0: read left neighbor; subPhase 1: read top neighbor
    let ncReadAddr := Signal.mux isCompNCSub0 leftNcAddr topNcAddr
    let tcMapRdAddr := Signal.mux isCompNC ncReadAddr tcMapAddr
    let tcMapData := Signal.memoryComboRead tcMapAddr tcMapWrData tcMapWrEn tcMapRdAddr

    -- ================================================================
    -- Bit buffer (MSB-aligned)
    -- ================================================================
    -- bpGe8: outBitPos >= 8 iff bits [6:3] nonzero
    let bpHigh := outBitPos.map (BitVec.extractLsb' 3 4 ·)
    let bpGe8 := ~~~(bpHigh === (0#4 : Signal dom _))
    -- Top byte always at [63:56]
    let topByte := outBitBuf.map (BitVec.extractLsb' 56 8 ·)
    -- After emitting: shift left 8, pos -= 8
    let newBufAfterByte := outBitBuf <<< 8#64
    let newPosAfterByte := outBitPos - 8#7

    -- pos64: zero-extended for shift operations
    let pos64 := 0#57 ++ outBitPos

    -- nC computation: average left and top totalCoeff per H.264 Section 9.2.1
    -- leftTC register holds left neighbor TC from subPhase 0 read
    -- tcMapData in subPhase 1 holds top neighbor TC
    let topTC := tcMapData.map (BitVec.extractLsb' 0 5 ·)
    -- Average: (leftTC + topTC + 1) >> 1
    let leftTC6 := 0#1 ++ leftTC
    let topTC6 := 0#1 ++ topTC
    let sumP1_6 := (leftTC6 + topTC6) + 1#6
    let avg5 := sumP1_6.map (BitVec.extractLsb' 1 5 ·)
    let nCVal := Signal.mux (hasLeft &&& hasTop) avg5
      (Signal.mux hasLeft leftTC
        (Signal.mux hasTop topTC (Signal.pure 0#5)))
    -- Classify nC into table select
    let nCHigh4 := nCVal.map (BitVec.extractLsb' 1 4 ·)  -- zero iff val < 2
    let nCHigh3 := nCVal.map (BitVec.extractLsb' 2 3 ·)  -- zero iff val < 4
    let nCHigh2 := nCVal.map (BitVec.extractLsb' 3 2 ·)  -- zero iff val < 8
    let nCLt2 := nCHigh4 === (0#4 : Signal dom _)
    let nCLt4 := nCHigh3 === (0#3 : Signal dom _)
    let nCLt8 := nCHigh2 === (0#2 : Signal dom _)
    let nCComputed := Signal.mux nCLt2 (Signal.pure 0#2)
      (Signal.mux nCLt4 (Signal.pure 1#2)
        (Signal.mux nCLt8 (Signal.pure 2#2) (Signal.pure 3#2)))

    -- ================================================================
    -- Completion conditions
    -- ================================================================
    let hdrDone := isEmitHdr &&& (headerIdx === (BitVec.ofNat 7 28 : Signal dom _))
    let pixDone16 := pixIdx === (15#5 : Signal dom _)
    let pixAt16 := pixIdx === (16#5 : Signal dom _)
    let lastRasterBlock := blockIdx === (15#5 : Signal dom _)
    let lastScanBlock := scanIdx === (15#5 : Signal dom _)
    let slMbDone := isEmitSlMb &&& (headerIdx === (7#7 : Signal dom _))
    let notBpGe8 := ~~~bpGe8

    -- ================================================================
    -- Fixed header ROM: 2-level mux tree (4 groups × 8 entries)
    -- SPS: 00 00 00 01 67 42 C0 0A 8C 69 C8 07 84 42 35
    -- PPS: 00 00 00 01 68 CE 3C 80
    -- IDR: 00 00 00 01 65
    -- ================================================================
    let hdrLo3 := headerIdx.map (BitVec.extractLsb' 0 3 ·)
    let hdrHi2 := headerIdx.map (BitVec.extractLsb' 3 2 ·)
    -- Group 0 (idx 0-7): SPS start
    let grp0 := Signal.mux (hdrLo3 === 7#3) (Signal.pure 0x0A#8)
      (Signal.mux (hdrLo3 === 6#3) (Signal.pure 0xC0#8)
        (Signal.mux (hdrLo3 === 5#3) (Signal.pure 0x42#8)
          (Signal.mux (hdrLo3 === 4#3) (Signal.pure 0x67#8)
            (Signal.mux (hdrLo3 === 3#3) (Signal.pure 0x01#8)
              (Signal.pure 0x00#8)))))
    -- Group 1 (idx 8-15): SPS end + PPS start
    let grp1 := Signal.mux (hdrLo3 === 7#3) (Signal.pure 0x00#8)
      (Signal.mux (hdrLo3 === 6#3) (Signal.pure 0x35#8)
        (Signal.mux (hdrLo3 === 5#3) (Signal.pure 0x42#8)
          (Signal.mux (hdrLo3 === 4#3) (Signal.pure 0x84#8)
            (Signal.mux (hdrLo3 === 3#3) (Signal.pure 0x07#8)
              (Signal.mux (hdrLo3 === 2#3) (Signal.pure 0xC8#8)
                (Signal.mux (hdrLo3 === 1#3) (Signal.pure 0x69#8)
                  (Signal.pure 0x8C#8)))))))
    -- Group 2 (idx 16-23): PPS + IDR start
    let grp2 := Signal.mux (hdrLo3 === 7#3) (Signal.pure 0x00#8)
      (Signal.mux (hdrLo3 === 6#3) (Signal.pure 0x80#8)
        (Signal.mux (hdrLo3 === 5#3) (Signal.pure 0x3C#8)
          (Signal.mux (hdrLo3 === 4#3) (Signal.pure 0xCE#8)
            (Signal.mux (hdrLo3 === 3#3) (Signal.pure 0x68#8)
              (Signal.mux (hdrLo3 === 2#3) (Signal.pure 0x01#8)
                (Signal.mux (hdrLo3 === 1#3) (Signal.pure 0x00#8)
                  (Signal.pure 0x00#8)))))))
    -- Group 3 (idx 24-27): IDR
    let grp3 := Signal.mux (hdrLo3 === 3#3) (Signal.pure 0x65#8)
      (Signal.mux (hdrLo3 === 2#3) (Signal.pure 0x01#8)
        (Signal.mux (hdrLo3 === 1#3) (Signal.pure 0x00#8)
          (Signal.pure 0x00#8)))
    -- Select group
    let hdrByte := Signal.mux (hdrHi2 === 3#2) grp3
      (Signal.mux (hdrHi2 === 2#2) grp2
        (Signal.mux (hdrHi2 === 1#2) grp1 grp0))
    let emitHdrValid := isEmitHdr &&& (~~~hdrDone)

    -- Slice+MB header ROM as mux chain (7 bytes, 49 bits)
    let hdrIdx3 := headerIdx.map (BitVec.extractLsb' 0 3 ·)
    let slMbByte := Signal.mux (hdrIdx3 === 6#3) (Signal.pure 0xDC#8)
      (Signal.mux (hdrIdx3 === 5#3) (Signal.pure 0xFF#8)
        (Signal.mux (hdrIdx3 === 4#3) (Signal.pure 0xFF#8)
          (Signal.mux (hdrIdx3 === 3#3) (Signal.pure 0x40#8)
            (Signal.mux (hdrIdx3 === 2#3) (Signal.pure 0x09#8)
              (Signal.mux (hdrIdx3 === 1#3) (Signal.pure 0x00#8)
                (Signal.pure 0xB8#8))))))

    -- Bit packing control
    let packSlMbBits := isEmitSlMb &&& (~~~slMbDone) &&& notBpGe8
    -- Bits per byte: 8 except byte 3 (slice tail, 3 bits) and byte 6 (MB tail, 6 bits)
    let slMbBitsToWrite := Signal.mux
      (headerIdx === (3#7 : Signal dom _))
      (Signal.pure 3#7)
      (Signal.mux (headerIdx === (6#7 : Signal dom _))
        (Signal.pure 6#7)
        (Signal.pure 8#7))
    -- Place byte at top of 64-bit word, shift right by pos
    let slMbByteAtTop := slMbByte ++ 0#56
    let slMbShifted := slMbByteAtTop >>> pos64

    -- CAVLC bits: already MSB-aligned in cavlcBsData (64-bit from CAVLC module)
    let cavlcBitsToEmit := cavlcBsLen.map (BitVec.extractLsb' 0 7 ·)
    let cavlcShifted := cavlcBsData >>> pos64
    let packCavlcBits := isEmitCBits &&& (subPhase === (0#3 : Signal dom _)) &&& notBpGe8

    -- Combined packing
    let packingActive := packSlMbBits ||| packCavlcBits
    let newBitsToOR := Signal.mux packSlMbBits slMbShifted
      (Signal.mux packCavlcBits cavlcShifted (Signal.pure 0#64))
    let newBitsLen := Signal.mux packSlMbBits slMbBitsToWrite
      (Signal.mux packCavlcBits cavlcBitsToEmit (Signal.pure 0#7))
    let packedBuf := outBitBuf ||| newBitsToOR
    let packedPos := outBitPos + newBitsLen

    -- RBSP trailing: stop bit + byte alignment
    let trailingBit := isEmitTrail &&& (subPhase === (0#3 : Signal dom _)) &&& notBpGe8
    -- Stop bit at position (63 - pos): shift 0x8000000000000000 right by pos
    let stopBit := 0x8000000000000000#64 >>> pos64
    let trailBuf := outBitBuf ||| stopBit
    let trailPos := outBitPos + 1#7
    -- Align to byte boundary: (pos+1+7) & ~7 = (pos+1+7) & 0x78
    let trailAlignPos := (trailPos + 7#7) &&& 120#7

    -- Drain: emit bytes when pos >= 8 (in emission phases)
    let isDraining := bpGe8 &&& (isEmitSlMb ||| isEmitCBits ||| isEmitTrail)

    -- ================================================================
    -- FSM transitions
    -- ================================================================
    let phaseNext := hw_cond mainPhase
      | startAndIdle  => (PH_EMIT_FIXED_HDR : Signal dom _)
      | hdrDone       => (PH_EMIT_SLICE_MB : Signal dom _)
      | slMbDone      => (PH_COMPUTE_DC : Signal dom _)
      | (isCompDC &&& (subPhase === (1#3 : Signal dom _))) => (PH_LOAD_ENCODER : Signal dom _)
      | (isLoadEnc &&& pixDone16) => (PH_RUN_ENCODER : Signal dom _)
      | (isRunEnc &&& encDoneFlag &&& (subPhase === (2#3 : Signal dom _))) => (PH_READ_QUANT : Signal dom _)
      | (isReadQuant &&& pixDone16) => (PH_COUNT_TC : Signal dom _)
      | (isCountTC &&& pixAt16)  => (PH_LOAD_DECODER : Signal dom _)
      | (isLoadDec &&& pixDone16) => (PH_RUN_DECODER : Signal dom _)
      | (isRunDec &&& decDoneFlag &&& (subPhase === (2#3 : Signal dom _))) => (PH_READ_RECON : Signal dom _)
      | (isReadRecon &&& pixDone16) => (PH_NEXT_RASTER : Signal dom _)
      | (isNextRaster &&& lastRasterBlock) => (PH_COMPUTE_NC : Signal dom _)
      | isNextRaster  => (PH_COMPUTE_DC : Signal dom _)
      | (isCompNC &&& (subPhase === (1#3 : Signal dom _))) => (PH_LOAD_CAVLC : Signal dom _)
      | (isLoadCAVLC &&& pixDone16) => (PH_RUN_CAVLC : Signal dom _)
      | (isRunCAVLC &&& cavlcDoneFlag &&& (subPhase === (2#3 : Signal dom _))) => (PH_READ_CAVLC_BS : Signal dom _)
      | isReadCBS     => (PH_EMIT_CAVLC_BITS : Signal dom _)
      | (isEmitCBits &&& (subPhase === (1#3 : Signal dom _)) &&& notBpGe8) => (PH_NEXT_SCAN : Signal dom _)
      | (isNextScan &&& lastScanBlock) => (PH_EMIT_TRAILING : Signal dom _)
      | isNextScan    => (PH_COMPUTE_NC : Signal dom _)
      | (isEmitTrail &&& (subPhase === (1#3 : Signal dom _)) &&& notBpGe8) => (PH_DONE : Signal dom _)
      | isDone        => (PH_IDLE : Signal dom _)

    let blockIdxNext := hw_cond blockIdx
      | startAndIdle => (0#5 : Signal dom _)
      | (isNextRaster &&& (~~~lastRasterBlock)) =>
          blockIdx + 1#5

    let scanIdxNext := hw_cond scanIdx
      | startAndIdle => (0#5 : Signal dom _)
      | (isNextScan &&& (~~~lastScanBlock)) =>
          scanIdx + 1#5

    let pixIdxInc := pixIdx + 1#5
    let pixIdxNext := hw_cond (0#5 : Signal dom _)
      | startAndIdle => (0#5 : Signal dom _)
      | (isCompDC &&& (subPhase === (1#3 : Signal dom _))) => (0#5 : Signal dom _)
      | isLoadEnc  => pixIdxInc
      | (isReadQuant &&& pixDone16) => (0#5 : Signal dom _)  -- reset for COUNT_TC entry
      | isReadQuant => pixIdxInc
      | (isCountTC &&& pixAt16) => (0#5 : Signal dom _)  -- reset for LOAD_DECODER entry
      | isCountTC  => pixIdxInc
      | isLoadDec  => pixIdxInc
      | isReadRecon => pixIdxInc
      | isLoadCAVLC => pixIdxInc
      | (isRunEnc &&& encDoneFlag) => (0#5 : Signal dom _)
      | (isRunDec &&& decDoneFlag) => (0#5 : Signal dom _)
      | (isRunCAVLC &&& cavlcDoneFlag) => (0#5 : Signal dom _)

    let subPhaseNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | isCompDC     => Signal.mux (subPhase === (1#3 : Signal dom _)) (Signal.pure 0#3) (Signal.pure 1#3)
      | isRunEnc     => Signal.mux (subPhase === (2#3 : Signal dom _))
          (Signal.mux encDoneFlag (Signal.pure 0#3) (Signal.pure 2#3))
          (subPhase + 1#3)
      | isRunDec     => Signal.mux (subPhase === (2#3 : Signal dom _))
          (Signal.mux decDoneFlag (Signal.pure 0#3) (Signal.pure 2#3))
          (subPhase + 1#3)
      | isRunCAVLC   => Signal.mux (subPhase === (2#3 : Signal dom _))
          (Signal.mux cavlcDoneFlag (Signal.pure 0#3) (Signal.pure 2#3))
          (subPhase + 1#3)
      | isCompNC     => Signal.mux (subPhase === (1#3 : Signal dom _)) (Signal.pure 0#3) (Signal.pure 1#3)
      | isEmitCBits  => Signal.mux (subPhase === (0#3 : Signal dom _))
          (Signal.mux notBpGe8 (Signal.pure 1#3) (Signal.pure 0#3))
          (Signal.pure 1#3)
      | isEmitTrail  => Signal.mux trailingBit (Signal.pure 1#3) subPhase

    let headerIdxInc := headerIdx + 1#7
    let headerIdxNext := hw_cond headerIdx
      | startAndIdle => (0#7 : Signal dom _)
      | hdrDone      => (0#7 : Signal dom _)
      | isEmitHdr    => headerIdxInc
      | slMbDone     => (0#7 : Signal dom _)
      | (isEmitSlMb &&& notBpGe8) => headerIdxInc

    let dcPredNext := hw_cond dcPred
      | startAndIdle => (128#16 : Signal dom _)
      | isCompDC     => Signal.pure 128#16

    let tcInc := curTC + 1#5
    let quantNonZero := ~~~(quantStoreMem === (0#16 : Signal dom _))
    let curTCNext := hw_cond curTC
      | startAndIdle => (0#5 : Signal dom _)
      | (isReadQuant &&& pixDone16) => (0#5 : Signal dom _)  -- reset before COUNT_TC
      | (isCountTC &&& quantNonZero) => tcInc

    let nCTblSelNext := hw_cond nCTblSel
      | startAndIdle => (0#2 : Signal dom _)
      | isCompNC     => nCComputed

    -- leftTC: store left neighbor's totalCoeff during COMPUTE_NC subPhase 0
    let leftTCVal := tcMapData.map (BitVec.extractLsb' 0 5 ·)
    let leftTCNext := hw_cond leftTC
      | startAndIdle => (0#5 : Signal dom _)
      | isCompNCSub0 => Signal.mux hasLeft leftTCVal (Signal.pure 0#5)

    -- Output bit buffer: drain priority > pack > trailing
    let outBitBufNext := hw_cond outBitBuf
      | startAndIdle => (0#64 : Signal dom _)
      | isDraining   => newBufAfterByte
      | packingActive => packedBuf
      | trailingBit   => trailBuf

    let outBitPosNext := hw_cond outBitPos
      | startAndIdle => (0#7 : Signal dom _)
      | isDraining   => newPosAfterByte
      | packingActive => packedPos
      | trailingBit   => trailAlignPos

    let outByteNext := Signal.mux emitHdrValid hdrByte
      (Signal.mux isDraining topByte (Signal.pure 0#8))
    let outValidNext := emitHdrValid ||| isDraining
    let doneNext := isDone

    -- Bundle state
    bundleAll! [
      Signal.register PH_IDLE phaseNext,
      Signal.register 0#5  blockIdxNext,
      Signal.register 0#5  pixIdxNext,
      Signal.register 0#3  subPhaseNext,
      Signal.register 128#16 dcPredNext,
      Signal.register 0#5  curTCNext,
      Signal.register 0#5  scanIdxNext,
      Signal.register 0#64 outBitBufNext,
      Signal.register 0#7  outBitPosNext,
      Signal.register 0#7  headerIdxNext,
      Signal.register false doneNext,
      Signal.register false outValidNext,
      Signal.register 0#8  outByteNext,
      Signal.register false encStartPulse,
      Signal.register false decStartPulse,
      Signal.register false cavlcStartPulse,
      Signal.register 0#2  nCTblSelNext,
      Signal.register 0#16 (Signal.pure 0#16),
      Signal.register 0#4  (Signal.pure 0#4),
      Signal.register 0#2  (Signal.pure 0#2),
      Signal.register 0#5  leftTCNext
    ]

  -- Extract outputs
  let outByte := FrameEncoderState.outByte loopState
  let outValid := FrameEncoderState.outValid loopState
  let done := FrameEncoderState.done loopState

  bundle2 outByte (bundle2 outValid done)

end Sparkle.IP.Video.H264.FrameEncoder
