/-
  H.264 Hardware MP4 Encoder

  Wraps the frame encoder and emits a complete playable MP4 file.
  Architecture: two-pass buffer + ROM template.

  Pass 1: Run frame encoder, skip first 27 bytes (SPS+PPS+start code),
           buffer IDR NAL bytes, count total.
  Pass 2: Emit ftyp+moov from ROM (patching width/height/stsz),
           then mdat header + buffered IDR bytes.

  Reference: ISO 14496-12 (ISOBMFF), ISO 14496-15 (AVC file format)
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.FrameEncoderSynth

set_option maxRecDepth 8192
set_option maxHeartbeats 12800000

namespace Sparkle.IP.Video.H264.MP4Encoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.IP.Video.H264.FrameEncoder

-- ============================================================================
-- State definition (~11 registers)
-- ============================================================================

declare_signal_state MP4MuxState
  | phase       : BitVec 4  := 0#4    -- FSM phase (0–6)
  | romIdx      : BitVec 10 := 0#10   -- ROM read pointer (0–628)
  | bufWrPtr    : BitVec 10 := 0#10   -- Buffer write pointer (IDR bytes)
  | bufRdPtr    : BitVec 10 := 0#10   -- Buffer read pointer
  | totalH264   : BitVec 10 := 0#10   -- Total H.264 bytes received
  | idrNalSize  : BitVec 10 := 0#10   -- IDR NAL size (= totalH264 - 27)
  | emitCtr     : BitVec 3  := 0#3    -- Sub-byte counter (mdat hdr / IDR len)
  | outValid    : Bool      := false
  | outByte     : BitVec 8  := 0#8
  | done        : Bool      := false
  | feStarted   : Bool      := false  -- Frame encoder start latch
  | pastHeader  : Bool      := false  -- Latches true after first 27 H.264 bytes

-- ============================================================================
-- FSM phase constants
-- ============================================================================

private def PH_IDLE          : BitVec 4 := 0#4
private def PH_RUN_ENCODER   : BitVec 4 := 1#4
private def PH_EMIT_ROM      : BitVec 4 := 2#4
private def PH_EMIT_MDAT_HDR : BitVec 4 := 3#4
private def PH_EMIT_IDR_LEN  : BitVec 4 := 4#4
private def PH_EMIT_IDR_DATA : BitVec 4 := 5#4
private def PH_DONE          : BitVec 4 := 6#4

-- ============================================================================
-- ROM patch offset constants (10-bit)
-- ============================================================================

-- tkhd width: bytes 232–235 (BE32: widthHi, widthLo, 0, 0)
private def PATCH_TKHD_W0 : BitVec 10 := 232#10
private def PATCH_TKHD_W1 : BitVec 10 := 233#10
private def PATCH_TKHD_W2 : BitVec 10 := 234#10
private def PATCH_TKHD_W3 : BitVec 10 := 235#10

-- tkhd height: bytes 236–239
private def PATCH_TKHD_H0 : BitVec 10 := 236#10
private def PATCH_TKHD_H1 : BitVec 10 := 237#10
private def PATCH_TKHD_H2 : BitVec 10 := 238#10
private def PATCH_TKHD_H3 : BitVec 10 := 239#10

-- avc1 width: bytes 445–446 (BE16)
private def PATCH_AVC1_W0 : BitVec 10 := 445#10
private def PATCH_AVC1_W1 : BitVec 10 := 446#10

-- avc1 height: bytes 447–448
private def PATCH_AVC1_H0 : BitVec 10 := 447#10
private def PATCH_AVC1_H1 : BitVec 10 := 448#10

-- stsz entry: bytes 605–608 (BE32: 4 + idrNalSize)
private def PATCH_STSZ_0 : BitVec 10 := 605#10
private def PATCH_STSZ_1 : BitVec 10 := 606#10
private def PATCH_STSZ_2 : BitVec 10 := 607#10
private def PATCH_STSZ_3 : BitVec 10 := 608#10

-- ============================================================================
-- Hardware MP4 Encoder
-- ============================================================================

def h264MP4Encoder {dom : DomainConfig}
    (start : Signal dom Bool)
    -- Frame buffer write (host loads image)
    (frameWriteEn : Signal dom Bool)
    (frameWriteAddr : Signal dom (BitVec 8))
    (frameWriteData : Signal dom (BitVec 16))
    -- QP parameters
    (quantMF0 quantMF1 quantMF2 quantF : Signal dom (BitVec 32))
    (quantShift : Signal dom (BitVec 5))
    (vscale0 vscale1 vscale2 : Signal dom (BitVec 32))
    -- VLC table loading (passed through to CAVLC)
    (ctWrEn : Signal dom Bool) (ctWrAddr : Signal dom (BitVec 9)) (ctWrData : Signal dom (BitVec 32))
    (tzWrEn : Signal dom Bool) (tzWrAddr : Signal dom (BitVec 7)) (tzWrData : Signal dom (BitVec 32))
    (rbWrEn : Signal dom Bool) (rbWrAddr : Signal dom (BitVec 6)) (rbWrData : Signal dom (BitVec 32))
    (zzWrEn : Signal dom Bool) (zzWrAddr : Signal dom (BitVec 4)) (zzWrData : Signal dom (BitVec 16))
    -- MP4 ROM loading (629 bytes, host loads once)
    (romWrEn : Signal dom Bool)
    (romWrAddr : Signal dom (BitVec 10))
    (romWrData : Signal dom (BitVec 8))
    -- Frame dimensions (for runtime patching)
    (widthIn : Signal dom (BitVec 16))
    (heightIn : Signal dom (BitVec 16))
    : Signal dom (BitVec 8 × Bool × Bool) :=   -- (outByte, outValid, done)
  let loopState := Signal.loop fun state =>
    -- Extract state registers
    let phase     := MP4MuxState.phase state
    let romIdx    := MP4MuxState.romIdx state
    let bufWrPtr  := MP4MuxState.bufWrPtr state
    let bufRdPtr  := MP4MuxState.bufRdPtr state
    let totalH264 := MP4MuxState.totalH264 state
    let idrNalSize := MP4MuxState.idrNalSize state
    let emitCtr   := MP4MuxState.emitCtr state
    let feStarted := MP4MuxState.feStarted state
    let pastHeader := MP4MuxState.pastHeader state

    -- Phase comparisons
    let isIdle       := phase === (PH_IDLE : Signal dom _)
    let isRunEnc     := phase === (PH_RUN_ENCODER : Signal dom _)
    let isEmitROM    := phase === (PH_EMIT_ROM : Signal dom _)
    let isEmitMdatH  := phase === (PH_EMIT_MDAT_HDR : Signal dom _)
    let isEmitIDRLen := phase === (PH_EMIT_IDR_LEN : Signal dom _)
    let isEmitIDRDat := phase === (PH_EMIT_IDR_DATA : Signal dom _)
    let isDone       := phase === (PH_DONE : Signal dom _)

    let startAndIdle := start &&& isIdle

    -- ================================================================
    -- Frame encoder sub-module
    -- ================================================================
    let feStart := isRunEnc &&& ((fun x => !x) <$> feStarted)
    let feOutput := h264FrameEncoder feStart
      frameWriteEn frameWriteAddr frameWriteData
      quantMF0 quantMF1 quantMF2 quantF quantShift
      vscale0 vscale1 vscale2
      ctWrEn ctWrAddr ctWrData
      tzWrEn tzWrAddr tzWrData
      rbWrEn rbWrAddr rbWrData
      zzWrEn zzWrAddr zzWrData
    let feByte  := projN! feOutput 3 0    -- BitVec 8
    let feValid := projN! feOutput 3 1    -- Bool
    let feDone  := projN! feOutput 3 2    -- Bool

    -- ================================================================
    -- IDR buffer memory (1024 × 8-bit, memoryComboRead)
    -- ================================================================
    -- Write: during RUN_ENCODER, when feValid and past first 27 bytes (SPS+PPS+start code)
    let bufWriteEn := isRunEnc &&& feValid &&& pastHeader
    let bufWrData8 := feByte
    let bufReadAddr := Signal.mux isEmitIDRDat bufRdPtr (Signal.pure 0#10)
    let bufData := Signal.memoryComboRead bufWrPtr bufWrData8 bufWriteEn bufReadAddr

    -- ================================================================
    -- ROM memory (1024 × 8-bit, memoryComboRead)
    -- ================================================================
    let romReadAddr := Signal.mux isEmitROM romIdx (Signal.pure 0#10)
    let romData := Signal.memoryComboRead romWrAddr romWrData romWrEn romReadAddr

    -- ================================================================
    -- Width/height byte extraction (for ROM patching)
    -- ================================================================
    let widthHi  := widthIn.map (BitVec.extractLsb' 8 8 ·)
    let widthLo  := widthIn.map (BitVec.extractLsb' 0 8 ·)
    let heightHi := heightIn.map (BitVec.extractLsb' 8 8 ·)
    let heightLo := heightIn.map (BitVec.extractLsb' 0 8 ·)

    -- stsz value: 4 + idrNalSize (as 16-bit, fits in 10 bits + 4)
    let stszVal16 := (· + ·) <$> (0#6 ++ idrNalSize) <*> Signal.pure 4#16
    let stszHi := stszVal16.map (BitVec.extractLsb' 8 8 ·)
    let stszLo := stszVal16.map (BitVec.extractLsb' 0 8 ·)

    -- ================================================================
    -- ROM patching: substitute bytes at specific offsets
    -- ================================================================
    let patchedByte :=
      -- tkhd width (BE32: widthHi, widthLo, 0, 0)
      Signal.mux (romIdx === (PATCH_TKHD_W0 : Signal dom _)) widthHi
      (Signal.mux (romIdx === (PATCH_TKHD_W1 : Signal dom _)) widthLo
      (Signal.mux (romIdx === (PATCH_TKHD_W2 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (romIdx === (PATCH_TKHD_W3 : Signal dom _)) (Signal.pure 0#8)
      -- tkhd height (BE32: heightHi, heightLo, 0, 0)
      (Signal.mux (romIdx === (PATCH_TKHD_H0 : Signal dom _)) heightHi
      (Signal.mux (romIdx === (PATCH_TKHD_H1 : Signal dom _)) heightLo
      (Signal.mux (romIdx === (PATCH_TKHD_H2 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (romIdx === (PATCH_TKHD_H3 : Signal dom _)) (Signal.pure 0#8)
      -- avc1 width/height (BE16)
      (Signal.mux (romIdx === (PATCH_AVC1_W0 : Signal dom _)) widthHi
      (Signal.mux (romIdx === (PATCH_AVC1_W1 : Signal dom _)) widthLo
      (Signal.mux (romIdx === (PATCH_AVC1_H0 : Signal dom _)) heightHi
      (Signal.mux (romIdx === (PATCH_AVC1_H1 : Signal dom _)) heightLo
      -- stsz entry (BE32: 0, 0, hi, lo)
      (Signal.mux (romIdx === (PATCH_STSZ_0 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (romIdx === (PATCH_STSZ_1 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (romIdx === (PATCH_STSZ_2 : Signal dom _)) stszHi
      (Signal.mux (romIdx === (PATCH_STSZ_3 : Signal dom _)) stszLo
      -- default: ROM data
      romData)))))))))))))))

    -- ================================================================
    -- mdat header: BE32(8 + 4 + idrNalSize) ++ "mdat"
    -- mdat box size = 8 (box header) + 4 (IDR length prefix) + idrNalSize
    -- ================================================================
    let mdatSize16 := (· + ·) <$> (0#6 ++ idrNalSize) <*> Signal.pure 12#16
    let mdatSizeHi := mdatSize16.map (BitVec.extractLsb' 8 8 ·)
    let mdatSizeLo := mdatSize16.map (BitVec.extractLsb' 0 8 ·)

    -- mdat header bytes (8 bytes): [0, 0, sizeHi, sizeLo, 'm', 'd', 'a', 't']
    let mdatHdrByte := Signal.mux (emitCtr === (0#3 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (emitCtr === (1#3 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (emitCtr === (2#3 : Signal dom _)) mdatSizeHi
      (Signal.mux (emitCtr === (3#3 : Signal dom _)) mdatSizeLo
      (Signal.mux (emitCtr === (4#3 : Signal dom _)) (Signal.pure 0x6D#8)  -- 'm'
      (Signal.mux (emitCtr === (5#3 : Signal dom _)) (Signal.pure 0x64#8)  -- 'd'
      (Signal.mux (emitCtr === (6#3 : Signal dom _)) (Signal.pure 0x61#8)  -- 'a'
      (Signal.pure 0x74#8)))))))                                             -- 't'

    -- IDR length prefix: BE32(idrNalSize)
    let idrSize16 := 0#6 ++ idrNalSize
    let idrSizeHi := idrSize16.map (BitVec.extractLsb' 8 8 ·)
    let idrSizeLo := idrSize16.map (BitVec.extractLsb' 0 8 ·)
    let idrLenByte := Signal.mux (emitCtr === (0#3 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (emitCtr === (1#3 : Signal dom _)) (Signal.pure 0#8)
      (Signal.mux (emitCtr === (2#3 : Signal dom _)) idrSizeHi
      idrSizeLo))

    -- ================================================================
    -- Completion conditions
    -- ================================================================
    let feDoneAndRunning := isRunEnc &&& feDone
    let romDone := isEmitROM &&& (romIdx === (628#10 : Signal dom _))
    let mdatHdrDone := isEmitMdatH &&& (emitCtr === (7#3 : Signal dom _))
    let idrLenDone := isEmitIDRLen &&& (emitCtr === (3#3 : Signal dom _))
    let idrDataDone := isEmitIDRDat &&& (bufRdPtr === idrNalSize)

    -- ================================================================
    -- FSM transitions
    -- ================================================================
    let phaseNext := hw_cond phase
      | startAndIdle   => (PH_RUN_ENCODER : Signal dom _)
      | feDoneAndRunning => (PH_EMIT_ROM : Signal dom _)
      | romDone        => (PH_EMIT_MDAT_HDR : Signal dom _)
      | mdatHdrDone    => (PH_EMIT_IDR_LEN : Signal dom _)
      | idrLenDone     => (PH_EMIT_IDR_DATA : Signal dom _)
      | idrDataDone    => (PH_DONE : Signal dom _)
      | isDone         => (PH_IDLE : Signal dom _)

    -- romIdx: increment during EMIT_ROM
    let romIdxNext := hw_cond romIdx
      | startAndIdle => (0#10 : Signal dom _)
      | (isEmitROM &&& ((fun x => !x) <$> romDone)) => romIdx + 1#10

    -- bufWrPtr: increment when buffering IDR bytes
    let bufWrPtrNext := hw_cond bufWrPtr
      | startAndIdle => (0#10 : Signal dom _)
      | bufWriteEn   => bufWrPtr + 1#10

    -- bufRdPtr: increment during EMIT_IDR_DATA
    let bufRdPtrNext := hw_cond bufRdPtr
      | startAndIdle => (0#10 : Signal dom _)
      | (isEmitIDRDat &&& ((fun x => !x) <$> idrDataDone)) =>
          bufRdPtr + 1#10

    -- totalH264: count all bytes from frame encoder
    let totalH264Next := hw_cond totalH264
      | startAndIdle        => (0#10 : Signal dom _)
      | (isRunEnc &&& feValid) => totalH264 + 1#10

    -- idrNalSize: capture at end of encoder run
    let idrNalSizeNext := hw_cond idrNalSize
      | startAndIdle     => (0#10 : Signal dom _)
      | feDoneAndRunning => bufWrPtr

    -- emitCtr: sub-byte counter
    let emitCtrNext := hw_cond emitCtr
      | startAndIdle => (0#3 : Signal dom _)
      | romDone      => (0#3 : Signal dom _)   -- reset for mdat header
      | mdatHdrDone  => (0#3 : Signal dom _)   -- reset for IDR length
      | isEmitMdatH  => emitCtr + 1#3
      | isEmitIDRLen => emitCtr + 1#3

    -- feStarted: latch so we only send one start pulse
    let feStartedNext := hw_cond feStarted
      | startAndIdle => (false : Signal dom _)
      | isRunEnc     => (true : Signal dom _)

    -- pastHeader: latch true after receiving 27th H.264 byte
    -- totalH264 == 26 means we've received bytes 0–25, currently receiving byte 26 (last skip byte)
    -- After this cycle, pastHeader=true, so byte 27 (first IDR NAL byte) gets buffered
    let reachedByte27 := isRunEnc &&& feValid &&& (totalH264 === (26#10 : Signal dom _))
    let pastHeaderNext := hw_cond pastHeader
      | startAndIdle  => (false : Signal dom _)
      | reachedByte27 => (true : Signal dom _)

    -- Output selection
    let outByteNext := Signal.mux isEmitROM patchedByte
      (Signal.mux isEmitMdatH mdatHdrByte
      (Signal.mux isEmitIDRLen idrLenByte
      (Signal.mux isEmitIDRDat bufData
      (Signal.pure 0#8))))

    let outValidNext := isEmitROM ||| isEmitMdatH ||| isEmitIDRLen |||
      (isEmitIDRDat &&& ((fun x => !x) <$> idrDataDone))

    let doneNext := isDone

    -- Bundle state
    bundleAll! [
      Signal.register PH_IDLE phaseNext,
      Signal.register 0#10 romIdxNext,
      Signal.register 0#10 bufWrPtrNext,
      Signal.register 0#10 bufRdPtrNext,
      Signal.register 0#10 totalH264Next,
      Signal.register 0#10 idrNalSizeNext,
      Signal.register 0#3  emitCtrNext,
      Signal.register false outValidNext,
      Signal.register 0#8  outByteNext,
      Signal.register false doneNext,
      Signal.register false feStartedNext,
      Signal.register false pastHeaderNext
    ]

  -- Extract outputs
  let outByte  := MP4MuxState.outByte loopState
  let outValid := MP4MuxState.outValid loopState
  let done     := MP4MuxState.done loopState

  bundle2 outByte (bundle2 outValid done)

end Sparkle.IP.Video.H264.MP4Encoder
