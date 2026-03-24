/-
  H.264 NAL Byte Stream Packer — Synthesizable Module

  Wraps encoded data into NAL units with proper Annex-B framing:
  - Emits start code (0x00, 0x00, 0x01)
  - Emits NAL header byte
  - Passes through payload bytes with emulation prevention
    (inserts 0x03 after 0x0000 if next byte <= 0x03)

  Interface:
    Inputs: start, nalType(8), nalRefIdc(8), inputValid, inputByte(8), inputDone
    Outputs: outputValid, outputByte(8), done

  Reference: ITU-T H.264 Section 7.3.1, B.1
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

namespace Sparkle.IP.Video.H264.NALSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- State definition (8 registers)
-- ============================================================================

declare_signal_state NALSynthState
  | fsmState   : BitVec 4  := 0#4     -- FSM phase
  | zeroCount  : BitVec 2  := 0#2     -- consecutive zero bytes seen
  | outputByte : BitVec 8  := 0#8     -- byte to output
  | outputValid : Bool      := false   -- output byte valid
  | done       : Bool       := false   -- NAL packing complete
  | nalHeader  : BitVec 8  := 0#8     -- (ref_idc << 5) | type
  | scIdx      : BitVec 2  := 0#2     -- start code byte index
  | epbPending : Bool       := false   -- emulation prevention byte pending

-- FSM states
private def FSM_IDLE       : BitVec 4 := 0#4
private def FSM_START_CODE : BitVec 4 := 1#4
private def FSM_HEADER     : BitVec 4 := 2#4
private def FSM_PAYLOAD    : BitVec 4 := 3#4
private def FSM_EPB        : BitVec 4 := 4#4  -- emit 0x03 emulation prevention byte
private def FSM_DONE       : BitVec 4 := 5#4

-- ============================================================================
-- Top-level synthesizable module
-- ============================================================================

/-- Synthesizable NAL byte stream packer.

    Input ports:
      0: start
      1: nalType(8) — NAL unit type (5=IDR, 7=SPS, 8=PPS)
      2: nalRefIdc(8) — reference indicator
      3: inputValid — input byte valid
      4: inputByte(8) — input payload byte
      5: inputDone — payload complete
    Output: (outputValid(32), outputByte(32), done(32)) -/
def nalStreamModule {dom : DomainConfig}
    (start : Signal dom Bool)
    (nalType : Signal dom (BitVec 8))
    (nalRefIdc : Signal dom (BitVec 8))
    (inputValid : Signal dom Bool)
    (inputByte : Signal dom (BitVec 8))
    (inputDone : Signal dom Bool)
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsmState   := NALSynthState.fsmState state
    let zeroCount  := NALSynthState.zeroCount state
    let _outputByte := NALSynthState.outputByte state
    let _outputValid := NALSynthState.outputValid state
    let _done      := NALSynthState.done state
    let nalHeader  := NALSynthState.nalHeader state
    let scIdx      := NALSynthState.scIdx state
    let epbPending := NALSynthState.epbPending state

    -- FSM comparisons
    let isIdle := fsmState === (FSM_IDLE : Signal dom _)
    let isSC   := fsmState === (FSM_START_CODE : Signal dom _)
    let isHdr  := fsmState === (FSM_HEADER : Signal dom _)
    let isPay  := fsmState === (FSM_PAYLOAD : Signal dom _)
    let isEPB  := fsmState === (FSM_EPB : Signal dom _)
    let isDone := fsmState === (FSM_DONE : Signal dom _)
    let startAndIdle := start &&& isIdle

    -- Start code emission (0x00, 0x00, 0x01)
    let scByte := hw_cond (0#8 : Signal dom _)
      | (isSC &&& (scIdx === (0#2 : Signal dom _))) => (0x00#8 : Signal dom _)
      | (isSC &&& (scIdx === (1#2 : Signal dom _))) => (0x00#8 : Signal dom _)
      | (isSC &&& (scIdx === (2#2 : Signal dom _))) => (0x01#8 : Signal dom _)
    let scDone := isSC &&& (scIdx === (2#2 : Signal dom _))

    -- NAL header byte: (ref_idc << 5) | type
    let headerByte := (nalRefIdc <<< 5#8) ||| nalType

    -- Emulation prevention detection:
    -- After two consecutive 0x00 bytes, if next byte <= 0x03, insert 0x03
    -- inputByte <= 3 means bits [7:2] are all zero
    let highBits := inputByte.map (BitVec.extractLsb' 2 6 ·)
    let inputIsLowByte := highBits === (0#6 : Signal dom _)
    let needEPB := isPay &&& inputValid &&& (zeroCount === 2#2) &&& inputIsLowByte

    -- Zero count tracking
    let inputIsZero := inputByte === 0x00#8
    let zcInc := Signal.mux (zeroCount === 2#2)
      zeroCount
      (zeroCount + 1#2)

    -- FSM transitions
    let fsmNext := hw_cond fsmState
      | startAndIdle => (FSM_START_CODE : Signal dom _)
      | scDone       => (FSM_HEADER : Signal dom _)
      | isSC         => fsmState
      | isHdr        => (FSM_PAYLOAD : Signal dom _)
      | needEPB      => (FSM_EPB : Signal dom _)
      | (isPay &&& inputDone) => (FSM_DONE : Signal dom _)
      | isEPB        => (FSM_PAYLOAD : Signal dom _)
      | isDone       => (FSM_IDLE : Signal dom _)

    -- scIdx
    let scIdxNext := hw_cond (0#2 : Signal dom _)
      | startAndIdle => (0#2 : Signal dom _)
      | isSC         => scIdx + 1#2

    -- nalHeader (latch on start)
    let nalHeaderNext := hw_cond nalHeader
      | startAndIdle => headerByte

    -- zeroCount
    let zeroCountNext := hw_cond (0#2 : Signal dom _)
      | startAndIdle => (0#2 : Signal dom _)
      | isSC         => (0#2 : Signal dom _)
      | isHdr        => (0#2 : Signal dom _)
      | isEPB        => (0#2 : Signal dom _)
      | (isPay &&& inputValid &&& inputIsZero) => zcInc
      | (isPay &&& inputValid) => (0#2 : Signal dom _)

    -- outputByte
    let outByteNext := hw_cond (0#8 : Signal dom _)
      | isSC    => scByte
      | isHdr   => nalHeader
      | isEPB   => (0x03#8 : Signal dom _)
      | (isPay &&& inputValid) => inputByte

    -- outputValid
    let outValidNext := isSC ||| isHdr ||| isEPB ||| (isPay &&& inputValid)

    -- epbPending (latch the input byte that triggered EPB for re-emit next cycle)
    let epbPendingNext := hw_cond false
      | needEPB => Signal.pure true

    -- done
    let doneNext := isDone

    bundleAll! [
      Signal.register FSM_IDLE fsmNext,
      Signal.register 0#2  zeroCountNext,
      Signal.register 0#8  outByteNext,
      Signal.register false outValidNext,
      Signal.register false doneNext,
      Signal.register 0#8  nalHeaderNext,
      Signal.register 0#2  scIdxNext,
      Signal.register false epbPendingNext
    ]

  -- Extract outputs
  let outputValid := NALSynthState.outputValid state
  let outputByte := NALSynthState.outputByte state
  let done := NALSynthState.done state

  let validU32 := Signal.mux outputValid (Signal.pure 1#32) (Signal.pure 0#32)
  let byteU32 := 0#24 ++ outputByte
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)

  bundleAll! [validU32, byteU32, doneU32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign nalStreamModule ".lake/build/gen/h264/nal_stream.sv" ".lake/build/gen/h264/nal_stream_cppsim.h"

end Sparkle.IP.Video.H264.NALSynth
