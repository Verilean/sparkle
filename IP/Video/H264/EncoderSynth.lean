/-
  H.264 Encoder Pipeline — Synthesizable Top-Level

  Monolithic encoder pipeline FSM performing 3 stages sequentially:
    Phase 1 (RESIDUAL, 16 cycles): original - predicted → residual
    Phase 2 (DCT, 64 cycles): residual → DCT coefficients via butterfly
    Phase 3 (QUANT, 16 cycles): DCT coefficients → quantized levels (QP=20)

  Total: ~96 cycles per 4×4 block (fixed QP=20).

  Uses internal memories for data passing between stages:
    mem0: original pixels (16×16-bit, combo-read, loaded externally)
    mem1: predicted pixels (16×16-bit, combo-read, loaded externally)
    mem2: residual (16×16-bit, written in phase 1, combo-read in phase 2)
    mem3: DCT intermediate (16×16-bit, written/read during phase 2 butterfly)
    mem4: DCT coefficients (16×16-bit, written in phase 2, combo-read in phase 3)
    mem5: quantized levels (16×16-bit, written in phase 3)

  External interface:
    - start: assert to begin encoding
    - origWriteEn/origWriteAddr/origWriteData: load original pixels
    - predWriteEn/predWriteAddr/predWriteData: load prediction pixels
    - Outputs: done (32-bit), phase (32-bit)

  Reference: ITU-T H.264 Section 7, 8
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.Quant
import IP.Video.H264.ForwardDCTSynth
import IP.Video.H264.QuantSynth

set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

namespace Sparkle.IP.Video.H264.EncoderSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.IP.Video.H264.ForwardDCTSynth
open Sparkle.IP.Video.H264.QuantSynth
open Sparkle.IP.Video.H264.Quant

-- ============================================================================
-- State definition (12 registers)
-- ============================================================================

-- Pipeline phase: 0=IDLE, 1=RESIDUAL, 2=DCT_ROW, 3=DCT_COL, 4=QUANT, 5=DONE
declare_signal_state EncoderPipeState
  | phase   : BitVec 3  := 0#3
  | idx     : BitVec 5  := 0#5
  | substep : BitVec 3  := 0#3
  | grpIdx  : BitVec 3  := 0#3
  | done    : Bool       := false
  | last    : BitVec 16 := 0#16
  | val0    : BitVec 16 := 0#16
  | val1    : BitVec 16 := 0#16
  | val2    : BitVec 16 := 0#16
  | val3    : BitVec 16 := 0#16
  | dctPhase : BitVec 2 := 0#2
  | dummy   : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (full encode pipeline at QP=20)
-- ============================================================================

/-- Pure residual computation: original - predicted (signed). -/
def residualRef (original : Array Nat) (predicted : Array Nat) : Array Int :=
  (List.range 16).toArray.map fun i =>
    let o := if h : i < original.size then original[i] else 0
    let p := if h : i < predicted.size then predicted[i] else 0
    Int.ofNat o - Int.ofNat p

/-- Pure encode pipeline: residual → forward DCT → quantize (parameterized QP).
    Takes original and predicted pixels, returns quantized levels. -/
def encoderPipelineRef (original : Array Nat) (predicted : Array Nat) (qp : Nat := 20) : Array Int :=
  let residual := residualRef original predicted
  let dctCoeffs := fwdDCTRef residual
  quantBlockRef dctCoeffs (qp := qp)

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Encoder pipeline synthesis module (monolithic FSM).
    Performs residual → forward DCT → quantize in a single Signal.loop.

    Inputs:
      start — assert to begin encoding
      origWriteEn/origWriteAddr/origWriteData — load original pixels
      predWriteEn/predWriteAddr/predWriteData — load predicted pixels
      quantMF0/1/2 — QP-dependent MF values per position class
      quantF — QP-dependent rounding offset
      quantShift — QP-dependent qbits shift amount
    Outputs: done (32-bit), phase (32-bit). -/
def encoderPipeline {dom : DomainConfig}
    (start : Signal dom Bool)
    (origWriteEn : Signal dom Bool)
    (origWriteAddr : Signal dom (BitVec 4))
    (origWriteData : Signal dom (BitVec 16))
    (predWriteEn : Signal dom Bool)
    (predWriteAddr : Signal dom (BitVec 4))
    (predWriteData : Signal dom (BitVec 16))
    (quantMF0 : Signal dom (BitVec 32))
    (quantMF1 : Signal dom (BitVec 32))
    (quantMF2 : Signal dom (BitVec 32))
    (quantF : Signal dom (BitVec 32))
    (quantShift : Signal dom (BitVec 5))
    : Signal dom (BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let phase   := EncoderPipeState.phase   state
    let idx     := EncoderPipeState.idx     state
    let substep := EncoderPipeState.substep state
    let grpIdx  := EncoderPipeState.grpIdx  state
    let v0      := EncoderPipeState.val0    state
    let v1      := EncoderPipeState.val1    state
    let v2      := EncoderPipeState.val2    state
    let v3      := EncoderPipeState.val3    state

    -- Phase decode
    let isIdle    := phase === (0#3 : Signal dom _)
    let isResid   := phase === (1#3 : Signal dom _)
    let isDctRow  := phase === (2#3 : Signal dom _)
    let isDctCol  := phase === (3#3 : Signal dom _)
    let isQuant   := phase === (4#3 : Signal dom _)
    let isDone    := phase === (5#3 : Signal dom _)
    let startAndIdle := start &&& isIdle
    let isDct := isDctRow ||| isDctCol

    -- Common index (truncated to 4 bits for memory addressing)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)

    -- ================================================================
    -- RESIDUAL PHASE (16 cycles): original - predicted
    -- ================================================================

    -- Original pixels memory (combo-read, loaded externally)
    let origVal := Signal.memoryComboRead origWriteAddr origWriteData origWriteEn readAddr4

    -- Predicted pixels memory (combo-read, loaded externally)
    let predVal := Signal.memoryComboRead predWriteAddr predWriteData predWriteEn readAddr4

    -- Residual = original - predicted (signed 16-bit)
    let residVal := (· - ·) <$> origVal <*> predVal

    -- Residual memory (written in residual phase, combo-read in DCT row phase)
    let residWrEn := isResid
    let _residMem := Signal.memoryComboRead readAddr4 residVal residWrEn (Signal.pure 0#4)

    -- ================================================================
    -- DCT PHASE (64 cycles): forward butterfly transforms
    -- ================================================================

    -- DCT substep and group decode
    let isSub0 := substep === (0#3 : Signal dom _)
    let isSub1 := substep === (1#3 : Signal dom _)
    let isSub2 := substep === (2#3 : Signal dom _)
    let isSub3 := substep === (3#3 : Signal dom _)
    let isSub4 := substep === (4#3 : Signal dom _)
    let isSub5 := substep === (5#3 : Signal dom _)
    let isSub6 := substep === (6#3 : Signal dom _)
    let isSub7 := substep === (7#3 : Signal dom _)
    let isDctReading := isSub0 ||| isSub1 ||| isSub2 ||| isSub3
    let isDctWriting := isSub4 ||| isSub5 ||| isSub6 ||| isSub7

    -- Zero-extend grpIdx[1:0] and substep[1:0] to 4 bits
    let grp4 := 0#2 ++ (grpIdx.map (BitVec.extractLsb' 0 2 ·))
    let subLo4 := 0#2 ++ (substep.map (BitVec.extractLsb' 0 2 ·))

    -- Row read: addr = grp*4 + subLo
    let dctRowAddr := (· + ·) <$> ((· * ·) <$> grp4 <*> Signal.pure 4#4) <*> subLo4
    -- Col read: addr = subLo*4 + grp
    let dctColAddr := (· + ·) <$> ((· * ·) <$> subLo4 <*> Signal.pure 4#4) <*> grp4
    let dctAddr := Signal.mux isDctRow dctRowAddr dctColAddr

    -- Residual memory read for DCT row phase (combo-read at dctAddr)
    let residReadAddr := Signal.mux (isDctRow &&& isDctReading) dctAddr (Signal.pure 0#4)
    let residRdData := Signal.memoryComboRead readAddr4 residVal residWrEn residReadAddr

    -- DCT intermediate memory (written during row phase, combo-read during col phase)
    let dctInterWrEn := isDctRow &&& isDctWriting
    -- DCT output / coefficients memory (written during col phase)
    let dctOutWrEn := isDctCol &&& isDctWriting

    -- Forward DCT butterfly computation
    -- s0 = v0+v3, s1 = v1+v2, d0 = v0-v3, d1 = v1-v2
    let s0 := (· + ·) <$> v0 <*> v3
    let s1 := (· + ·) <$> v1 <*> v2
    let d0 := (· - ·) <$> v0 <*> v3
    let d1 := (· - ·) <$> v1 <*> v2

    -- Y0 = s0+s1, Y1 = 2*d0+d1, Y2 = s0-s1, Y3 = d0-2*d1
    let d0x2 := (· + ·) <$> d0 <*> d0
    let d1x2 := (· + ·) <$> d1 <*> d1

    let y0 := (· + ·) <$> s0 <*> s1
    let y1 := (· + ·) <$> d0x2 <*> d1
    let y2 := (· - ·) <$> s0 <*> s1
    let y3 := (· - ·) <$> d0 <*> d1x2

    -- Select output based on substep (same butterfly for both row and col)
    let butterflyOut := hw_cond y0
      | isSub4 => y0
      | isSub5 => y1
      | isSub6 => y2
      | isSub7 => y3

    -- Intermediate memory for DCT
    let interReadAddr := Signal.mux (isDctCol &&& isDctReading) dctAddr (Signal.pure 0#4)
    let interData := Signal.memoryComboRead dctAddr butterflyOut dctInterWrEn interReadAddr

    -- DCT coefficients memory (written in col phase, combo-read in quant phase)
    let dctCoeffMem := Signal.memoryComboRead dctAddr butterflyOut dctOutWrEn readAddr4

    -- DCT data source for reading into val registers
    let dctSrcData := Signal.mux isDctRow residRdData interData

    -- Update val registers during DCT read phase
    let v0Next := Signal.mux (isDct &&& isSub0) dctSrcData v0
    let v1Next := Signal.mux (isDct &&& isSub1) dctSrcData v1
    let v2Next := Signal.mux (isDct &&& isSub2) dctSrcData v2
    let v3Next := Signal.mux (isDct &&& isSub3) dctSrcData v3

    -- ================================================================
    -- QUANT PHASE (16 cycles): forward quantization at QP=20
    -- ================================================================

    -- DCT coefficient from memory (combo-read)
    let quantInput := dctCoeffMem

    -- Sign handling
    let qSignBit := quantInput.map (BitVec.extractLsb' 15 1 ·)
    let qIsNeg := qSignBit === 1#1
    let qNegCoeff := (· - ·) <$> Signal.pure 0#16 <*> quantInput
    let qAbsCoeff := Signal.mux qIsNeg qNegCoeff quantInput
    let qAbsCoeff32 := 0#16 ++ qAbsCoeff

    -- Position class for QP=20: MF values
    let qIdxBit0 := idx.map (BitVec.extractLsb' 0 1 ·)
    let qIdxBit2 := idx.map (BitVec.extractLsb' 2 1 ·)
    let qRowOdd := qIdxBit2 === 1#1
    let qColOdd := qIdxBit0 === 1#1
    let qBothEven := ((fun x => !x) <$> qRowOdd) &&& ((fun x => !x) <$> qColOdd)
    let qBothOdd := qRowOdd &&& qColOdd

    -- MF values: selected from input ports by position class
    let mfVal := Signal.mux qBothEven quantMF0
                   (Signal.mux qBothOdd quantMF1
                     quantMF2)

    -- product = absCoeff * MF + f (from input port)
    let qProduct := (· * ·) <$> qAbsCoeff32 <*> mfVal
    let qWithF := (· + ·) <$> qProduct <*> quantF

    -- Variable shift right by qbits from input port
    let quantShift32 := 0#27 ++ quantShift
    let qShifted := (· >>> ·) <$> qWithF <*> quantShift32
    let qLevel16 := qShifted.map (BitVec.extractLsb' 0 16 ·)

    -- Restore sign
    let qNegLevel := (· - ·) <$> Signal.pure 0#16 <*> qLevel16
    let qResult := Signal.mux qIsNeg qNegLevel qLevel16

    -- Output quantized levels memory (written in quant phase)
    let quantWrEn := isQuant
    let _outMem := Signal.memory readAddr4 qResult quantWrEn (Signal.pure 0#4)

    -- ================================================================
    -- FSM Control
    -- ================================================================

    -- Residual done: idx reaches 15
    let residDone := isResid &&& (idx === (15#5 : Signal dom _))

    -- DCT group/substep control
    let substepInc := substep + 1#3
    let groupDone := isDct &&& isSub7
    let lastGroup := grpIdx === (3#3 : Signal dom _)
    let dctRowDone := isDctRow &&& groupDone &&& lastGroup
    let dctColDone := isDctCol &&& groupDone &&& lastGroup

    let grpInc := grpIdx + 1#3
    let grpIdxNext := hw_cond grpIdx
      | startAndIdle => (0#3 : Signal dom _)
      | dctRowDone   => (0#3 : Signal dom _)
      | groupDone    => grpInc

    let substepNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | residDone    => (0#3 : Signal dom _)
      | isDct        => substepInc

    -- Quant done: idx reaches 15
    let quantDone := isQuant &&& (idx === (15#5 : Signal dom _))

    -- Index control
    let idxInc := idx + 1#5
    let idxNext := hw_cond (0#5 : Signal dom _)
      | startAndIdle => (0#5 : Signal dom _)
      | residDone    => (0#5 : Signal dom _)
      | dctColDone   => (0#5 : Signal dom _)
      | isResid      => idxInc
      | isQuant      => idxInc

    -- Phase transitions
    let startAndDone := start &&& isDone
    let phaseNext := hw_cond phase
      | startAndIdle => (1#3 : Signal dom _)
      | residDone    => (2#3 : Signal dom _)
      | dctRowDone   => (3#3 : Signal dom _)
      | dctColDone   => (4#3 : Signal dom _)
      | quantDone    => (5#3 : Signal dom _)
      | startAndDone => (1#3 : Signal dom _)

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3  phaseNext,
      Signal.register 0#5  idxNext,
      Signal.register 0#3  substepNext,
      Signal.register 0#3  grpIdxNext,
      Signal.register false doneNext,
      Signal.register 0#16 qResult,
      Signal.register 0#16 v0Next,
      Signal.register 0#16 v1Next,
      Signal.register 0#16 v2Next,
      Signal.register 0#16 v3Next,
      Signal.register 0#2  (Signal.pure 0#2),
      Signal.register 0#16 (Signal.pure 0#16)
    ]

  -- Extract outputs
  let done := EncoderPipeState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let phaseVal := EncoderPipeState.phase state
  let phaseU32 := 0#29 ++ phaseVal

  bundleAll! [doneU32, phaseU32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign encoderPipeline ".lake/build/gen/h264/encoder_pipeline.sv" ".lake/build/gen/h264/encoder_pipeline_cppsim.h"

-- ============================================================================
-- V2: Encoder pipeline with external read port for quantized levels
-- ============================================================================

/-- Encoder pipeline V2 — identical to encoderPipeline but adds a quantReadAddr
    input and returns quantReadData as a third output.
    Used as a sub-module inside h264FrameEncoder where the parent needs to
    read quantized levels from the internal memory.

    Returns: (done : BitVec 32, phase : BitVec 32, quantReadData : BitVec 16) -/
def encoderPipelineV2 {dom : DomainConfig}
    (start : Signal dom Bool)
    (origWriteEn : Signal dom Bool)
    (origWriteAddr : Signal dom (BitVec 4))
    (origWriteData : Signal dom (BitVec 16))
    (predWriteEn : Signal dom Bool)
    (predWriteAddr : Signal dom (BitVec 4))
    (predWriteData : Signal dom (BitVec 16))
    (quantMF0 : Signal dom (BitVec 32))
    (quantMF1 : Signal dom (BitVec 32))
    (quantMF2 : Signal dom (BitVec 32))
    (quantF : Signal dom (BitVec 32))
    (quantShift : Signal dom (BitVec 5))
    (quantReadAddr : Signal dom (BitVec 4))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 16) :=
  let state := Signal.loop fun state =>
    let phase   := EncoderPipeState.phase   state
    let idx     := EncoderPipeState.idx     state
    let substep := EncoderPipeState.substep state
    let grpIdx  := EncoderPipeState.grpIdx  state
    let v0      := EncoderPipeState.val0    state
    let v1      := EncoderPipeState.val1    state
    let v2      := EncoderPipeState.val2    state
    let v3      := EncoderPipeState.val3    state

    -- Phase decode
    let isIdle    := phase === (0#3 : Signal dom _)
    let isResid   := phase === (1#3 : Signal dom _)
    let isDctRow  := phase === (2#3 : Signal dom _)
    let isDctCol  := phase === (3#3 : Signal dom _)
    let isQuant   := phase === (4#3 : Signal dom _)
    let isDone    := phase === (5#3 : Signal dom _)
    let startAndIdle := start &&& isIdle
    let isDct := isDctRow ||| isDctCol

    -- Common index (truncated to 4 bits for memory addressing)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)

    -- Original pixels memory (combo-read, loaded externally)
    let origVal := Signal.memoryComboRead origWriteAddr origWriteData origWriteEn readAddr4

    -- Predicted pixels memory (combo-read, loaded externally)
    let predVal := Signal.memoryComboRead predWriteAddr predWriteData predWriteEn readAddr4

    -- Residual = original - predicted (signed 16-bit)
    let residVal := (· - ·) <$> origVal <*> predVal

    -- Residual memory (written in residual phase, combo-read in DCT row phase)
    let residWrEn := isResid
    let _residMem := Signal.memoryComboRead readAddr4 residVal residWrEn (Signal.pure 0#4)

    -- DCT substep and group decode
    let isSub0 := substep === (0#3 : Signal dom _)
    let isSub1 := substep === (1#3 : Signal dom _)
    let isSub2 := substep === (2#3 : Signal dom _)
    let isSub3 := substep === (3#3 : Signal dom _)
    let isSub4 := substep === (4#3 : Signal dom _)
    let isSub5 := substep === (5#3 : Signal dom _)
    let isSub6 := substep === (6#3 : Signal dom _)
    let isSub7 := substep === (7#3 : Signal dom _)
    let isDctReading := isSub0 ||| isSub1 ||| isSub2 ||| isSub3
    let isDctWriting := isSub4 ||| isSub5 ||| isSub6 ||| isSub7

    let grp4 := 0#2 ++ (grpIdx.map (BitVec.extractLsb' 0 2 ·))
    let subLo4 := 0#2 ++ (substep.map (BitVec.extractLsb' 0 2 ·))

    let dctRowAddr := (· + ·) <$> ((· * ·) <$> grp4 <*> Signal.pure 4#4) <*> subLo4
    let dctColAddr := (· + ·) <$> ((· * ·) <$> subLo4 <*> Signal.pure 4#4) <*> grp4
    let dctAddr := Signal.mux isDctRow dctRowAddr dctColAddr

    let residReadAddr := Signal.mux (isDctRow &&& isDctReading) dctAddr (Signal.pure 0#4)
    let residRdData := Signal.memoryComboRead readAddr4 residVal residWrEn residReadAddr

    let dctInterWrEn := isDctRow &&& isDctWriting
    let dctOutWrEn := isDctCol &&& isDctWriting

    let s0 := (· + ·) <$> v0 <*> v3
    let s1 := (· + ·) <$> v1 <*> v2
    let d0 := (· - ·) <$> v0 <*> v3
    let d1 := (· - ·) <$> v1 <*> v2

    let d0x2 := (· + ·) <$> d0 <*> d0
    let d1x2 := (· + ·) <$> d1 <*> d1

    let y0 := (· + ·) <$> s0 <*> s1
    let y1 := (· + ·) <$> d0x2 <*> d1
    let y2 := (· - ·) <$> s0 <*> s1
    let y3 := (· - ·) <$> d0 <*> d1x2

    let butterflyOut := hw_cond y0
      | isSub4 => y0
      | isSub5 => y1
      | isSub6 => y2
      | isSub7 => y3

    let interReadAddr := Signal.mux (isDctCol &&& isDctReading) dctAddr (Signal.pure 0#4)
    let interData := Signal.memoryComboRead dctAddr butterflyOut dctInterWrEn interReadAddr

    let dctCoeffMem := Signal.memoryComboRead dctAddr butterflyOut dctOutWrEn readAddr4

    let dctSrcData := Signal.mux isDctRow residRdData interData

    let v0Next := Signal.mux (isDct &&& isSub0) dctSrcData v0
    let v1Next := Signal.mux (isDct &&& isSub1) dctSrcData v1
    let v2Next := Signal.mux (isDct &&& isSub2) dctSrcData v2
    let v3Next := Signal.mux (isDct &&& isSub3) dctSrcData v3

    -- QUANT PHASE
    let quantInput := dctCoeffMem

    let qSignBit := quantInput.map (BitVec.extractLsb' 15 1 ·)
    let qIsNeg := qSignBit === 1#1
    let qNegCoeff := (· - ·) <$> Signal.pure 0#16 <*> quantInput
    let qAbsCoeff := Signal.mux qIsNeg qNegCoeff quantInput
    let qAbsCoeff32 := 0#16 ++ qAbsCoeff

    let qIdxBit0 := idx.map (BitVec.extractLsb' 0 1 ·)
    let qIdxBit2 := idx.map (BitVec.extractLsb' 2 1 ·)
    let qRowOdd := qIdxBit2 === 1#1
    let qColOdd := qIdxBit0 === 1#1
    let qBothEven := ((fun x => !x) <$> qRowOdd) &&& ((fun x => !x) <$> qColOdd)
    let qBothOdd := qRowOdd &&& qColOdd

    let mfVal := Signal.mux qBothEven quantMF0
                   (Signal.mux qBothOdd quantMF1
                     quantMF2)

    let qProduct := (· * ·) <$> qAbsCoeff32 <*> mfVal
    let qWithF := (· + ·) <$> qProduct <*> quantF

    let quantShift32 := 0#27 ++ quantShift
    let qShifted := (· >>> ·) <$> qWithF <*> quantShift32
    let qLevel16 := qShifted.map (BitVec.extractLsb' 0 16 ·)

    let qNegLevel := (· - ·) <$> Signal.pure 0#16 <*> qLevel16
    let qResult := Signal.mux qIsNeg qNegLevel qLevel16

    -- V2 change: use memoryComboRead with quantReadAddr, pipe through state register
    let quantWrEn := isQuant
    let quantRdCombo := Signal.memoryComboRead readAddr4 qResult quantWrEn quantReadAddr

    -- FSM Control
    let residDone := isResid &&& (idx === (15#5 : Signal dom _))

    let substepInc := substep + 1#3
    let groupDone := isDct &&& isSub7
    let lastGroup := grpIdx === (3#3 : Signal dom _)
    let dctRowDone := isDctRow &&& groupDone &&& lastGroup
    let dctColDone := isDctCol &&& groupDone &&& lastGroup

    let grpInc := grpIdx + 1#3
    let startAndDone := start &&& isDone

    let grpIdxNext := hw_cond grpIdx
      | startAndIdle => (0#3 : Signal dom _)
      | startAndDone => (0#3 : Signal dom _)
      | dctRowDone   => (0#3 : Signal dom _)
      | groupDone    => grpInc

    let substepNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | residDone    => (0#3 : Signal dom _)
      | isDct        => substepInc

    let quantDone := isQuant &&& (idx === (15#5 : Signal dom _))

    let idxInc := idx + 1#5
    let idxNext := hw_cond (0#5 : Signal dom _)
      | startAndIdle => (0#5 : Signal dom _)
      | residDone    => (0#5 : Signal dom _)
      | dctColDone   => (0#5 : Signal dom _)
      | isResid      => idxInc
      | isQuant      => idxInc
    let phaseNext := hw_cond phase
      | startAndIdle => (1#3 : Signal dom _)
      | residDone    => (2#3 : Signal dom _)
      | dctRowDone   => (3#3 : Signal dom _)
      | dctColDone   => (4#3 : Signal dom _)
      | quantDone    => (5#3 : Signal dom _)
      | startAndDone => (1#3 : Signal dom _)

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3  phaseNext,
      Signal.register 0#5  idxNext,
      Signal.register 0#3  substepNext,
      Signal.register 0#3  grpIdxNext,
      Signal.register false doneNext,
      Signal.register 0#16 qResult,
      Signal.register 0#16 v0Next,
      Signal.register 0#16 v1Next,
      Signal.register 0#16 v2Next,
      Signal.register 0#16 v3Next,
      Signal.register 0#2  (Signal.pure 0#2),
      Signal.register 0#16 quantRdCombo  -- V2: capture combo-read data for external access
    ]

  -- Extract outputs
  let done := EncoderPipeState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let phaseVal := EncoderPipeState.phase state
  let phaseU32 := 0#29 ++ phaseVal
  -- V2: registered combo-read data (1-cycle read latency from quantReadAddr)
  let quantReadData := EncoderPipeState.dummy state

  bundleAll! [doneU32, phaseU32, quantReadData]

end Sparkle.IP.Video.H264.EncoderSynth
