/-
  H.264 Decoder Pipeline — Synthesizable Top-Level

  Monolithic decoder pipeline FSM performing 3 stages sequentially:
    Phase 1 (DEQUANT, 16 cycles): quantized levels → dequantized coefficients
    Phase 2 (IDCT, 64 cycles): dequantized → residual via butterfly IDCT
    Phase 3 (RECON, 16 cycles): predicted + residual → clamped pixels [0,255]

  Total: ~96 cycles per 4×4 block (fixed QP=20).

  Uses internal memories for coefficient passing between stages:
    mem0: input quantized levels (16×16-bit, combo-read, loaded externally)
    mem1: dequantized coefficients (16×16-bit, written in phase 1, combo-read in phase 2)
    mem2: IDCT intermediate (16×16-bit, written/read during phase 2 butterfly)
    mem3: residual / IDCT output (16×16-bit, written in phase 2, combo-read in phase 3)
    mem4: prediction (16×16-bit, combo-read, loaded externally)
    mem5: output pixels (16×16-bit, written in phase 3)

  External interface:
    - start: assert to begin decoding
    - coeffWriteEn/coeffWriteAddr/coeffWriteData: load quantized levels
    - predWriteEn/predWriteAddr/predWriteData: load prediction pixels
    - Outputs: done (32-bit), phase (32-bit)

  Reference: ITU-T H.264 Section 7, 8
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.Quant
import IP.Video.H264.DequantSynth
import IP.Video.H264.IDCTSynth
import IP.Video.H264.ReconstructSynth

set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

namespace Sparkle.IP.Video.H264.DecoderSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.IP.Video.H264.DequantSynth
open Sparkle.IP.Video.H264.IDCTSynth
open Sparkle.IP.Video.H264.ReconstructSynth
open Sparkle.IP.Video.H264.Quant

-- ============================================================================
-- State definition (12 registers)
-- ============================================================================

-- Pipeline phase: 0=IDLE, 1=DEQUANT, 2=IDCT_ROW, 3=IDCT_COL, 4=RECON, 5=DONE
declare_signal_state DecoderPipeState
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
  | idctPhase : BitVec 2 := 0#2
  | dummy   : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (full decode pipeline at QP=20)
-- ============================================================================

/-- Pure decode pipeline: dequant → IDCT → reconstruct (parameterized QP, DC prediction).
    Takes quantized levels and predicted pixels, returns decoded pixels. -/
def decoderPipelineRef (quantLevels : Array Int) (predicted : Array Nat) (qp : Nat := 20) : Array Nat :=
  let dequantized := dequantBlockRef quantLevels (qp := qp)
  let residual := idctRef dequantized
  reconstructRef predicted residual

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Signed arithmetic right shift by 1 -/
private def sarBy1 {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let signBit := x.map (BitVec.extractLsb' 15 1 ·)
  let upper15 := x.map (BitVec.extractLsb' 1 15 ·)
  signBit ++ upper15

/-- Signed arithmetic right shift by 6 -/
private def sarBy6 {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let signBit := x.map (BitVec.extractLsb' 15 1 ·)
  let upper10 := x.map (BitVec.extractLsb' 6 10 ·)
  let sign2 := signBit ++ signBit
  let sign4 := sign2 ++ sign2
  let sign6 := sign2 ++ sign4
  sign6 ++ upper10

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Decoder pipeline synthesis module (monolithic FSM).
    Performs dequant → IDCT → reconstruct in a single Signal.loop.

    Inputs:
      start — assert to begin decoding
      coeffWriteEn/coeffWriteAddr/coeffWriteData — load quantized levels
      predWriteEn/predWriteAddr/predWriteData — load prediction pixels
      vscale0/1/2 — QP-dependent dequantization V*scale values
    Outputs: done (32-bit), phase (32-bit). -/
def decoderPipeline {dom : DomainConfig}
    (start : Signal dom Bool)
    (coeffWriteEn : Signal dom Bool)
    (coeffWriteAddr : Signal dom (BitVec 4))
    (coeffWriteData : Signal dom (BitVec 16))
    (predWriteEn : Signal dom Bool)
    (predWriteAddr : Signal dom (BitVec 4))
    (predWriteData : Signal dom (BitVec 16))
    (vscale0 : Signal dom (BitVec 32))
    (vscale1 : Signal dom (BitVec 32))
    (vscale2 : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let phase   := DecoderPipeState.phase   state
    let idx     := DecoderPipeState.idx     state
    let substep := DecoderPipeState.substep state
    let grpIdx  := DecoderPipeState.grpIdx  state
    let v0      := DecoderPipeState.val0    state
    let v1      := DecoderPipeState.val1    state
    let v2      := DecoderPipeState.val2    state
    let v3      := DecoderPipeState.val3    state

    -- Phase decode
    let isIdle    := phase === (0#3 : Signal dom _)
    let isDequant := phase === (1#3 : Signal dom _)
    let isIdctRow := phase === (2#3 : Signal dom _)
    let isIdctCol := phase === (3#3 : Signal dom _)
    let isRecon   := phase === (4#3 : Signal dom _)
    let isDone    := phase === (5#3 : Signal dom _)
    let startAndIdle := start &&& isIdle
    let isIdct := isIdctRow ||| isIdctCol

    -- Common index (truncated to 4 bits for memory addressing)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)

    -- ================================================================
    -- DEQUANT PHASE (16 cycles): same as DequantSynth
    -- ================================================================

    -- Input quantized levels memory (combo-read, loaded externally)
    let inputLevel := Signal.memoryComboRead coeffWriteAddr coeffWriteData coeffWriteEn readAddr4

    -- Sign handling
    let dqSignBit := inputLevel.map (BitVec.extractLsb' 15 1 ·)
    let dqIsNeg := dqSignBit === 1#1
    let dqNegLevel := 0#16 - inputLevel
    let dqAbsLevel := Signal.mux dqIsNeg dqNegLevel inputLevel
    let dqAbsLevel32 := 0#16 ++ dqAbsLevel

    -- Position class for QP=20: V*8 values
    let idxBit0 := idx.map (BitVec.extractLsb' 0 1 ·)
    let idxBit2 := idx.map (BitVec.extractLsb' 2 1 ·)
    let rowOdd := idxBit2 === 1#1
    let colOdd := idxBit0 === 1#1
    let bothEven := (~~~rowOdd) &&& (~~~colOdd)
    let bothOdd := rowOdd &&& colOdd
    let vscale := Signal.mux bothEven vscale0
                    (Signal.mux bothOdd vscale1 vscale2)

    let dqProduct := dqAbsLevel32 * vscale
    let dqResult16 := dqProduct.map (BitVec.extractLsb' 0 16 ·)
    let dqNegResult := 0#16 - dqResult16
    let dqResult := Signal.mux dqIsNeg dqNegResult dqResult16

    -- Dequantized memory (written in dequant phase, combo-read in IDCT phase)
    let dequantWrEn := isDequant
    let _dequantMem := Signal.memoryComboRead readAddr4 dqResult dequantWrEn (Signal.pure 0#4)

    -- ================================================================
    -- IDCT PHASE (64 cycles): butterfly transforms
    -- ================================================================

    -- IDCT substep and group decode
    let isSub0 := substep === (0#3 : Signal dom _)
    let isSub1 := substep === (1#3 : Signal dom _)
    let isSub2 := substep === (2#3 : Signal dom _)
    let isSub3 := substep === (3#3 : Signal dom _)
    let isSub4 := substep === (4#3 : Signal dom _)
    let isSub5 := substep === (5#3 : Signal dom _)
    let isSub6 := substep === (6#3 : Signal dom _)
    let isSub7 := substep === (7#3 : Signal dom _)
    let isIdctReading := isSub0 ||| isSub1 ||| isSub2 ||| isSub3
    let isIdctWriting := isSub4 ||| isSub5 ||| isSub6 ||| isSub7

    -- Zero-extend grpIdx[1:0] and substep[1:0] to 4 bits
    let grp4 := 0#2 ++ (grpIdx.map (BitVec.extractLsb' 0 2 ·))
    let subLo4 := 0#2 ++ (substep.map (BitVec.extractLsb' 0 2 ·))

    -- Row read: addr = grp*4 + subLo
    let idctRowAddr := (grp4 * 4#4) + subLo4
    -- Col read: addr = subLo*4 + grp
    let idctColAddr := (subLo4 * 4#4) + grp4
    let idctAddr := Signal.mux isIdctRow idctRowAddr idctColAddr

    -- Dequant memory read for IDCT row phase (combo-read at idctAddr)
    let dequantReadAddr := Signal.mux (isIdctRow &&& isIdctReading) idctAddr (Signal.pure 0#4)
    let dequantRdData := Signal.memoryComboRead readAddr4 dqResult dequantWrEn dequantReadAddr

    -- IDCT intermediate memory (written during row phase, combo-read during col phase)
    let idctInterWrEn := isIdctRow &&& isIdctWriting
    -- IDCT output / residual memory (written during col phase)
    let idctOutWrEn := isIdctCol &&& isIdctWriting

    -- Butterfly computation
    let s0 := v0 + v2
    let s1 := v0 - v2
    let d0 := (sarBy1 v1) - v3
    let d1 := v1 + (sarBy1 v3)

    -- Row results (no rounding)
    let rowR0 := s0 + d1
    let rowR1 := s1 + d0
    let rowR2 := s1 - d0
    let rowR3 := s0 - d1

    -- Col results (with +32 >>6)
    let colR0 := sarBy6 ((s0 + d1) + 32#16)
    let colR1 := sarBy6 ((s1 + d0) + 32#16)
    let colR2 := sarBy6 ((s1 - d0) + 32#16)
    let colR3 := sarBy6 ((s0 - d1) + 32#16)

    -- Select output based on substep
    let rowOut := hw_cond rowR0
      | isSub4 => rowR0
      | isSub5 => rowR1
      | isSub6 => rowR2
      | isSub7 => rowR3
    let colOut := hw_cond colR0
      | isSub4 => colR0
      | isSub5 => colR1
      | isSub6 => colR2
      | isSub7 => colR3

    let butterflyOut := Signal.mux isIdctRow rowOut colOut

    -- Intermediate memory for IDCT
    let interReadAddr := Signal.mux (isIdctCol &&& isIdctReading) idctAddr (Signal.pure 0#4)
    let interData := Signal.memoryComboRead idctAddr butterflyOut idctInterWrEn interReadAddr

    -- Residual / IDCT output memory (written in col phase, combo-read in recon phase)
    let residualMem := Signal.memoryComboRead idctAddr butterflyOut idctOutWrEn readAddr4

    -- IDCT data source for reading into val registers
    let idctSrcData := Signal.mux isIdctRow dequantRdData interData

    -- Update val registers during IDCT read phase
    let v0Next := Signal.mux (isIdct &&& isSub0) idctSrcData v0
    let v1Next := Signal.mux (isIdct &&& isSub1) idctSrcData v1
    let v2Next := Signal.mux (isIdct &&& isSub2) idctSrcData v2
    let v3Next := Signal.mux (isIdct &&& isSub3) idctSrcData v3

    -- ================================================================
    -- RECONSTRUCT PHASE (16 cycles)
    -- ================================================================

    -- Prediction memory (combo-read, loaded externally)
    let predVal := Signal.memoryComboRead predWriteAddr predWriteData predWriteEn readAddr4

    -- Residual value from IDCT output memory (combo-read)
    let resVal := residualMem

    -- Add and clamp
    let sumVal := predVal + resVal
    let rcSignBit := sumVal.map (BitVec.extractLsb' 15 1 ·)
    let rcIsNeg := rcSignBit === 1#1
    let upperByte := sumVal.map (BitVec.extractLsb' 8 8 ·)
    let upperNonZero := ~~~(upperByte === 0#8)
    let isOver255 := (~~~rcIsNeg) &&& upperNonZero
    let clampedVal := Signal.mux rcIsNeg (Signal.pure 0#16)
                        (Signal.mux isOver255 (Signal.pure 255#16) sumVal)

    -- Output pixel memory (written in recon phase)
    let outWrEn := isRecon
    let _outMem := Signal.memory readAddr4 clampedVal outWrEn (Signal.pure 0#4)

    -- ================================================================
    -- FSM Control
    -- ================================================================

    -- Dequant done: idx reaches 15
    let dequantDone := isDequant &&& (idx === (15#5 : Signal dom _))

    -- IDCT group/substep control
    let substepInc := substep + 1#3
    let groupDone := isIdct &&& isSub7
    let lastGroup := grpIdx === (3#3 : Signal dom _)
    let idctRowDone := isIdctRow &&& groupDone &&& lastGroup
    let idctColDone := isIdctCol &&& groupDone &&& lastGroup

    let grpInc := grpIdx + 1#3
    let grpIdxNext := hw_cond grpIdx
      | startAndIdle => (0#3 : Signal dom _)
      | idctRowDone  => (0#3 : Signal dom _)
      | groupDone    => grpInc

    let substepNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | dequantDone  => (0#3 : Signal dom _)
      | isIdct       => substepInc

    -- Recon done: idx reaches 15
    let reconDone := isRecon &&& (idx === (15#5 : Signal dom _))

    -- Index control
    let idxInc := idx + 1#5
    let idxNext := hw_cond (0#5 : Signal dom _)
      | startAndIdle => (0#5 : Signal dom _)
      | dequantDone  => (0#5 : Signal dom _)
      | idctColDone  => (0#5 : Signal dom _)
      | isDequant    => idxInc
      | isRecon      => idxInc

    -- Phase transitions
    let startAndDone := start &&& isDone
    let phaseNext := hw_cond phase
      | startAndIdle => (1#3 : Signal dom _)
      | dequantDone  => (2#3 : Signal dom _)
      | idctRowDone  => (3#3 : Signal dom _)
      | idctColDone  => (4#3 : Signal dom _)
      | reconDone    => (5#3 : Signal dom _)
      | startAndDone => (1#3 : Signal dom _)

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3  phaseNext,
      Signal.register 0#5  idxNext,
      Signal.register 0#3  substepNext,
      Signal.register 0#3  grpIdxNext,
      Signal.register false doneNext,
      Signal.register 0#16 clampedVal,
      Signal.register 0#16 v0Next,
      Signal.register 0#16 v1Next,
      Signal.register 0#16 v2Next,
      Signal.register 0#16 v3Next,
      Signal.register 0#2  (Signal.pure 0#2),
      Signal.register 0#16 (Signal.pure 0#16)
    ]

  -- Extract outputs
  let done := DecoderPipeState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let phaseVal := DecoderPipeState.phase state
  let phaseU32 := 0#29 ++ phaseVal

  bundleAll! [doneU32, phaseU32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign decoderPipeline ".lake/build/gen/h264/decoder_pipeline.sv" ".lake/build/gen/h264/decoder_pipeline_cppsim.h"

-- ============================================================================
-- V2: Decoder pipeline with external read port for reconstructed pixels
-- ============================================================================

/-- Decoder pipeline V2 — identical to decoderPipeline but adds a reconReadAddr
    input and returns reconReadData as a third output.
    Used as a sub-module inside h264FrameEncoder where the parent needs to
    read reconstructed pixels from the internal memory.

    Returns: (done : BitVec 32, phase : BitVec 32, reconReadData : BitVec 16) -/
def decoderPipelineV2 {dom : DomainConfig}
    (start : Signal dom Bool)
    (coeffWriteEn : Signal dom Bool)
    (coeffWriteAddr : Signal dom (BitVec 4))
    (coeffWriteData : Signal dom (BitVec 16))
    (predWriteEn : Signal dom Bool)
    (predWriteAddr : Signal dom (BitVec 4))
    (predWriteData : Signal dom (BitVec 16))
    (vscale0 : Signal dom (BitVec 32))
    (vscale1 : Signal dom (BitVec 32))
    (vscale2 : Signal dom (BitVec 32))
    (reconReadAddr : Signal dom (BitVec 4))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 16) :=
  let state := Signal.loop fun state =>
    let phase   := DecoderPipeState.phase   state
    let idx     := DecoderPipeState.idx     state
    let substep := DecoderPipeState.substep state
    let grpIdx  := DecoderPipeState.grpIdx  state
    let v0      := DecoderPipeState.val0    state
    let v1      := DecoderPipeState.val1    state
    let v2      := DecoderPipeState.val2    state
    let v3      := DecoderPipeState.val3    state

    -- Phase decode
    let isIdle    := phase === (0#3 : Signal dom _)
    let isDequant := phase === (1#3 : Signal dom _)
    let isIdctRow := phase === (2#3 : Signal dom _)
    let isIdctCol := phase === (3#3 : Signal dom _)
    let isRecon   := phase === (4#3 : Signal dom _)
    let isDone    := phase === (5#3 : Signal dom _)
    let startAndIdle := start &&& isIdle
    let isIdct := isIdctRow ||| isIdctCol

    -- Common index (truncated to 4 bits for memory addressing)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)

    -- DEQUANT PHASE
    let inputLevel := Signal.memoryComboRead coeffWriteAddr coeffWriteData coeffWriteEn readAddr4

    let dqSignBit := inputLevel.map (BitVec.extractLsb' 15 1 ·)
    let dqIsNeg := dqSignBit === 1#1
    let dqNegLevel := 0#16 - inputLevel
    let dqAbsLevel := Signal.mux dqIsNeg dqNegLevel inputLevel
    let dqAbsLevel32 := 0#16 ++ dqAbsLevel

    let idxBit0 := idx.map (BitVec.extractLsb' 0 1 ·)
    let idxBit2 := idx.map (BitVec.extractLsb' 2 1 ·)
    let rowOdd := idxBit2 === 1#1
    let colOdd := idxBit0 === 1#1
    let bothEven := (~~~rowOdd) &&& (~~~colOdd)
    let bothOdd := rowOdd &&& colOdd
    let vscale := Signal.mux bothEven vscale0
                    (Signal.mux bothOdd vscale1 vscale2)

    let dqProduct := dqAbsLevel32 * vscale
    let dqResult16 := dqProduct.map (BitVec.extractLsb' 0 16 ·)
    let dqNegResult := 0#16 - dqResult16
    let dqResult := Signal.mux dqIsNeg dqNegResult dqResult16

    let dequantWrEn := isDequant
    let _dequantMem := Signal.memoryComboRead readAddr4 dqResult dequantWrEn (Signal.pure 0#4)

    -- IDCT PHASE
    let isSub0 := substep === (0#3 : Signal dom _)
    let isSub1 := substep === (1#3 : Signal dom _)
    let isSub2 := substep === (2#3 : Signal dom _)
    let isSub3 := substep === (3#3 : Signal dom _)
    let isSub4 := substep === (4#3 : Signal dom _)
    let isSub5 := substep === (5#3 : Signal dom _)
    let isSub6 := substep === (6#3 : Signal dom _)
    let isSub7 := substep === (7#3 : Signal dom _)
    let isIdctReading := isSub0 ||| isSub1 ||| isSub2 ||| isSub3
    let isIdctWriting := isSub4 ||| isSub5 ||| isSub6 ||| isSub7

    let grp4 := 0#2 ++ (grpIdx.map (BitVec.extractLsb' 0 2 ·))
    let subLo4 := 0#2 ++ (substep.map (BitVec.extractLsb' 0 2 ·))

    let idctRowAddr := (grp4 * 4#4) + subLo4
    let idctColAddr := (subLo4 * 4#4) + grp4
    let idctAddr := Signal.mux isIdctRow idctRowAddr idctColAddr

    let dequantReadAddr := Signal.mux (isIdctRow &&& isIdctReading) idctAddr (Signal.pure 0#4)
    let dequantRdData := Signal.memoryComboRead readAddr4 dqResult dequantWrEn dequantReadAddr

    let idctInterWrEn := isIdctRow &&& isIdctWriting
    let idctOutWrEn := isIdctCol &&& isIdctWriting

    let s0 := v0 + v2
    let s1 := v0 - v2
    let d0 := (sarBy1 v1) - v3
    let d1 := v1 + (sarBy1 v3)

    let rowR0 := s0 + d1
    let rowR1 := s1 + d0
    let rowR2 := s1 - d0
    let rowR3 := s0 - d1

    let colR0 := sarBy6 ((s0 + d1) + 32#16)
    let colR1 := sarBy6 ((s1 + d0) + 32#16)
    let colR2 := sarBy6 ((s1 - d0) + 32#16)
    let colR3 := sarBy6 ((s0 - d1) + 32#16)

    let rowOut := hw_cond rowR0
      | isSub4 => rowR0
      | isSub5 => rowR1
      | isSub6 => rowR2
      | isSub7 => rowR3
    let colOut := hw_cond colR0
      | isSub4 => colR0
      | isSub5 => colR1
      | isSub6 => colR2
      | isSub7 => colR3

    let butterflyOut := Signal.mux isIdctRow rowOut colOut

    let interReadAddr := Signal.mux (isIdctCol &&& isIdctReading) idctAddr (Signal.pure 0#4)
    let interData := Signal.memoryComboRead idctAddr butterflyOut idctInterWrEn interReadAddr

    let residualMem := Signal.memoryComboRead idctAddr butterflyOut idctOutWrEn readAddr4

    let idctSrcData := Signal.mux isIdctRow dequantRdData interData

    let v0Next := Signal.mux (isIdct &&& isSub0) idctSrcData v0
    let v1Next := Signal.mux (isIdct &&& isSub1) idctSrcData v1
    let v2Next := Signal.mux (isIdct &&& isSub2) idctSrcData v2
    let v3Next := Signal.mux (isIdct &&& isSub3) idctSrcData v3

    -- RECONSTRUCT PHASE
    let predVal := Signal.memoryComboRead predWriteAddr predWriteData predWriteEn readAddr4
    let resVal := residualMem
    let sumVal := predVal + resVal
    let rcSignBit := sumVal.map (BitVec.extractLsb' 15 1 ·)
    let rcIsNeg := rcSignBit === 1#1
    let upperByte := sumVal.map (BitVec.extractLsb' 8 8 ·)
    let upperNonZero := ~~~(upperByte === 0#8)
    let isOver255 := (~~~rcIsNeg) &&& upperNonZero
    let clampedVal := Signal.mux rcIsNeg (Signal.pure 0#16)
                        (Signal.mux isOver255 (Signal.pure 255#16) sumVal)

    -- V2 change: use memoryComboRead with reconReadAddr, pipe through state register
    let outWrEn := isRecon
    let reconRdCombo := Signal.memoryComboRead readAddr4 clampedVal outWrEn reconReadAddr

    -- FSM Control
    let dequantDone := isDequant &&& (idx === (15#5 : Signal dom _))

    let substepInc := substep + 1#3
    let groupDone := isIdct &&& isSub7
    let lastGroup := grpIdx === (3#3 : Signal dom _)
    let idctRowDone := isIdctRow &&& groupDone &&& lastGroup
    let idctColDone := isIdctCol &&& groupDone &&& lastGroup

    let grpInc := grpIdx + 1#3
    let startAndDone := start &&& isDone

    let grpIdxNext := hw_cond grpIdx
      | startAndIdle => (0#3 : Signal dom _)
      | startAndDone => (0#3 : Signal dom _)
      | idctRowDone  => (0#3 : Signal dom _)
      | groupDone    => grpInc

    let substepNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | dequantDone  => (0#3 : Signal dom _)
      | isIdct       => substepInc

    let reconDone := isRecon &&& (idx === (15#5 : Signal dom _))

    let idxInc := idx + 1#5
    let idxNext := hw_cond (0#5 : Signal dom _)
      | startAndIdle => (0#5 : Signal dom _)
      | dequantDone  => (0#5 : Signal dom _)
      | idctColDone  => (0#5 : Signal dom _)
      | isDequant    => idxInc
      | isRecon      => idxInc
    let phaseNext := hw_cond phase
      | startAndIdle => (1#3 : Signal dom _)
      | dequantDone  => (2#3 : Signal dom _)
      | idctRowDone  => (3#3 : Signal dom _)
      | idctColDone  => (4#3 : Signal dom _)
      | reconDone    => (5#3 : Signal dom _)
      | startAndDone => (1#3 : Signal dom _)

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3  phaseNext,
      Signal.register 0#5  idxNext,
      Signal.register 0#3  substepNext,
      Signal.register 0#3  grpIdxNext,
      Signal.register false doneNext,
      Signal.register 0#16 clampedVal,
      Signal.register 0#16 v0Next,
      Signal.register 0#16 v1Next,
      Signal.register 0#16 v2Next,
      Signal.register 0#16 v3Next,
      Signal.register 0#2  (Signal.pure 0#2),
      Signal.register 0#16 reconRdCombo  -- V2: capture combo-read data for external access
    ]

  -- Extract outputs
  let done := DecoderPipeState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let phaseVal := DecoderPipeState.phase state
  let phaseU32 := 0#29 ++ phaseVal
  -- V2: registered combo-read data (1-cycle read latency from reconReadAddr)
  let reconReadData := DecoderPipeState.dummy state

  bundleAll! [doneU32, phaseU32, reconReadData]

end Sparkle.IP.Video.H264.DecoderSynth
