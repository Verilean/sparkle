/-
  H.264 Reconstruction — Synthesizable Module

  Reconstruction FSM for a single 4×4 block:
  predicted[i] + residual[i], clamped to [0, 255]

  16-cycle processing: 1 pixel per cycle.
  - Read predicted pixel from prediction memory (combo-read)
  - Read residual value from residual memory (combo-read)
  - Add them (signed 16-bit arithmetic)
  - Clamp to [0, 255]
  - Write result to output memory

  Inputs: start, prediction memory write port, residual memory write port
  Outputs: done, output memory (16×8-bit as 16-bit values)

  Reference: ITU-T H.264 Section 8.5.13
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.ReconstructSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- State definition (4 registers)
-- ============================================================================

-- FSM: 0=IDLE, 1=PROCESS, 2=DONE
declare_signal_state ReconState
  | fsm  : BitVec 2  := 0#2
  | idx  : BitVec 5  := 0#5
  | done : Bool       := false
  | last : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (for golden comparison)
-- ============================================================================

/-- Pure reconstruction: predicted + residual, clamped to [0, 255]. -/
def reconstructRef (predicted : Array Nat) (residual : Array Int) : Array Nat :=
  (List.range 16).toArray.map fun i =>
    let p := if h : i < predicted.size then predicted[i] else 0
    let r := if h : i < residual.size then residual[i] else 0
    let val := Int.ofNat p + r
    if val < 0 then 0 else if val > 255 then 255 else val.toNat

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Reconstruction synthesis module.
    Inputs:
      start — assert to begin processing
      predWriteEn/predWriteAddr/predWriteData — load predicted pixels (unsigned 8-bit in 16-bit)
      resWriteEn/resWriteAddr/resWriteData — load residual values (signed 16-bit)
    Outputs: done (32-bit), idx (32-bit), last output (32-bit).

    Internal memories:
      mem0: prediction (16×16-bit, combo-read) — unsigned pixel values
      mem1: residual (16×16-bit, combo-read) — signed residual values
      mem2: output (16×16-bit) — clamped pixel results
    After asserting start, processes 16 pixels in 16 cycles. -/
def reconstructModule {dom : DomainConfig}
    (start : Signal dom Bool)
    (predWriteEn : Signal dom Bool)
    (predWriteAddr : Signal dom (BitVec 4))
    (predWriteData : Signal dom (BitVec 16))
    (resWriteEn : Signal dom Bool)
    (resWriteAddr : Signal dom (BitVec 4))
    (resWriteData : Signal dom (BitVec 16))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsm := ReconState.fsm state
    let idx := ReconState.idx state

    let isIdle    := fsm === (0#2 : Signal dom _)
    let isProcess := fsm === (1#2 : Signal dom _)
    let isDone    := fsm === (2#2 : Signal dom _)
    let startAndIdle := start &&& isIdle

    -- Current processing index (truncated to 4 bits)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)

    -- Prediction memory (combo-read): unsigned pixel values
    let predVal := Signal.memoryComboRead predWriteAddr predWriteData predWriteEn readAddr4

    -- Residual memory (combo-read): signed 16-bit values
    let resVal := Signal.memoryComboRead resWriteAddr resWriteData resWriteEn readAddr4

    -- === Reconstruction: predicted + residual, clamped [0, 255] ===

    -- Add predicted (unsigned, zero-extended) + residual (signed)
    -- Both are 16-bit; the sum may overflow, so we need signed comparison
    let sumVal := (· + ·) <$> predVal <*> resVal

    -- Clamp to [0, 255]:
    -- Check if negative (sign bit = 1) → clamp to 0
    -- Check if > 255 → clamp to 255
    -- Otherwise use sum

    let signBit := sumVal.map (BitVec.extractLsb' 15 1 ·)
    let isNegative := (· == ·) <$> signBit <*> Signal.pure 1#1

    -- Check if > 255: if not negative and upper byte (bits 15:8) is non-zero
    let upperByte := sumVal.map (BitVec.extractLsb' 8 8 ·)
    let upperNonZero := (fun x => !x) <$> ((· == ·) <$> upperByte <*> Signal.pure 0#8)
    let isOver255 := ((fun x => !x) <$> isNegative) &&& upperNonZero

    -- Clamped result
    let clampedVal := Signal.mux isNegative (Signal.pure 0#16)
                        (Signal.mux isOver255 (Signal.pure 255#16)
                          sumVal)

    -- Write clamped result to output memory
    let outMemRead := Signal.memory readAddr4 clampedVal isProcess (Signal.pure 0#4)

    -- === FSM transitions ===
    let processDone := isProcess &&& (idx === (15#5 : Signal dom _))
    let startAndDone := start &&& isDone
    let fsmNext := hw_cond fsm
      | startAndIdle => (1#2 : Signal dom _)
      | processDone  => (2#2 : Signal dom _)
      | startAndDone => (1#2 : Signal dom _)

    let idxInc := (· + ·) <$> idx <*> Signal.pure 1#5
    let idxNext := hw_cond (0#5 : Signal dom _)
      | startAndIdle  => (0#5 : Signal dom _)
      | startAndDone  => (0#5 : Signal dom _)
      | isProcess     => idxInc

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#2  fsmNext,
      Signal.register 0#5  idxNext,
      Signal.register false doneNext,
      Signal.register 0#16 outMemRead
    ]

  -- Extract outputs
  let done := ReconState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let idx := ReconState.idx state
  let idxU32 := (· ++ ·) <$> Signal.pure 0#27 <*> idx
  let lastOut := ReconState.last state
  let lastOut32 := (· ++ ·) <$> Signal.pure 0#16 <*> lastOut

  bundleAll! [doneU32, idxU32, lastOut32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign reconstructModule "IP/Video/H264/gen/reconstruct.sv" "IP/Video/H264/gen/reconstruct_cppsim.h"

end Sparkle.IP.Video.H264.ReconstructSynth
