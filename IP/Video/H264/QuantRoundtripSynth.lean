/-
  H.264 Quant/Dequant Roundtrip — Synthesizable Module for JIT Testing

  A minimal synthesizable pipeline that:
  1. Reads 16 coefficients from input memory (combo-read)
  2. Applies forward quantization (fixed QP=0, posClass=0)
  3. Applies inverse dequantization
  4. Writes results to output memory

  This module validates the JIT workflow for H.264 processing:
  load coefficients → run FSM → read results → compare with golden.

  Reference: ITU-T H.264 Table 8-12 (MF), Table 8-13 (V)
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.QuantRoundtripSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- State definition (4 registers)
-- ============================================================================

-- FSM: 0=IDLE, 1=PROCESS, 2=DONE
declare_signal_state QDState
  | fsm     : BitVec 2  := 0#2
  | idx     : BitVec 5  := 0#5
  | done    : Bool       := false
  | lastOut : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (for golden comparison in tests)
-- ============================================================================

/-- Pure quant→dequant roundtrip matching the synthesizable module.
    Fixed QP=0, posClass=0: MF=13107, f=5461, qbits=15, V=10.
    Dequant includes rounding: (level * V + 2) / 4. -/
def quantDequantRef (coeff : Int) : Int :=
  let absCoeff := coeff.natAbs
  let level := (absCoeff * 13107 + 5461) / 32768  -- (abs * MF + f) >>> qbits
  let dequant := (level * 10 + 2) / 4             -- (level * V + rounding) >>> 2
  if coeff >= 0 then (dequant : Int) else -(dequant : Int)

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Quant→Dequant roundtrip synthesis module.
    Inputs: start, writeEn/writeAddr/writeData for loading coefficients.
    Outputs: done (32-bit), current idx (32-bit), last output (32-bit).

    Internal: input memory (16×16-bit combo-read), output memory (16×16-bit).
    After asserting start, processes 16 coefficients in 16 cycles.
    Use JIT.setMem/getMem to access input/output memories directly. -/
def quantDequantSynth {dom : DomainConfig}
    (start : Signal dom Bool)
    (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsm := QDState.fsm state
    let idx := QDState.idx state

    let isIdle    := fsm === (0#2 : Signal dom _)
    let isProcess := fsm === (1#2 : Signal dom _)
    let isDone    := fsm === (2#2 : Signal dom _)
    let startAndIdle := start &&& isIdle

    -- Read input memory at current processing index (same-cycle read)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4

    -- === Quant → Dequant computation (fixed QP=0, posClass=0) ===
    -- MF=13107, f=5461, qbits=15, V=10

    -- 1. Sign bit extraction (bit 15 of 16-bit 2's complement)
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1

    -- 2. Absolute value via 2's complement negation
    let negCoeff := 0#16 - inputCoeff
    let absCoeff := Signal.mux isNeg negCoeff inputCoeff

    -- 3. Widen to 32 bits for multiplication
    let absCoeff32 := 0#16 ++ absCoeff

    -- 4. Forward quantization: level = (absCoeff * 13107 + 5461) >> 15
    let product := absCoeff32 * 13107#32
    let rounded := product + 5461#32
    let level16 := rounded.map (BitVec.extractLsb' 15 16 ·)

    -- 5. Inverse dequantization: dequant = (level * 10 + 2) >> 2
    let level32 := 0#16 ++ level16
    let dequantRaw := level32 * 10#32
    let dequantRounded := dequantRaw + 2#32
    let dequant16 := dequantRounded.map (BitVec.extractLsb' 2 16 ·)

    -- 6. Restore sign
    let negDequant := 0#16 - dequant16
    let result := Signal.mux isNeg negDequant dequant16

    -- Write result to output memory (write during PROCESS, read addr 0 for state capture)
    let outMemRead := Signal.memory readAddr4 result isProcess (Signal.pure 0#4)

    -- === FSM transitions ===
    -- FSM stays in DONE until start is re-asserted
    let processDone := isProcess &&& (idx === (15#5 : Signal dom _))
    let startAndDone := start &&& isDone
    let fsmNext := hw_cond fsm
      | startAndIdle => (1#2 : Signal dom _)
      | processDone  => (2#2 : Signal dom _)
      | startAndDone => (1#2 : Signal dom _)

    let idxInc := idx + 1#5
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

  -- Extract outputs (outside the loop)
  let done := QDState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let idx := QDState.idx state
  let idxU32 := 0#27 ++ idx
  let lastOut := QDState.lastOut state
  let lastOut32 := 0#16 ++ lastOut

  bundleAll! [doneU32, idxU32, lastOut32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign quantDequantSynth ".lake/build/gen/h264/quant_roundtrip.sv" ".lake/build/gen/h264/quant_roundtrip_cppsim.h"

end Sparkle.IP.Video.H264.QuantRoundtripSynth
