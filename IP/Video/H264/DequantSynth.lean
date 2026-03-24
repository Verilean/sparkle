/-
  H.264 Dequantization — Synthesizable Module

  Inverse dequantization FSM for a single 4×4 block (fixed QP=20):
  1. Reads 16 quantized levels from input memory (combo-read)
  2. Applies inverse dequantization: coeff = level * V[posClass] * 2^(qp/6)
  3. Writes dequantized coefficients to output memory

  For QP=20: qp%6=2, qp/6=3 → V=[13,20,16], scale=2^3=8
  So: dequant(level, pos) = level * V[posClass(pos)] * 8

  Position class LUT (16 entries):
    pos  0: row=0 col=0 → class 0 (corner)      V=13 * 8 = 104
    pos  1: row=0 col=1 → class 2 (mixed)        V=16 * 8 = 128
    pos  2: row=0 col=2 → class 0 (corner)       V=13 * 8 = 104
    pos  3: row=0 col=3 → class 2 (mixed)        V=16 * 8 = 128
    pos  4: row=1 col=0 → class 2 (mixed)        V=16 * 8 = 128
    pos  5: row=1 col=1 → class 1 (other even)   V=20 * 8 = 160
    pos  6: row=1 col=2 → class 2 (mixed)        V=16 * 8 = 128
    pos  7: row=1 col=3 → class 1 (other even)   V=20 * 8 = 160
    pos  8: row=2 col=0 → class 0 (corner)       V=13 * 8 = 104
    pos  9: row=2 col=1 → class 2 (mixed)        V=16 * 8 = 128
    pos 10: row=2 col=2 → class 0 (corner)       V=13 * 8 = 104
    pos 11: row=2 col=3 → class 2 (mixed)        V=16 * 8 = 128
    pos 12: row=3 col=0 → class 2 (mixed)        V=16 * 8 = 128
    pos 13: row=3 col=1 → class 1 (other even)   V=20 * 8 = 160
    pos 14: row=3 col=2 → class 2 (mixed)        V=16 * 8 = 128
    pos 15: row=3 col=3 → class 1 (other even)   V=20 * 8 = 160

  Reference: ITU-T H.264 Section 8.5.12
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.Quant

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.DequantSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.IP.Video.H264.Quant

-- ============================================================================
-- State definition (4 registers)
-- ============================================================================

-- FSM: 0=IDLE, 1=PROCESS, 2=DONE
declare_signal_state DequantState
  | fsm  : BitVec 2  := 0#2
  | idx  : BitVec 5  := 0#5
  | done : Bool       := false
  | last : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (for golden comparison in tests)
-- ============================================================================

/-- V*scale lookup for given QP.
    Returns V[posClass(pos)] * 2^(qp/6). -/
private def vScale (qp : Nat) (pos : Nat) : Int :=
  let row := pos / 4
  let col := pos % 4
  let pc := if row % 2 == 0 && col % 2 == 0 then 0
            else if row % 2 == 0 || col % 2 == 0 then 2
            else 1
  let (vs0, vs1, vs2) := dequantScales qp
  match pc with
  | 0 => Int.ofNat vs0
  | 1 => Int.ofNat vs1
  | _ => Int.ofNat vs2

/-- Pure dequantization for given QP (default QP=20).
    dequant(level, pos) = level * V[posClass(pos)] * 2^(qp/6) -/
def dequantRef (level : Int) (pos : Nat) (qp : Nat := 20) : Int :=
  level * vScale qp pos

/-- Dequantize a full 4×4 block at given QP (default QP=20). -/
def dequantBlockRef (levels : Array Int) (qp : Nat := 20) : Array Int :=
  (List.range 16).toArray.map fun i =>
    if h : i < levels.size then dequantRef levels[i] i qp else 0

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Dequantization synthesis module (parameterized QP via input ports).
    Inputs: start, writeEn/writeAddr/writeData for loading quantized levels,
            vscale0/1/2 for QP-dependent V*scale values per position class.
    Outputs: done (32-bit), current idx (32-bit), last output (32-bit).

    Internal: input memory (16×16-bit combo-read), output memory (16×16-bit).
    After asserting start, processes 16 coefficients in 16 cycles.
    Use JIT.setMem/getMem to access input/output memories directly.

    vscale0 = V[qp%6][0] * 2^(qp/6) (corner positions)
    vscale1 = V[qp%6][1] * 2^(qp/6) (other even-even positions)
    vscale2 = V[qp%6][2] * 2^(qp/6) (mixed even-odd positions) -/
def dequantModule {dom : DomainConfig}
    (start : Signal dom Bool)
    (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16))
    (vscale0 : Signal dom (BitVec 32))
    (vscale1 : Signal dom (BitVec 32))
    (vscale2 : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsm := DequantState.fsm state
    let idx := DequantState.idx state

    let isIdle    := fsm === (0#2 : Signal dom _)
    let isProcess := fsm === (1#2 : Signal dom _)
    let isDone    := fsm === (2#2 : Signal dom _)
    let startAndIdle := start &&& isIdle

    -- Read input memory at current processing index (same-cycle read)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputLevel := Signal.memoryComboRead writeAddr writeData writeEn readAddr4

    -- === Dequantization computation (fixed QP=20) ===
    -- coeff = level * V[posClass] * 8
    -- We use a position-class LUT based on idx.
    -- posClass pattern for 4×4: 0,2,0,2, 2,1,2,1, 0,2,0,2, 2,1,2,1
    -- V*8 values: class0=104, class1=160, class2=128
    -- Simplified: use idx[0] and idx[2] bits to distinguish classes

    -- 1. Sign bit extraction (bit 15 of 16-bit 2's complement)
    let signBit := inputLevel.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1

    -- 2. Absolute value via 2's complement negation
    let negLevel := (· - ·) <$> Signal.pure 0#16 <*> inputLevel
    let absLevel := Signal.mux isNeg negLevel inputLevel

    -- 3. Widen to 32 bits for multiplication
    let absLevel32 := 0#16 ++ absLevel

    -- 4. Determine V*scale based on position class
    -- idx bits: [3:2] = row, [1:0] = col
    -- row_even = !(idx[2]), col_even = !(idx[0])
    let idxBit0 := idx.map (BitVec.extractLsb' 0 1 ·)  -- col bit 0
    let idxBit1 := idx.map (BitVec.extractLsb' 1 1 ·)  -- col bit 1
    let idxBit2 := idx.map (BitVec.extractLsb' 2 1 ·)  -- row bit 0
    let idxBit3 := idx.map (BitVec.extractLsb' 3 1 ·)  -- row bit 1

    -- row_even: row%2==0 means row bit 0 == 0
    let rowOdd := idxBit2 === 1#1
    -- col_even: col%2==0 means col bit 0 == 0
    let colOdd := idxBit0 === 1#1

    -- Suppress unused warnings
    let _ := idxBit1
    let _ := idxBit3

    -- posClass: 0 = both even, 1 = both odd, 2 = mixed
    let bothEven := ((fun x => !x) <$> rowOdd) &&& ((fun x => !x) <$> colOdd)
    let bothOdd := rowOdd &&& colOdd

    -- V*scale: selected from input ports by position class
    let vscale := Signal.mux bothEven vscale0
                    (Signal.mux bothOdd vscale1
                      vscale2)

    -- 5. Multiply: dequant = absLevel * vscale
    let product := (· * ·) <$> absLevel32 <*> vscale
    let dequant16 := product.map (BitVec.extractLsb' 0 16 ·)

    -- 6. Restore sign
    let negDequant := (· - ·) <$> Signal.pure 0#16 <*> dequant16
    let result := Signal.mux isNeg negDequant dequant16

    -- Write result to output memory
    let outMemRead := Signal.memory readAddr4 result isProcess (Signal.pure 0#4)

    -- === FSM transitions ===
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
  let done := DequantState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let idx := DequantState.idx state
  let idxU32 := 0#27 ++ idx
  let lastOut := DequantState.last state
  let lastOut32 := 0#16 ++ lastOut

  bundleAll! [doneU32, idxU32, lastOut32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign dequantModule ".lake/build/gen/h264/dequant.sv" ".lake/build/gen/h264/dequant_cppsim.h"

end Sparkle.IP.Video.H264.DequantSynth
