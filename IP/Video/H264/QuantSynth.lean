/-
  H.264 Forward Quantization — Synthesizable Module

  Forward quantization FSM for a single 4×4 block (fixed QP=20):
  1. Reads 16 DCT coefficients from input memory (combo-read)
  2. Applies forward quantization: level = (|coeff| * MF + f) >> qbits
  3. Writes quantized levels to output memory

  For QP=20: qp%6=2, qp/6=3 → MF=[10082, 4194, 6554]
  qbits = 15 + 3 = 18, f = 2^18 / 3 = 87381

  Position class LUT (same as DequantSynth):
    bothEven (corner) → class 0 → MF=10082
    bothOdd           → class 1 → MF=4194
    mixed             → class 2 → MF=6554

  Reference: ITU-T H.264 Section 8.5.11
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.Quant

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.QuantSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.IP.Video.H264.Quant

-- ============================================================================
-- State definition (4 registers)
-- ============================================================================

-- FSM: 0=IDLE, 1=PROCESS, 2=DONE
declare_signal_state QuantState
  | fsm  : BitVec 2  := 0#2
  | idx  : BitVec 5  := 0#5
  | done : Bool       := false
  | last : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (for golden comparison in tests)
-- ============================================================================

/-- MF lookup for given QP.
    Returns MF[posClass(pos)] for the forward quantization. -/
private def mfLookup (pos : Nat) (qp : Nat := 20) : Nat :=
  let row := pos / 4
  let col := pos % 4
  let pc := if row % 2 == 0 && col % 2 == 0 then 0
            else if row % 2 == 0 || col % 2 == 0 then 2
            else 1
  let (mf0, mf1, mf2, _, _) := quantParams qp
  match pc with
  | 0 => mf0
  | 1 => mf1
  | _ => mf2

/-- Pure forward quantization for given QP (default QP=20).
    level = sign(coeff) * ((|coeff| * MF + f) >> qbits) -/
def quantRef (coeff : Int) (pos : Nat) (qp : Nat := 20) : Int :=
  let (_, _, _, f, qbits) := quantParams qp
  let mf := mfLookup pos (qp := qp)
  let absCoeff := coeff.natAbs
  let level := (absCoeff * mf + f) >>> qbits
  if coeff >= 0 then Int.ofNat level else -Int.ofNat level

/-- Quantize a full 4×4 block at given QP (default QP=20). -/
def quantBlockRef (coeffs : Array Int) (qp : Nat := 20) : Array Int :=
  (List.range 16).toArray.map fun i =>
    if h : i < coeffs.size then quantRef coeffs[i] i (qp := qp) else 0

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Forward quantization synthesis module (parameterized QP via input ports).
    Inputs: start, writeEn/writeAddr/writeData for loading DCT coefficients,
            quantMF0/1/2 for MF per position class, quantF for rounding offset,
            quantShift for qbits shift amount.
    Outputs: done (32-bit), current idx (32-bit), last output (32-bit).

    Internal: input memory (16×16-bit combo-read), output memory (16×16-bit).
    After asserting start, processes 16 coefficients in 16 cycles.

    quantMF0 = MF[qp%6][0] (corner positions)
    quantMF1 = MF[qp%6][1] (other even-even positions)
    quantMF2 = MF[qp%6][2] (mixed even-odd positions)
    quantF = 2^qbits / 3 (intra rounding offset)
    quantShift = 15 + qp/6 (qbits shift amount) -/
def quantModule {dom : DomainConfig}
    (start : Signal dom Bool)
    (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16))
    (quantMF0 : Signal dom (BitVec 32))
    (quantMF1 : Signal dom (BitVec 32))
    (quantMF2 : Signal dom (BitVec 32))
    (quantF : Signal dom (BitVec 32))
    (quantShift : Signal dom (BitVec 5))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsm := QuantState.fsm state
    let idx := QuantState.idx state

    let isIdle    := fsm === (0#2 : Signal dom _)
    let isProcess := fsm === (1#2 : Signal dom _)
    let isDone    := fsm === (2#2 : Signal dom _)
    let startAndIdle := start &&& isIdle

    -- Read input memory at current processing index (same-cycle read)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4

    -- === Forward quantization computation (fixed QP=20) ===
    -- level = sign * ((|coeff| * MF + f) >> qbits)
    -- QP=20: qbits=18, f=87381, MF=[10082, 4194, 6554]

    -- 1. Sign bit extraction (bit 15 of 16-bit 2's complement)
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1

    -- 2. Absolute value via 2's complement negation
    let negCoeff := (· - ·) <$> Signal.pure 0#16 <*> inputCoeff
    let absCoeff := Signal.mux isNeg negCoeff inputCoeff

    -- 3. Widen to 32 bits for multiplication
    let absCoeff32 := 0#16 ++ absCoeff

    -- 4. Determine MF based on position class
    -- idx bits: [3:2] = row, [1:0] = col
    -- row_even = !(idx[2]), col_even = !(idx[0])
    let idxBit0 := idx.map (BitVec.extractLsb' 0 1 ·)  -- col bit 0
    let idxBit2 := idx.map (BitVec.extractLsb' 2 1 ·)  -- row bit 0

    -- row_even: row%2==0 means row bit 0 == 0
    let rowOdd := idxBit2 === 1#1
    -- col_even: col%2==0 means col bit 0 == 0
    let colOdd := idxBit0 === 1#1

    -- posClass: 0 = both even, 1 = both odd, 2 = mixed
    let bothEven := ((fun x => !x) <$> rowOdd) &&& ((fun x => !x) <$> colOdd)
    let bothOdd := rowOdd &&& colOdd

    -- MF values: selected from input ports by position class
    let mfVal := Signal.mux bothEven quantMF0
                   (Signal.mux bothOdd quantMF1
                     quantMF2)

    -- 5. Multiply: product = absCoeff * MF
    let product := (· * ·) <$> absCoeff32 <*> mfVal

    -- 6. Add rounding offset from input port
    let withF := (· + ·) <$> product <*> quantF

    -- 7. Variable shift right by qbits from input port
    let quantShift32 := 0#27 ++ quantShift
    let shifted := (· >>> ·) <$> withF <*> quantShift32
    let level16 := shifted.map (BitVec.extractLsb' 0 16 ·)

    -- 8. Restore sign
    let negLevel := (· - ·) <$> Signal.pure 0#16 <*> level16
    let result := Signal.mux isNeg negLevel level16

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
  let done := QuantState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let idx := QuantState.idx state
  let idxU32 := 0#27 ++ idx
  let lastOut := QuantState.last state
  let lastOut32 := 0#16 ++ lastOut

  bundleAll! [doneU32, idxU32, lastOut32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign quantModule ".lake/build/gen/h264/fwd_quant.sv" ".lake/build/gen/h264/fwd_quant_cppsim.h"

end Sparkle.IP.Video.H264.QuantSynth
