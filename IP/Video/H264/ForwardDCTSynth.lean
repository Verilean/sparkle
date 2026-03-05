/-
  H.264 Forward DCT — Synthesizable Module

  Forward 4×4 integer DCT FSM:
  Phase ROW (32 cycles): For each row i (0-3), 8 sub-steps:
    Sub-steps 0-3: Read input[i*4+0..3] into val registers
    Sub-steps 4-7: Compute butterfly, write to intermediate memory
      s0 = val0+val3, s1 = val1+val2, d0 = val0-val3, d1 = val1-val2
      Y0 = s0+s1, Y1 = 2*d0+d1, Y2 = s0-s1, Y3 = d0-2*d1

  Phase COL (32 cycles): For each col j (0-3), 8 sub-steps:
    Sub-steps 0-3: Read intermediate[0*4+j..3*4+j] into val registers
    Sub-steps 4-7: Compute butterfly (same, no rounding), write to output memory

  Total: 64 cycles + FSM overhead.

  Reference: ITU-T H.264 Section 8.5.10
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.ForwardDCTSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- State definition (8 registers)
-- ============================================================================

-- FSM: 0=IDLE, 1=ROW, 2=COL, 3=DONE
declare_signal_state FwdDCTState
  | fsm     : BitVec 3  := 0#3
  | grpIdx  : BitVec 3  := 0#3
  | substep : BitVec 3  := 0#3
  | done    : Bool       := false
  | val0    : BitVec 16 := 0#16
  | val1    : BitVec 16 := 0#16
  | val2    : BitVec 16 := 0#16
  | val3    : BitVec 16 := 0#16

-- ============================================================================
-- Pure reference function (for golden comparison)
-- ============================================================================

/-- Pure forward DCT matching DCT.forwardDCT. -/
def fwdDCTRef (input : Array Int) : Array Int :=
  let temp := Id.run do
    let mut t := Array.replicate 16 (0 : Int)
    for i in [:4] do
      let get := fun c => if h : i * 4 + c < input.size then input[i * 4 + c] else 0
      let s0 := get 0 + get 3
      let s1 := get 1 + get 2
      let d0 := get 0 - get 3
      let d1 := get 1 - get 2
      t := t.set! (i * 4 + 0) (s0 + s1)
      t := t.set! (i * 4 + 1) (2 * d0 + d1)
      t := t.set! (i * 4 + 2) (s0 - s1)
      t := t.set! (i * 4 + 3) (d0 - 2 * d1)
    t
  Id.run do
    let mut out := Array.replicate 16 (0 : Int)
    for j in [:4] do
      let get := fun r => if h : r * 4 + j < temp.size then temp[r * 4 + j] else 0
      let s0 := get 0 + get 3
      let s1 := get 1 + get 2
      let d0 := get 0 - get 3
      let d1 := get 1 - get 2
      out := out.set! (0 * 4 + j) (s0 + s1)
      out := out.set! (1 * 4 + j) (2 * d0 + d1)
      out := out.set! (2 * 4 + j) (s0 - s1)
      out := out.set! (3 * 4 + j) (d0 - 2 * d1)
    out

-- ============================================================================
-- Synthesizable module
-- ============================================================================

/-- Forward DCT synthesis module.
    Inputs: start, writeEn/writeAddr/writeData for loading residual values.
    Outputs: done (32-bit), grpIdx (32-bit), substep (32-bit).

    Internal memories: input (combo-read), intermediate (combo-read), output.
    64 cycles: 32 row-transform + 32 col-transform. -/
def fwdDCTModule {dom : DomainConfig}
    (start : Signal dom Bool)
    (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16))
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsm     := FwdDCTState.fsm     state
    let grpIdx  := FwdDCTState.grpIdx  state
    let substep := FwdDCTState.substep state
    let v0      := FwdDCTState.val0    state
    let v1      := FwdDCTState.val1    state
    let v2      := FwdDCTState.val2    state
    let v3      := FwdDCTState.val3    state

    -- FSM decode
    let isIdle := fsm === (0#3 : Signal dom _)
    let isRow  := fsm === (1#3 : Signal dom _)
    let isCol  := fsm === (2#3 : Signal dom _)
    let isDone := fsm === (3#3 : Signal dom _)
    let startAndIdle := start &&& isIdle
    let active := isRow ||| isCol

    -- Substep decode
    let isSub0 := substep === (0#3 : Signal dom _)
    let isSub1 := substep === (1#3 : Signal dom _)
    let isSub2 := substep === (2#3 : Signal dom _)
    let isSub3 := substep === (3#3 : Signal dom _)
    let isSub4 := substep === (4#3 : Signal dom _)
    let isSub5 := substep === (5#3 : Signal dom _)
    let isSub6 := substep === (6#3 : Signal dom _)
    let isSub7 := substep === (7#3 : Signal dom _)
    let isReading := isSub0 ||| isSub1 ||| isSub2 ||| isSub3
    let isWriting := isSub4 ||| isSub5 ||| isSub6 ||| isSub7

    -- Zero-extend grpIdx[1:0] and substep[1:0] to 4 bits for address math
    let grp4' := (· ++ ·) <$> Signal.pure 0#2 <*> (grpIdx.map (BitVec.extractLsb' 0 2 ·))
    let subLo4 := (· ++ ·) <$> Signal.pure 0#2 <*> (substep.map (BitVec.extractLsb' 0 2 ·))

    -- Read address computation (all 4-bit arithmetic)
    -- Row read: addr = grp*4 + subLo (row-major: row*4+col)
    let rowReadAddr := (· + ·) <$> ((· * ·) <$> grp4' <*> Signal.pure 4#4)
                                <*> subLo4
    -- Col read: addr = subLo*4 + grp (column access: row*4+col, row=subLo, col=grp)
    let colReadAddr := (· + ·) <$> ((· * ·) <$> subLo4 <*> Signal.pure 4#4)
                                <*> grp4'

    let readAddr4 := Signal.mux isRow rowReadAddr colReadAddr

    -- Write address: same formula as read (substep[1:0] for 4,5,6,7 gives 0,1,2,3)
    let intWriteAddr := Signal.mux isRow rowReadAddr colReadAddr

    -- Input memory (combo-read): external write port, read during row phase
    let inputData := Signal.memoryComboRead writeAddr writeData writeEn readAddr4

    -- Forward DCT butterfly computation from stored val registers
    -- s0 = v0+v3, s1 = v1+v2, d0 = v0-v3, d1 = v1-v2
    let s0 := (· + ·) <$> v0 <*> v3
    let s1 := (· + ·) <$> v1 <*> v2
    let d0 := (· - ·) <$> v0 <*> v3
    let d1 := (· - ·) <$> v1 <*> v2

    -- Y0 = s0+s1, Y1 = 2*d0+d1, Y2 = s0-s1, Y3 = d0-2*d1
    -- 2*d0 via add-to-self, 2*d1 via add-to-self
    let d0x2 := (· + ·) <$> d0 <*> d0
    let d1x2 := (· + ·) <$> d1 <*> d1

    let y0 := (· + ·) <$> s0 <*> s1
    let y1 := (· + ·) <$> d0x2 <*> d1
    let y2 := (· - ·) <$> s0 <*> s1
    let y3 := (· - ·) <$> d0 <*> d1x2

    -- Select butterfly output based on substep (4→Y0, 5→Y1, 6→Y2, 7→Y3)
    -- Same butterfly for both row and col phases (no rounding in forward DCT)
    let butterflyOut := hw_cond y0
      | isSub4 => y0
      | isSub5 => y1
      | isSub6 => y2
      | isSub7 => y3

    -- Intermediate memory: write during row write phase, combo-read during col read phase
    let interWrEn := isRow &&& isWriting
    let interRdAddr := Signal.mux (isCol &&& isReading) readAddr4 (Signal.pure 0#4)
    let interData := Signal.memoryComboRead intWriteAddr butterflyOut interWrEn interRdAddr

    -- Output memory: write during col write phase, read externally
    let outWrEn := isCol &&& isWriting
    let _outMemRead := Signal.memory intWriteAddr butterflyOut outWrEn (Signal.pure 0#4)

    -- Data source for reading into val registers
    let memSrcData := Signal.mux isRow inputData interData

    -- Update val registers during read phase
    let v0Next := Signal.mux (active &&& isSub0) memSrcData v0
    let v1Next := Signal.mux (active &&& isSub1) memSrcData v1
    let v2Next := Signal.mux (active &&& isSub2) memSrcData v2
    let v3Next := Signal.mux (active &&& isSub3) memSrcData v3

    -- Substep counter: 0→1→...→7→0
    let substepInc := (· + ·) <$> substep <*> Signal.pure 1#3
    let groupDone := active &&& isSub7
    let substepNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | active       => substepInc

    -- Group index: advance after substep 7
    let grpInc := (· + ·) <$> grpIdx <*> Signal.pure 1#3
    let lastGroup := grpIdx === (3#3 : Signal dom _)
    let rowPhaseDone := isRow &&& groupDone &&& lastGroup
    let colPhaseDone := isCol &&& groupDone &&& lastGroup

    let grpIdxNext := hw_cond (0#3 : Signal dom _)
      | startAndIdle => (0#3 : Signal dom _)
      | rowPhaseDone => (0#3 : Signal dom _)
      | groupDone    => grpInc

    -- FSM transitions
    let startAndDone := start &&& isDone
    let fsmNext := hw_cond fsm
      | startAndIdle => (1#3 : Signal dom _)
      | rowPhaseDone => (2#3 : Signal dom _)
      | colPhaseDone => (3#3 : Signal dom _)
      | startAndDone => (1#3 : Signal dom _)

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3  fsmNext,
      Signal.register 0#3  grpIdxNext,
      Signal.register 0#3  substepNext,
      Signal.register false doneNext,
      Signal.register 0#16 v0Next,
      Signal.register 0#16 v1Next,
      Signal.register 0#16 v2Next,
      Signal.register 0#16 v3Next
    ]

  -- Extract outputs
  let done := FwdDCTState.done state
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let grpVal := FwdDCTState.grpIdx state
  let grpU32 := (· ++ ·) <$> Signal.pure 0#29 <*> grpVal
  let subVal := FwdDCTState.substep state
  let subU32 := (· ++ ·) <$> Signal.pure 0#29 <*> subVal

  bundleAll! [doneU32, grpU32, subU32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign fwdDCTModule "IP/Video/H264/gen/fwd_dct.sv" "IP/Video/H264/gen/fwd_dct_cppsim.h"

end Sparkle.IP.Video.H264.ForwardDCTSynth
