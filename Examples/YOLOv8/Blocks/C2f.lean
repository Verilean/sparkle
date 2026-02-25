/-
  C2f Block — Signal DSL

  Cross Stage Partial with 2 convolutions.
  This is the main feature extraction block in YOLOv8.

  Architecture:
    1. 1x1 conv splits input channels into two halves
    2. One half passes through N bottleneck blocks
    3. All intermediate outputs are concatenated
    4. Final 1x1 conv merges back

  This module implements the controller FSM that sequences
  the sub-operations. The actual convolutions use the shared
  Conv2DEngine managed by the top-level controller.

  FSM states:
    IDLE (0)     → waiting for start
    SPLIT (1)    → 1x1 conv to split channels
    BOTTLENECK (2) → running N bottleneck blocks sequentially
    CONCAT (3)   → concatenating outputs (managed by buffer addressing)
    MERGE (4)    → final 1x1 conv to merge
    DONE (5)     → result ready
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Blocks.C2f

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- C2f block controller FSM.

    Manages the data flow through split → bottleneck(s) → concat → merge.
    The actual computation is performed by shared Conv2DEngine instances
    controlled by the top-level SoC.

    State registers (5 total):
      0: fsmState    (BitVec 3)  — IDLE/SPLIT/BOTTLENECK/CONCAT/MERGE/DONE
      1: bottleneckIdx (BitVec 4) — current bottleneck index (0..N-1)
      2: maxBottlenecks (BitVec 4) — total number of bottlenecks
      3: resultReady  (Bool)      — output ready flag
      4: doneFlag     (Bool)      — done pulse

    Inputs:
      - subOpDone: done signal from the currently active sub-operation
      - start:     begin C2f computation
      - numBottlenecks: number of bottleneck blocks (N)

    Outputs:
      - phase:  current phase (for routing control signals)
      - bottleneckIdx: which bottleneck is active
      - done:   result valid pulse
-/
def c2fController {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    (numBottlenecks : Signal dom (BitVec 4))
    : Signal dom (BitVec 3 × BitVec 4 × Bool) :=
  let loopState := Signal.loop fun state =>
    let fsmReg    := projN! state 5 0  -- BitVec 3
    let bnIdxReg  := projN! state 5 1  -- BitVec 4
    let maxBnReg  := projN! state 5 2  -- BitVec 4
    let readyReg  := projN! state 5 3  -- Bool
    let doneReg   := projN! state 5 4  -- Bool

    let isIdle       := (· == ·) <$> fsmReg <*> Signal.pure 0#3
    let isSplit      := (· == ·) <$> fsmReg <*> Signal.pure 1#3
    let isBottleneck := (· == ·) <$> fsmReg <*> Signal.pure 2#3
    let isConcat     := (· == ·) <$> fsmReg <*> Signal.pure 3#3
    let isMerge      := (· == ·) <$> fsmReg <*> Signal.pure 4#3
    let isDone       := (· == ·) <$> fsmReg <*> Signal.pure 5#3

    let startAndIdle := (· && ·) <$> start <*> isIdle
    let splitDone := (· && ·) <$> subOpDone <*> isSplit

    -- Bottleneck iteration
    let bnIdxInc := (· + ·) <$> bnIdxReg <*> Signal.pure 1#4
    let bnDone := (· && ·) <$> subOpDone <*> isBottleneck
    let allBnDone := (· && ·) <$> bnDone <*>
      ((· == ·) <$> bnIdxInc <*> maxBnReg)
    let moreBn := (· && ·) <$> bnDone <*>
      ((fun x => !x) <$> ((· == ·) <$> bnIdxInc <*> maxBnReg))

    let concatDone := (· && ·) <$> subOpDone <*> isConcat
    let mergeDone := (· && ·) <$> subOpDone <*> isMerge

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#3)       -- IDLE → SPLIT
        (Signal.mux splitDone (Signal.pure 2#3)        -- SPLIT → BOTTLENECK
          (Signal.mux allBnDone (Signal.pure 3#3)      -- last BN → CONCAT
            (Signal.mux concatDone (Signal.pure 4#3)   -- CONCAT → MERGE
              (Signal.mux mergeDone (Signal.pure 5#3)  -- MERGE → DONE
                (Signal.mux isDone (Signal.pure 0#3)   -- DONE → IDLE
                  fsmReg)))))

    -- Bottleneck index
    let bnIdxNext :=
      Signal.mux startAndIdle (Signal.pure 0#4)
        (Signal.mux moreBn bnIdxInc
          bnIdxReg)

    -- Max bottlenecks: latch on start
    let maxBnNext := Signal.mux startAndIdle numBottlenecks maxBnReg

    -- Ready flag
    let readyNext := mergeDone

    -- Done pulse
    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3 fsmNext,
      Signal.register 0#4 bnIdxNext,
      Signal.register 0#4 maxBnNext,
      Signal.register false readyNext,
      Signal.register false doneNext
    ]

  let phaseOut := projN! loopState 5 0
  let bnIdxOut := projN! loopState 5 1
  let doneOut := projN! loopState 5 4
  bundle3 phaseOut bnIdxOut doneOut

#synthesizeVerilog c2fController

end Sparkle.Examples.YOLOv8.Blocks.C2f
