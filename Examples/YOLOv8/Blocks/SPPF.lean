/-
  SPPF — Signal DSL

  Spatial Pyramid Pooling - Fast.
  Three sequential 5x5 max pools, then channel concatenation + 1x1 conv.

  In YOLOv8, SPPF uses three sequential 5x5 max-pool passes
  (equivalent to 5x5, 9x9, 13x13 receptive fields), then concatenates
  the original + 3 pooled versions and applies a 1x1 conv.

  This module implements the controller FSM.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Blocks.SPPF

open Sparkle.Core.Domain
open Sparkle.Core.Signal

private abbrev SPPFState := BitVec 3 × BitVec 2 × Bool × Bool

/-- SPPF controller FSM.

    Sequences: ConvBnSiLU → MaxPool1 → MaxPool2 → MaxPool3 → Concat → ConvBnSiLU
    Each max-pool pass reuses the same MaxPool engine on the entire feature map.

    State registers (4 total):
      0: fsmState   (BitVec 3)  — phase
      1: poolStage  (BitVec 2)  — which max-pool pass (0, 1, 2)
      2: resultReady (Bool)
      3: doneFlag   (Bool)

    FSM states:
      0: IDLE
      1: CONV_PRE    — initial 1x1 ConvBnSiLU (channel reduction)
      2: POOL        — max-pool pass (runs 3 times)
      3: CONCAT      — concatenate original + 3 pooled
      4: CONV_POST   — final 1x1 ConvBnSiLU (channel restore)
      5: DONE

    Inputs:
      - subOpDone: done signal from current sub-operation
      - start:     begin SPPF computation

    Outputs:
      - phase:     current FSM state
      - poolStage: which max-pool pass (0..2)
      - done:      result valid pulse
-/
private def sppfControllerBody {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    (state : Signal dom SPPFState) : Signal dom SPPFState :=
    let fsmReg     := projN! state 4 0  -- BitVec 3
    let poolStgReg := projN! state 4 1  -- BitVec 2
    let readyReg   := projN! state 4 2  -- Bool
    let doneReg    := projN! state 4 3  -- Bool

    let isIdle     := (· == ·) <$> fsmReg <*> Signal.pure 0#3
    let isConvPre  := (· == ·) <$> fsmReg <*> Signal.pure 1#3
    let isPool     := (· == ·) <$> fsmReg <*> Signal.pure 2#3
    let isConcat   := (· == ·) <$> fsmReg <*> Signal.pure 3#3
    let isConvPost := (· == ·) <$> fsmReg <*> Signal.pure 4#3
    let isDone     := (· == ·) <$> fsmReg <*> Signal.pure 5#3

    let startAndIdle := (· && ·) <$> start <*> isIdle
    let convPreDone  := (· && ·) <$> subOpDone <*> isConvPre
    let poolDone     := (· && ·) <$> subOpDone <*> isPool

    -- Pool stage counter
    let poolStgInc := (· + ·) <$> poolStgReg <*> Signal.pure 1#2
    let allPoolsDone := (· && ·) <$> poolDone <*>
      ((· == ·) <$> poolStgReg <*> Signal.pure 2#2)  -- 3 stages: 0,1,2
    let morePool := (· && ·) <$> poolDone <*>
      ((fun x => !x) <$> ((· == ·) <$> poolStgReg <*> Signal.pure 2#2))

    let concatDone   := (· && ·) <$> subOpDone <*> isConcat
    let convPostDone := (· && ·) <$> subOpDone <*> isConvPost

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#3)         -- IDLE → CONV_PRE
        (Signal.mux convPreDone (Signal.pure 2#3)        -- CONV_PRE → POOL
          (Signal.mux allPoolsDone (Signal.pure 3#3)     -- last POOL → CONCAT
            (Signal.mux concatDone (Signal.pure 4#3)     -- CONCAT → CONV_POST
              (Signal.mux convPostDone (Signal.pure 5#3) -- CONV_POST → DONE
                (Signal.mux isDone (Signal.pure 0#3)     -- DONE → IDLE
                  fsmReg)))))

    -- Pool stage: increment after each pool, reset on start
    let poolStgNext :=
      Signal.mux startAndIdle (Signal.pure 0#2)
        (Signal.mux morePool poolStgInc
          poolStgReg)

    let readyNext := convPostDone
    let doneNext := isDone

    bundleAll! [
      Signal.register 0#3 fsmNext,
      Signal.register 0#2 poolStgNext,
      Signal.register false readyNext,
      Signal.register false doneNext
    ]

def sppfController {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    : Signal dom (BitVec 3 × BitVec 2 × Bool) :=
  let loopState := Signal.loop fun state => sppfControllerBody subOpDone start state
  let phaseOut := projN! loopState 4 0
  let poolStgOut := projN! loopState 4 1
  let doneOut := projN! loopState 4 3
  bundle2 phaseOut (bundle2 poolStgOut doneOut)

def sppfControllerSimulate {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    : IO (Signal dom (BitVec 3 × BitVec 2 × Bool)) := do
  let loopState ← Signal.loopMemo (sppfControllerBody subOpDone start)
  let phaseOut := projN! loopState 4 0
  let poolStgOut := projN! loopState 4 1
  let doneOut := projN! loopState 4 3
  return bundle2 phaseOut (bundle2 poolStgOut doneOut)

#synthesizeVerilog sppfController

end Sparkle.Examples.YOLOv8.Blocks.SPPF
