/-
  YOLOv8 Neck — Signal DSL

  Feature Pyramid Network (FPN) + Path Aggregation Network (PAN).

  Top-down path (FPN):
    P5 → Upsample 2x → Concat(P4) → C2f → N4
    N4 → Upsample 2x → Concat(P3) → C2f → N3

  Bottom-up path (PAN):
    N3 → Conv 3x3 s2 → Concat(N4) → C2f → N4'
    N4'→ Conv 3x3 s2 → Concat(P5) → C2f → N5'

  Outputs: N3, N4', N5' (three-scale feature maps for detection head)

  All convolutions reuse the shared Conv2DEngine.
  This module implements the controller FSM for sequencing.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Config
import Examples.YOLOv8.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Neck

open Sparkle.Core.Domain
open Sparkle.Core.Signal

private abbrev NeckState := BitVec 4 × BitVec 3 × Bool × Bool × Bool × Bool

/-- Neck controller FSM.

    Sequences the FPN top-down and PAN bottom-up paths.

    State registers (6 total):
      0: fsmState    (BitVec 4)  — current phase
      1: pathIdx     (BitVec 3)  — which path step (0-3)
      2: bufferSel   (Bool)      — ping-pong buffer
      3: n3Ready     (Bool)      — N3 output ready
      4: n4Ready     (Bool)      — N4' output ready
      5: doneFlag    (Bool)

    FSM states:
      0: IDLE
      1: FPN_UPSAMPLE  — upsample P5 or N4
      2: FPN_CONCAT    — concatenate with P4 or P3
      3: FPN_C2F       — C2f block
      4: PAN_CONV      — 3x3 stride-2 conv (downsample)
      5: PAN_CONCAT    — concatenate with N4 or P5
      6: PAN_C2F       — C2f block
      7: DONE

    Inputs:
      - subOpDone: done from current sub-operation
      - start:     begin neck computation

    Outputs:
      - phase:   current FSM state
      - pathIdx: which path step
      - done:    neck complete
-/
private def neckControllerBody {dom : DomainConfig}
    (subOpDone : Signal dom Bool) (start : Signal dom Bool)
    (state : Signal dom NeckState) : Signal dom NeckState :=
    let fsmReg    := projN! state 6 0  -- BitVec 4
    let pathReg   := projN! state 6 1  -- BitVec 3
    let bufSelReg := projN! state 6 2  -- Bool
    let n3Reg     := projN! state 6 3  -- Bool
    let n4Reg     := projN! state 6 4  -- Bool
    let doneReg   := projN! state 6 5  -- Bool

    let isIdle       := fsmReg === 0#4
    let isFpnUp      := fsmReg === 1#4
    let isFpnConcat  := fsmReg === 2#4
    let isFpnC2f     := fsmReg === 3#4
    let isPanConv    := fsmReg === 4#4
    let isPanConcat  := fsmReg === 5#4
    let isPanC2f     := fsmReg === 6#4
    let isDone       := fsmReg === 7#4

    let startAndIdle := start &&& isIdle
    let fpnUpDone    := subOpDone &&& isFpnUp
    let fpnConcDone  := subOpDone &&& isFpnConcat
    let fpnC2fDone   := subOpDone &&& isFpnC2f
    let panConvDone  := subOpDone &&& isPanConv
    let panConcDone  := subOpDone &&& isPanConcat
    let panC2fDone   := subOpDone &&& isPanC2f

    -- Path tracking: FPN has 2 steps (P5→N4, N4→N3), PAN has 2 steps (N3→N4', N4'→N5')
    let pathInc := pathReg + 1#3
    let fpnComplete := pathReg === 1#3  -- 2 FPN steps: 0,1
    let panComplete := pathReg === 3#3  -- 2 PAN steps: 2,3

    -- After FPN C2f: if FPN not done, loop back for next FPN step
    -- If FPN done, transition to PAN
    let fpnNotDone := fpnC2fDone &&& (~~~fpnComplete)
    let fpnAllDone := fpnC2fDone &&& fpnComplete

    -- After PAN C2f: if PAN not done, loop back for next PAN step
    let panNotDone := panC2fDone &&& (~~~panComplete)
    let panAllDone := panC2fDone &&& panComplete

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#4)         -- IDLE → FPN_UPSAMPLE
        (Signal.mux fpnUpDone (Signal.pure 2#4)          -- FPN_UP → FPN_CONCAT
          (Signal.mux fpnConcDone (Signal.pure 3#4)      -- FPN_CONCAT → FPN_C2F
            (Signal.mux fpnNotDone (Signal.pure 1#4)     -- FPN_C2F → FPN_UP (next step)
              (Signal.mux fpnAllDone (Signal.pure 4#4)   -- FPN done → PAN_CONV
                (Signal.mux panConvDone (Signal.pure 5#4) -- PAN_CONV → PAN_CONCAT
                  (Signal.mux panConcDone (Signal.pure 6#4) -- PAN_CONCAT → PAN_C2F
                    (Signal.mux panNotDone (Signal.pure 4#4) -- PAN_C2F → PAN_CONV (next)
                      (Signal.mux panAllDone (Signal.pure 7#4) -- PAN done → DONE
                        (Signal.mux isDone (Signal.pure 0#4) -- DONE → IDLE
                          fsmReg)))))))))

    -- Path index
    let pathNext :=
      Signal.mux startAndIdle (Signal.pure 0#3)
        (Signal.mux fpnC2fDone pathInc
          (Signal.mux panC2fDone pathInc
            pathReg))

    -- Buffer select
    let bufSelNext := bufSelReg

    -- Feature readiness
    let n3Next := Signal.mux (fpnC2fDone &&& fpnComplete) (Signal.pure true) n3Reg
    let n4Next := Signal.mux (panC2fDone &&& (pathReg === 2#3)) (Signal.pure true) n4Reg

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#4 fsmNext,
      Signal.register 0#3 pathNext,
      Signal.register false bufSelNext,
      Signal.register false n3Next,
      Signal.register false n4Next,
      Signal.register false doneNext
    ]

def neckController {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    : Signal dom (BitVec 4 × BitVec 3 × Bool) :=
  let loopState := Signal.loop fun state => neckControllerBody subOpDone start state
  let phaseOut  := projN! loopState 6 0
  let pathOut   := projN! loopState 6 1
  let doneOut   := projN! loopState 6 5
  bundle2 phaseOut (bundle2 pathOut doneOut)

def neckControllerSimulate {dom : DomainConfig}
    (subOpDone : Signal dom Bool) (start : Signal dom Bool)
    : IO (Signal dom (BitVec 4 × BitVec 3 × Bool)) := do
  let loopState ← Signal.loopMemo (neckControllerBody subOpDone start)
  let phaseOut  := projN! loopState 6 0
  let pathOut   := projN! loopState 6 1
  let doneOut   := projN! loopState 6 5
  return bundle3 phaseOut pathOut doneOut

#synthesizeVerilog neckController

end Sparkle.Examples.YOLOv8.Neck
