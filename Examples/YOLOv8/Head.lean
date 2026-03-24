/-
  Detection Head — Signal DSL

  Decoupled detection head at 3 scales (N3, N4', N5').
  Each scale has:
    - Bbox regression branch: 2× Conv 3x3 → Conv 1x1 → 4×(reg_max+1) outputs
    - Classification branch: 2× Conv 3x3 → Conv 1x1 → num_classes outputs

  For YOLOv8-WorldV2, classification uses text embedding dot product
  instead of fixed class outputs.

  This module implements the controller FSM for sequencing the
  detection head computation across all three scales.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Config
import Examples.YOLOv8.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Head

open Sparkle.Core.Domain
open Sparkle.Core.Signal

private abbrev HeadState := BitVec 4 × BitVec 2 × Bool × BitVec 2 × Bool × Bool

/-- Detection head controller FSM.

    Processes three feature map scales sequentially.
    For each scale: bbox_branch → cls_branch → text_dot_product

    State registers (6 total):
      0: fsmState    (BitVec 4)  — current phase
      1: scaleIdx    (BitVec 2)  — which scale (0=N3, 1=N4', 2=N5')
      2: branchSel   (Bool)      — false=bbox, true=cls
      3: convInBranch (BitVec 2) — which conv within branch (0,1,2)
      4: dotProdDone (Bool)      — text embedding dot product complete
      5: doneFlag    (Bool)

    FSM states:
      0: IDLE
      1: BBOX_CONV    — conv layers in bbox branch
      2: CLS_CONV     — conv layers in cls branch
      3: TEXT_DOT      — text embedding dot product
      4: NEXT_SCALE   — advance to next scale
      5: DONE

    Inputs:
      - subOpDone: done from current sub-operation
      - start:     begin head computation

    Outputs:
      - phase:   current FSM state
      - scaleIdx: which scale
      - branchSel: which branch
      - done:    head complete
-/
private def headControllerBody {dom : DomainConfig}
    (subOpDone : Signal dom Bool) (start : Signal dom Bool)
    (state : Signal dom HeadState) : Signal dom HeadState :=
    let fsmReg      := projN! state 6 0  -- BitVec 4
    let scaleReg    := projN! state 6 1  -- BitVec 2
    let branchReg   := projN! state 6 2  -- Bool
    let convIdxReg  := projN! state 6 3  -- BitVec 2
    let dotDoneReg  := projN! state 6 4  -- Bool
    let doneReg     := projN! state 6 5  -- Bool

    let isIdle      := fsmReg === 0#4
    let isBboxConv  := fsmReg === 1#4
    let isClsConv   := fsmReg === 2#4
    let isTextDot   := fsmReg === 3#4
    let isNextScale := fsmReg === 4#4
    let isDone      := fsmReg === 5#4

    let startAndIdle := start &&& isIdle

    -- Conv index tracking (3 convs per branch: conv3x3, conv3x3, conv1x1)
    let convIdxInc := convIdxReg + 1#2
    let bboxConvDone := subOpDone &&& isBboxConv
    let allBboxConvs := bboxConvDone &&& (convIdxReg === 2#2)  -- 3 convs: 0,1,2
    let moreBboxConv := bboxConvDone &&& (~~~(convIdxReg === 2#2))

    let clsConvDone := subOpDone &&& isClsConv
    let allClsConvs := clsConvDone &&& (convIdxReg === 2#2)
    let moreClsConv := clsConvDone &&& (~~~(convIdxReg === 2#2))

    let textDotDone := subOpDone &&& isTextDot

    -- Scale tracking
    let scaleInc := scaleReg + 1#2
    let allScales := scaleReg === 2#2  -- 3 scales: 0,1,2

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#4)            -- IDLE → BBOX_CONV
        (Signal.mux moreBboxConv (Signal.pure 1#4)          -- more bbox convs
          (Signal.mux allBboxConvs (Signal.pure 2#4)        -- BBOX done → CLS_CONV
            (Signal.mux moreClsConv (Signal.pure 2#4)       -- more cls convs
              (Signal.mux allClsConvs (Signal.pure 3#4)     -- CLS done → TEXT_DOT
                (Signal.mux textDotDone (Signal.pure 4#4)   -- TEXT_DOT → NEXT_SCALE
                  (Signal.mux isNextScale
                    (Signal.mux allScales
                      (Signal.pure 5#4)                      -- last scale → DONE
                      (Signal.pure 1#4))                     -- next scale → BBOX_CONV
                    (Signal.mux isDone (Signal.pure 0#4)     -- DONE → IDLE
                      fsmReg)))))))

    -- Scale index
    let scaleNext :=
      Signal.mux startAndIdle (Signal.pure 0#2)
        (Signal.mux isNextScale scaleInc
          scaleReg)

    -- Branch select: false for bbox, true for cls
    let branchNext :=
      Signal.mux startAndIdle (Signal.pure false)
        (Signal.mux allBboxConvs (Signal.pure true)
          (Signal.mux isNextScale (Signal.pure false)
            branchReg))

    -- Conv index within branch
    let convIdxNext :=
      Signal.mux startAndIdle (Signal.pure 0#2)
        (Signal.mux moreBboxConv convIdxInc
          (Signal.mux allBboxConvs (Signal.pure 0#2)  -- Reset for cls branch
            (Signal.mux moreClsConv convIdxInc
              (Signal.mux isNextScale (Signal.pure 0#2)
                convIdxReg))))

    let dotDoneNext := textDotDone
    let doneNext := isDone

    bundleAll! [
      Signal.register 0#4 fsmNext,
      Signal.register 0#2 scaleNext,
      Signal.register false branchNext,
      Signal.register 0#2 convIdxNext,
      Signal.register false dotDoneNext,
      Signal.register false doneNext
    ]

def headController {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    : Signal dom (BitVec 4 × BitVec 2 × Bool × Bool) :=
  let loopState := Signal.loop fun state => headControllerBody subOpDone start state
  let phaseOut  := projN! loopState 6 0
  let scaleOut  := projN! loopState 6 1
  let branchOut := projN! loopState 6 2
  let doneOut   := projN! loopState 6 5
  bundle2 phaseOut (bundle2 scaleOut (bundle2 branchOut doneOut))

def headControllerSimulate {dom : DomainConfig}
    (subOpDone : Signal dom Bool) (start : Signal dom Bool)
    : IO (Signal dom (BitVec 4 × BitVec 2 × Bool × Bool)) := do
  let loopState ← Signal.loopMemo (headControllerBody subOpDone start)
  let phaseOut  := projN! loopState 6 0
  let scaleOut  := projN! loopState 6 1
  let branchOut := projN! loopState 6 2
  let doneOut   := projN! loopState 6 5
  return bundle2 phaseOut (bundle2 scaleOut (bundle2 branchOut doneOut))

#synthesizeVerilog headController

end Sparkle.Examples.YOLOv8.Head
