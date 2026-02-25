/-
  YOLOv8n Backbone — Signal DSL

  Controller FSM that sequences through the 5 backbone stages:
    Stage 0: Conv 3x3, 3→16 channels (stem)
    Stage 1: Conv 3x3 s2, 16→32 + C2f(32, n=1)  → P1
    Stage 2: Conv 3x3 s2, 32→64 + C2f(64, n=2)  → P3
    Stage 3: Conv 3x3 s2, 64→128 + C2f(128, n=2) → P4
    Stage 4: Conv 3x3 s2, 128→256 + C2f(256, n=1) + SPPF → P5

  The backbone produces three feature maps (P3, P4, P5) at different scales
  for the FPN+PAN neck.

  All convolutions reuse a shared Conv2DEngine. The FSM manages:
  - Weight ROM address generation
  - Activation buffer ping-pong
  - Layer sequencing
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Config
import Examples.YOLOv8.Types
import Examples.YOLOv8.Blocks.C2f
import Examples.YOLOv8.Blocks.SPPF

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Backbone

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8

/-- Backbone controller FSM.

    Sequences through all backbone layers, managing:
    - Which layer/stage is currently being computed
    - Weight ROM base address for each layer
    - Activation buffer selection (ping-pong)
    - Feature map save points (P3, P4, P5 stored for neck)

    State registers (8 total):
      0: fsmState    (BitVec 4)  — overall pipeline phase
      1: stageIdx    (BitVec 3)  — current backbone stage (0-4)
      2: layerInStage (BitVec 4) — layer within current stage
      3: weightBase  (BitVec 20) — weight ROM base address
      4: bufferSel   (Bool)      — ping-pong buffer select
      5: p3Saved     (Bool)      — P3 feature map saved
      6: p4Saved     (Bool)      — P4 feature map saved
      7: doneFlag    (Bool)      — backbone complete

    FSM states:
      0: IDLE
      1: STEM         — 3x3 conv, 3→16
      2: STAGE_CONV   — downsampling 3x3 conv with stride 2
      3: STAGE_C2F    — C2f block
      4: STAGE_SPPF   — SPPF block (stage 4 only)
      5: SAVE_FEATURE — save feature map for neck
      6: NEXT_STAGE   — advance to next stage
      7: DONE

    Inputs:
      - subOpDone: done signal from current sub-operation
      - start:     begin backbone computation

    Outputs:
      - stageIdx:    current stage (for weight/config lookup)
      - layerInStage: layer within stage
      - weightBase:  weight ROM base address
      - bufferSel:   which buffer to read/write
      - done:        backbone complete
-/
def backboneController {dom : DomainConfig}
    (subOpDone : Signal dom Bool)
    (start : Signal dom Bool)
    : Signal dom (BitVec 4 × BitVec 3 × BitVec 4 × BitVec 20 × Bool × Bool) :=
  let loopState := Signal.loop fun state =>
    let fsmReg      := projN! state 8 0  -- BitVec 4
    let stageReg    := projN! state 8 1  -- BitVec 3
    let layerReg    := projN! state 8 2  -- BitVec 4
    let wBaseReg    := projN! state 8 3  -- BitVec 20
    let bufSelReg   := projN! state 8 4  -- Bool
    let p3SavedReg  := projN! state 8 5  -- Bool
    let p4SavedReg  := projN! state 8 6  -- Bool
    let doneReg     := projN! state 8 7  -- Bool

    let isIdle      := (· == ·) <$> fsmReg <*> Signal.pure 0#4
    let isStem      := (· == ·) <$> fsmReg <*> Signal.pure 1#4
    let isStageConv := (· == ·) <$> fsmReg <*> Signal.pure 2#4
    let isStageC2f  := (· == ·) <$> fsmReg <*> Signal.pure 3#4
    let isStageSppf := (· == ·) <$> fsmReg <*> Signal.pure 4#4
    let isSaveFeat  := (· == ·) <$> fsmReg <*> Signal.pure 5#4
    let isNextStage := (· == ·) <$> fsmReg <*> Signal.pure 6#4
    let isDone      := (· == ·) <$> fsmReg <*> Signal.pure 7#4

    let startAndIdle := (· && ·) <$> start <*> isIdle
    let stemDone     := (· && ·) <$> subOpDone <*> isStem
    let stageConvDone := (· && ·) <$> subOpDone <*> isStageConv
    let stageC2fDone := (· && ·) <$> subOpDone <*> isStageC2f
    let stageSppfDone := (· && ·) <$> subOpDone <*> isStageSppf

    -- Check if current stage needs SPPF (stage 4 only)
    let isStage4 := (· == ·) <$> stageReg <*> Signal.pure 4#3
    -- Check if current stage needs feature save (stages 2, 3, 4)
    -- s >= 2 ⟺ ¬(s == 0 || s == 1)
    let sIs0 := (· == ·) <$> stageReg <*> Signal.pure 0#3
    let sIs1 := (· == ·) <$> stageReg <*> Signal.pure 1#3
    let sLt2 := (· || ·) <$> sIs0 <*> sIs1
    let needsSave := (fun x => !x) <$> sLt2

    -- Check if all stages complete (stage >= 5 means done)
    let stageInc := (· + ·) <$> stageReg <*> Signal.pure 1#3
    let allStagesDone := (· == ·) <$> stageReg <*> Signal.pure 4#3

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#4)          -- IDLE → STEM
        (Signal.mux stemDone (Signal.pure 2#4)            -- STEM → STAGE_CONV
          (Signal.mux stageConvDone (Signal.pure 3#4)     -- STAGE_CONV → STAGE_C2F
            (Signal.mux stageC2fDone
              (Signal.mux isStage4
                (Signal.pure 4#4)                          -- C2F → SPPF (stage 4)
                (Signal.mux needsSave
                  (Signal.pure 5#4)                        -- C2F → SAVE_FEATURE
                  (Signal.pure 6#4)))                      -- C2F → NEXT_STAGE
              (Signal.mux stageSppfDone (Signal.pure 5#4)  -- SPPF → SAVE_FEATURE
                (Signal.mux isSaveFeat (Signal.pure 6#4)   -- SAVE → NEXT_STAGE
                  (Signal.mux isNextStage
                    (Signal.mux allStagesDone
                      (Signal.pure 7#4)                    -- last stage → DONE
                      (Signal.pure 2#4))                   -- NEXT → STAGE_CONV
                    (Signal.mux isDone (Signal.pure 0#4)   -- DONE → IDLE
                      fsmReg)))))))

    -- Stage index
    let stageNext :=
      Signal.mux startAndIdle (Signal.pure 1#3)  -- Start at stage 1 (stage 0 is stem)
        (Signal.mux isNextStage stageInc
          stageReg)

    -- Layer within stage (reset per stage)
    let layerNext :=
      Signal.mux isNextStage (Signal.pure 0#4)
        (Signal.mux startAndIdle (Signal.pure 0#4)
          layerReg)

    -- Weight base address (incremented after each conv completes)
    let wBaseNext := wBaseReg  -- Managed by weight address generator

    -- Buffer select: toggle after each layer
    let bufSelNext :=
      Signal.mux (Signal.mux stemDone (Signal.pure true) (Signal.mux stageConvDone (Signal.pure true) (Signal.pure false)))
        ((fun b => !b) <$> bufSelReg)
        bufSelReg

    -- Feature map save flags
    let isStage2 := (· == ·) <$> stageReg <*> Signal.pure 2#3
    let isStage3 := (· == ·) <$> stageReg <*> Signal.pure 3#3
    let p3SavedNext := Signal.mux ((· && ·) <$> isSaveFeat <*> isStage2) (Signal.pure true) p3SavedReg
    let p4SavedNext := Signal.mux ((· && ·) <$> isSaveFeat <*> isStage3) (Signal.pure true) p4SavedReg

    let doneNext := isDone

    bundleAll! [
      Signal.register 0#4 fsmNext,
      Signal.register 0#3 stageNext,
      Signal.register 0#4 layerNext,
      Signal.register 0#20 wBaseNext,
      Signal.register false bufSelNext,
      Signal.register false p3SavedNext,
      Signal.register false p4SavedNext,
      Signal.register false doneNext
    ]

  let fsmOut     := projN! loopState 8 0
  let stageOut   := projN! loopState 8 1
  let layerOut   := projN! loopState 8 2
  let wBaseOut   := projN! loopState 8 3
  let bufSelOut  := projN! loopState 8 4
  let doneOut    := projN! loopState 8 7

  bundle2 fsmOut (bundle2 stageOut (bundle2 layerOut (bundle2 wBaseOut (bundle2 bufSelOut doneOut))))

#synthesizeVerilog backboneController

end Sparkle.Examples.YOLOv8.Backbone
