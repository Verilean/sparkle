/-
  YOLOv8n-WorldV2 Top Level — Signal DSL

  Full inference SoC that sequences:
    1. Input loading (160x160x3 RGB → INT8)
    2. Backbone (5 stages → P3, P4, P5)
    3. Neck (FPN + PAN → N3, N4', N5')
    4. Head (detection at 3 scales + text embedding dot product)
    5. Output (bounding boxes + class scores)

  Uses Signal.loopMemo for simulation (follows RV32 SoC pattern).
  All convolutions share a single Conv2DEngine instance.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Config
import Examples.YOLOv8.Types
import Examples.YOLOv8.Primitives.Conv2DEngine
import Examples.YOLOv8.Primitives.MaxPool
import Examples.YOLOv8.Primitives.Upsample
import Examples.YOLOv8.Backbone
import Examples.YOLOv8.Neck
import Examples.YOLOv8.Head
import Examples.YOLOv8.TextEmbedding

set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Sparkle.Examples.YOLOv8.Top

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8

/-- Top-level inference pipeline controller.

    Master FSM that sequences backbone → neck → head.
    Delegates to sub-controllers and shared compute engines.

    State registers (10 total):
      0: fsmState    (BitVec 4)  — top-level phase
      1: cycleCount  (BitVec 32) — total cycle counter
      2: pixelCount  (BitVec 16) — input pixel counter
      3: layerIdx    (BitVec 8)  — overall layer index
      4: bufferSel   (Bool)      — activation buffer ping-pong
      5: backboneDone (Bool)     — backbone complete flag
      6: neckDone    (Bool)      — neck complete flag
      7: headDone    (Bool)      — head complete flag
      8: outputReady (Bool)      — final output ready
      9: errorFlag   (Bool)      — error indicator

    FSM states:
      0: IDLE
      1: LOAD_INPUT   — streaming input pixels into buffer
      2: BACKBONE     — running backbone
      3: NECK         — running neck
      4: HEAD         — running detection head
      5: OUTPUT       — output results
      6: DONE

    Inputs:
      - pixelIn:    INT8 input pixel
      - pixelValid: input pixel valid strobe
      - startInfer: begin inference

    Outputs:
      - phase:      current top-level phase
      - cycleCount: total cycles elapsed
      - done:       inference complete
      - outputReady: results available
-/
def yolov8nTop {dom : DomainConfig}
    (pixelIn : Signal dom (BitVec 8))
    (pixelValid : Signal dom Bool)
    (startInfer : Signal dom Bool)
    : Signal dom (BitVec 4 × BitVec 32 × Bool × Bool) :=
  let loopState := Signal.loop fun state =>
    let fsmReg       := projN! state 10 0   -- BitVec 4
    let cycleReg     := projN! state 10 1   -- BitVec 32
    let pixelCntReg  := projN! state 10 2   -- BitVec 16
    let layerReg     := projN! state 10 3   -- BitVec 8
    let bufSelReg    := projN! state 10 4   -- Bool
    let bbDoneReg    := projN! state 10 5   -- Bool
    let nkDoneReg    := projN! state 10 6   -- Bool
    let hdDoneReg    := projN! state 10 7   -- Bool
    let outReadyReg  := projN! state 10 8   -- Bool
    let errorReg     := projN! state 10 9   -- Bool

    let isIdle      := fsmReg === 0#4
    let isLoadInput := fsmReg === 1#4
    let isBackbone  := fsmReg === 2#4
    let isNeck      := fsmReg === 3#4
    let isHead      := fsmReg === 4#4
    let isOutput    := fsmReg === 5#4
    let isDone      := fsmReg === 6#4

    let startAndIdle := startInfer &&& isIdle

    -- Total pixels: 160 * 160 * 3 = 76800
    let totalPixels := Signal.pure 76800#16
    let allPixelsLoaded := isLoadInput &&& (pixelCntReg === totalPixels)

    -- Pixel counter
    let pixelInc := pixelCntReg + 1#16
    let pixelCounting := isLoadInput &&& pixelValid

    -- Cycle counter (always incrementing when not idle)
    let cycleInc := cycleReg + 1#32

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#4)           -- IDLE → LOAD_INPUT
        (Signal.mux allPixelsLoaded (Signal.pure 2#4)      -- LOAD → BACKBONE
          (Signal.mux (isBackbone &&& bbDoneReg) (Signal.pure 3#4)  -- BB → NECK
            (Signal.mux (isNeck &&& nkDoneReg) (Signal.pure 4#4)    -- NECK → HEAD
              (Signal.mux (isHead &&& hdDoneReg) (Signal.pure 5#4)  -- HEAD → OUTPUT
                (Signal.mux isOutput (Signal.pure 6#4)     -- OUTPUT → DONE
                  (Signal.mux isDone (Signal.pure 0#4)     -- DONE → IDLE
                    fsmReg))))))

    -- Cycle counter
    let cycleNext :=
      Signal.mux startAndIdle (Signal.pure 0#32)
        (Signal.mux isIdle cycleReg
          cycleInc)

    -- Pixel counter
    let pixelCntNext :=
      Signal.mux startAndIdle (Signal.pure 0#16)
        (Signal.mux pixelCounting pixelInc
          pixelCntReg)

    -- Layer index (advanced by sub-controllers)
    let layerNext := layerReg

    -- Buffer select
    let bufSelNext := bufSelReg

    -- Completion flags (set by sub-controllers)
    let bbDoneNext := bbDoneReg
    let nkDoneNext := nkDoneReg
    let hdDoneNext := hdDoneReg

    -- Output ready
    let outReadyNext := isOutput

    -- Error flag
    let errorNext := errorReg

    bundleAll! [
      Signal.register 0#4 fsmNext,
      Signal.register 0#32 cycleNext,
      Signal.register 0#16 pixelCntNext,
      Signal.register 0#8 layerNext,
      Signal.register false bufSelNext,
      Signal.register false bbDoneNext,
      Signal.register false nkDoneNext,
      Signal.register false hdDoneNext,
      Signal.register false outReadyNext,
      Signal.register false errorNext
    ]

  let phaseOut     := projN! loopState 10 0
  let cycleOut     := projN! loopState 10 1
  let outReadyOut  := projN! loopState 10 8
  let doneOut      := (projN! loopState 10 0) === 6#4

  bundle2 phaseOut (bundle2 cycleOut (bundle2 doneOut outReadyOut))

#synthesizeVerilog yolov8nTop

end Sparkle.Examples.YOLOv8.Top
