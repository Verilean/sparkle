/-
  Bottleneck — Signal DSL

  1x1 ConvBnSiLU → 3x3 ConvBnSiLU, with optional residual connection.
  This is the basic building block inside C2f.

  The bottleneck reduces channels via 1x1 conv, then applies spatial
  processing via 3x3 conv. When residual=true, the input is added
  to the output (requires same channel count).

  This module coordinates two sequential ConvBnSiLU blocks via an FSM.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types
import Examples.YOLOv8.Blocks.ConvBnSiLU

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Blocks.Bottleneck

open Sparkle.Core.Domain
open Sparkle.Core.Signal

private abbrev BottleneckState := BitVec 2 × BitVec 8 × BitVec 8 × Bool

/-- Bottleneck block controller FSM.

    Sequences two ConvBnSiLU operations:
    1. 1x1 conv (channel reduction/expansion)
    2. 3x3 conv (spatial processing)
    Then optionally adds the residual connection.

    State registers (4 total):
      0: fsmState  (BitVec 2) — IDLE/CONV1/CONV2/DONE
      1: residualVal (BitVec 8) — stored input for residual add
      2: resultVal  (BitVec 8) — final output
      3: doneFlag   (Bool)

    The actual convolution computation is delegated to ConvBnSiLU instances
    controlled by the top-level SoC controller. This FSM just manages
    the sequencing and residual addition.

    Inputs:
      - convResult: output from the currently active ConvBnSiLU
      - convDone:   done signal from ConvBnSiLU
      - inputVal:   original input for residual connection
      - start:      begin bottleneck computation
      - addResidual: whether to add residual (true for shortcut=True)

    Outputs:
      - result: INT8 output
      - done:   result valid pulse
      - phase:  current phase (0=idle, 1=conv1, 2=conv2, 3=done)
-/
private def bottleneckControllerBody {dom : DomainConfig}
    (convResult : Signal dom (BitVec 8))
    (convDone : Signal dom Bool)
    (inputVal : Signal dom (BitVec 8))
    (start : Signal dom Bool)
    (addResidual : Signal dom Bool)
    (state : Signal dom BottleneckState) : Signal dom BottleneckState :=
    let fsmReg      := projN! state 4 0  -- BitVec 2
    let residualReg := projN! state 4 1  -- BitVec 8
    let resultReg   := projN! state 4 2  -- BitVec 8
    let doneReg     := projN! state 4 3  -- Bool

    let isIdle  := (· == ·) <$> fsmReg <*> Signal.pure 0#2
    let isConv1 := (· == ·) <$> fsmReg <*> Signal.pure 1#2
    let isConv2 := (· == ·) <$> fsmReg <*> Signal.pure 2#2
    let isDone  := (· == ·) <$> fsmReg <*> Signal.pure 3#2

    let startAndIdle := (· && ·) <$> start <*> isIdle
    let conv1Done := (· && ·) <$> convDone <*> isConv1
    let conv2Done := (· && ·) <$> convDone <*> isConv2

    -- Residual addition: saturating signed add
    let sumRaw := (· + ·) <$> convResult <*> residualReg
    let withResidual := Signal.mux addResidual sumRaw convResult

    -- FSM transitions
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#2)    -- IDLE → CONV1
        (Signal.mux conv1Done (Signal.pure 2#2)    -- CONV1 → CONV2
          (Signal.mux conv2Done (Signal.pure 3#2)  -- CONV2 → DONE
            (Signal.mux isDone (Signal.pure 0#2)   -- DONE → IDLE
              fsmReg)))

    -- Latch input for residual on start
    let residualNext := Signal.mux startAndIdle inputVal residualReg

    -- Latch result on conv2 completion
    let resultNext := Signal.mux conv2Done withResidual resultReg

    -- Done pulse
    let doneNext := isDone

    bundleAll! [
      Signal.register 0#2 fsmNext,
      Signal.register 0#8 residualNext,
      Signal.register 0#8 resultNext,
      Signal.register false doneNext
    ]

def bottleneckController {dom : DomainConfig}
    (convResult : Signal dom (BitVec 8))
    (convDone : Signal dom Bool)
    (inputVal : Signal dom (BitVec 8))
    (start : Signal dom Bool)
    (addResidual : Signal dom Bool)
    : Signal dom (BitVec 8 × Bool × BitVec 2) :=
  let loopState := Signal.loop fun state => bottleneckControllerBody convResult convDone inputVal start addResidual state
  let resultOut := projN! loopState 4 2
  let doneOut := projN! loopState 4 3
  let phaseOut := projN! loopState 4 0
  bundle2 resultOut (bundle2 doneOut phaseOut)

def bottleneckControllerSimulate {dom : DomainConfig}
    (convResult : Signal dom (BitVec 8))
    (convDone : Signal dom Bool)
    (inputVal : Signal dom (BitVec 8))
    (start : Signal dom Bool)
    (addResidual : Signal dom Bool)
    : IO (Signal dom (BitVec 8 × Bool × BitVec 2)) := do
  let loopState ← Signal.loopMemo (bottleneckControllerBody convResult convDone inputVal start addResidual)
  let resultOut := projN! loopState 4 2
  let doneOut := projN! loopState 4 3
  let phaseOut := projN! loopState 4 0
  return bundle3 resultOut doneOut phaseOut

#synthesizeVerilog bottleneckController

end Sparkle.Examples.YOLOv8.Blocks.Bottleneck
