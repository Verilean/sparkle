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
import IP.YOLOv8.Types
import IP.YOLOv8.Blocks.ConvBnSiLU

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.YOLOv8.Blocks.Bottleneck

open Sparkle.Core.Domain
open Sparkle.Core.Signal

declare_signal_state BottleneckState
  | fsmReg      : BitVec 2   := 0#2
  | residualReg : BitVec 8   := 0#8
  | resultReg   : BitVec 8   := 0#8
  | doneReg     : Bool        := false

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
    let fsmReg := BottleneckState.fsmReg state
    let residualReg := BottleneckState.residualReg state
    let resultReg := BottleneckState.resultReg state

    let isIdle  := fsmReg === (0#2)
    let isConv1 := fsmReg === (1#2)
    let isConv2 := fsmReg === (2#2)
    let isDone  := fsmReg === (3#2)

    let startAndIdle := start &&& isIdle
    let conv1Done := convDone &&& isConv1
    let conv2Done := convDone &&& isConv2

    -- Residual addition: saturating signed add
    let sumRaw := convResult + residualReg
    let withResidual := Signal.mux addResidual sumRaw convResult

    -- FSM transitions
    let fsmNext := hw_cond fsmReg
      | startAndIdle => (1#2 : Signal dom _)  -- IDLE → CONV1
      | conv1Done    => (2#2 : Signal dom _)  -- CONV1 → CONV2
      | conv2Done    => (3#2 : Signal dom _)  -- CONV2 → DONE
      | isDone       => (0#2 : Signal dom _)  -- DONE → IDLE

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
  bundle2 (BottleneckState.resultReg loopState) (bundle2 (BottleneckState.doneReg loopState) (BottleneckState.fsmReg loopState))

def bottleneckControllerSimulate {dom : DomainConfig}
    (convResult : Signal dom (BitVec 8))
    (convDone : Signal dom Bool)
    (inputVal : Signal dom (BitVec 8))
    (start : Signal dom Bool)
    (addResidual : Signal dom Bool)
    : IO (Signal dom (BitVec 8 × Bool × BitVec 2)) := do
  let loopState ← Signal.loopMemo (bottleneckControllerBody convResult convDone inputVal start addResidual)
  return bundle3 (BottleneckState.resultReg loopState) (BottleneckState.doneReg loopState) (BottleneckState.fsmReg loopState)

#synthesizeVerilog bottleneckController

end Sparkle.IP.YOLOv8.Blocks.Bottleneck
