/-
  Nearest-Neighbor Upsample 2x — Signal DSL

  Duplicates each pixel horizontally and each row vertically
  to produce 2x resolution output. Uses FSM with counters.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Primitives.Upsample

open Sparkle.Core.Domain
open Sparkle.Core.Signal

variable {dom : DomainConfig}

private abbrev UpsampleState := Bool × BitVec 8 × Bool

private def upsample2xBody {dom : DomainConfig}
    (pixelIn : Signal dom (BitVec 8)) (valid : Signal dom Bool)
    (state : Signal dom UpsampleState) : Signal dom UpsampleState :=
    let phaseReg  := projN! state 3 0  -- Bool: false=first pixel, true=duplicate
    let heldReg   := projN! state 3 1  -- BitVec 8: held pixel value
    let validReg  := projN! state 3 2  -- Bool: output valid

    -- When valid and phase=false: latch input, output it, go to phase=true
    -- When phase=true: output held pixel, go to phase=false
    let validAndNotPhase := valid &&& (~~~phaseReg)

    -- Next held pixel: latch on valid & !phase
    let heldNext := Signal.mux validAndNotPhase pixelIn heldReg

    -- Output pixel: held pixel (works for both phases)
    -- On first phase, we latch and output pixelIn
    -- On second phase, we output the held value
    let pixelOut := Signal.mux validAndNotPhase pixelIn heldReg

    -- Phase toggles: false→true on valid input, true→false always
    let phaseNext := Signal.mux validAndNotPhase (Signal.pure true)
      (Signal.mux phaseReg (Signal.pure false) phaseReg)

    -- Output valid: true when we have data to output
    let outValidNext := validAndNotPhase ||| phaseReg

    bundleAll! [
      Signal.register false phaseNext,
      Signal.register 0#8 heldNext,
      Signal.register false outValidNext
    ]

/-- Nearest-neighbor 2x upsample controller.
    Inputs:
      - pixelIn: incoming pixel value (INT8)
      - valid:   input pixel valid strobe
    Outputs:
      - pixelOut: upsampled pixel (each input pixel appears 2x horizontally)
      - outValid: output valid strobe

    The horizontal duplication is handled by toggling a phase bit.
    Vertical duplication requires reading each row twice (managed by the
    upstream controller).

    State: (phase : Bool × heldPixel : BitVec 8 × outValid : Bool)
    - phase = false: latch new input pixel, output it, set phase = true
    - phase = true:  output held pixel again, set phase = false
-/
def upsample2x {dom : DomainConfig}
    (pixelIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    : Signal dom (BitVec 8 × Bool) :=
  let loopState := Signal.loop fun state => upsample2xBody pixelIn valid state
  let pixelOut := Signal.mux (projN! loopState 3 0)
    (projN! loopState 3 1)
    (projN! loopState 3 1)
  let outValid := projN! loopState 3 2
  bundle2 pixelOut outValid

def upsample2xSimulate {dom : DomainConfig}
    (pixelIn : Signal dom (BitVec 8)) (valid : Signal dom Bool)
    : IO (Signal dom (BitVec 8 × Bool)) := do
  let loopState ← Signal.loopMemo (upsample2xBody pixelIn valid)
  let pixelOut := Signal.mux (projN! loopState 3 0)
    (projN! loopState 3 1)
    (projN! loopState 3 1)
  let outValid := projN! loopState 3 2
  return bundle2 pixelOut outValid

#synthesizeVerilog upsample2x

end Sparkle.Examples.YOLOv8.Primitives.Upsample
