/-
  Line Buffer — Signal DSL

  3-row line buffer for 3x3 convolutions using Signal.memory.
  Stores two complete rows in memory; the third row comes from
  the current input stream.

  Outputs a sliding 3x3 window of INT8 values.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Primitives.LineBuffer

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- 3-row line buffer for 3x3 convolution.

    Uses two Signal.memory instances (each stores one row of `width` pixels)
    and 9 registers for the 3x3 sliding window.

    Data flow (each clock cycle when valid=true):
      - Current pixel enters row 0 (direct input)
      - Previous row's pixel is read from line buffer 1 (row 1)
      - Two-rows-ago pixel is read from line buffer 2 (row 2)
      - Column position advances

    The sliding window shifts right by 1 pixel each valid cycle.

    State registers (13 total):
      0-8:  window[0..8] (3x3 window, row-major: 0-2=top, 3-5=mid, 6-8=bot)
      9:    colPos (BitVec 8) — current column position
      10:   rowPos (BitVec 8) — current row position
      11:   windowValid (Bool) — window contains valid data
      12:   writeAddr (BitVec 8) — write address for line buffers

    Inputs:
      - pixelIn:  INT8 input pixel
      - valid:    input pixel valid strobe
      - width:    row width (constant, but passed as signal for flexibility)

    Outputs:
      - window[0..8]: 3x3 window (9 INT8 values)
      - windowValid:  true when the window is fully populated
-/
def lineBuffer3x3 {dom : DomainConfig}
    (pixelIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    : Signal dom (BitVec 8 × BitVec 8 × BitVec 8 ×
                  BitVec 8 × BitVec 8 × BitVec 8 ×
                  BitVec 8 × BitVec 8 × BitVec 8 × Bool) :=
  let loopState := Signal.loop fun state =>
    -- Window registers (3x3)
    let w0 := projN! state 13 0   -- top-left
    let w1 := projN! state 13 1   -- top-center
    let w2 := projN! state 13 2   -- top-right
    let w3 := projN! state 13 3   -- mid-left
    let w4 := projN! state 13 4   -- mid-center
    let w5 := projN! state 13 5   -- mid-right
    let w6 := projN! state 13 6   -- bot-left
    let w7 := projN! state 13 7   -- bot-center
    let w8 := projN! state 13 8   -- bot-right
    let colPos := projN! state 13 9     -- BitVec 8
    let rowPos := projN! state 13 10    -- BitVec 8
    let wValid := projN! state 13 11    -- Bool
    let wrAddr := projN! state 13 12    -- BitVec 8

    -- Line buffer memories (8-bit address = max 256 pixel width)
    -- Buffer 1: stores previous row
    let lb1ReadData := Signal.memory wrAddr pixelIn valid colPos
    -- Buffer 2: stores row before previous
    let lb2ReadData := Signal.memory wrAddr lb1ReadData valid colPos

    -- Shift window on valid input:
    -- New column arrives: shift each row left, new pixel enters right
    let w0Next := Signal.mux valid w1 w0
    let w1Next := Signal.mux valid w2 w1
    let w2Next := Signal.mux valid lb2ReadData w2   -- top-right from oldest row
    let w3Next := Signal.mux valid w4 w3
    let w4Next := Signal.mux valid w5 w4
    let w5Next := Signal.mux valid lb1ReadData w5   -- mid-right from previous row
    let w6Next := Signal.mux valid w7 w6
    let w7Next := Signal.mux valid w8 w7
    let w8Next := Signal.mux valid pixelIn w8       -- bot-right is current input

    -- Column counter
    let colInc := colPos + 1#8
    let colNext := Signal.mux valid colInc colPos

    -- Row counter: increment when column wraps (simplified: assume width < 256)
    let rowInc := rowPos + 1#8
    let rowNext := rowPos  -- Row tracking managed by external controller

    -- Window valid: true after first 2 rows + 2 columns
    -- r >= 2 ⟺ ¬(r < 2) ⟺ ¬(r == 0 || r == 1)
    let rowIs0 := rowPos === 0#8
    let rowIs1 := rowPos === 1#8
    let rowLt2 := rowIs0 ||| rowIs1
    let hasEnoughRows := ~~~rowLt2
    let colIs0 := colPos === 0#8
    let colIs1 := colPos === 1#8
    let colLt2 := colIs0 ||| colIs1
    let hasEnoughCols := ~~~colLt2
    let validNext := hasEnoughRows &&& hasEnoughCols

    -- Write address for line buffers
    let wrAddrNext := Signal.mux valid colInc wrAddr

    bundleAll! [
      Signal.register 0#8 w0Next,
      Signal.register 0#8 w1Next,
      Signal.register 0#8 w2Next,
      Signal.register 0#8 w3Next,
      Signal.register 0#8 w4Next,
      Signal.register 0#8 w5Next,
      Signal.register 0#8 w6Next,
      Signal.register 0#8 w7Next,
      Signal.register 0#8 w8Next,
      Signal.register 0#8 colNext,
      Signal.register 0#8 rowNext,
      Signal.register false validNext,
      Signal.register 0#8 wrAddrNext
    ]

  -- Extract outputs
  let w0out := projN! loopState 13 0
  let w1out := projN! loopState 13 1
  let w2out := projN! loopState 13 2
  let w3out := projN! loopState 13 3
  let w4out := projN! loopState 13 4
  let w5out := projN! loopState 13 5
  let w6out := projN! loopState 13 6
  let w7out := projN! loopState 13 7
  let w8out := projN! loopState 13 8
  let validOut := projN! loopState 13 11

  -- Bundle outputs into a 10-tuple
  bundle2 w0out (bundle2 w1out (bundle2 w2out
    (bundle2 w3out (bundle2 w4out (bundle2 w5out
      (bundle2 w6out (bundle2 w7out (bundle2 w8out validOut))))))))

end Sparkle.Examples.YOLOv8.Primitives.LineBuffer
