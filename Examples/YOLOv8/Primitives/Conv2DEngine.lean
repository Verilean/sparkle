/-
  Conv2D MAC Engine — Signal DSL

  Sequential single-MAC engine for convolution.
  Follows the multi-cycle FSM pattern from RV32 Divider.

  FSM states:
    IDLE (0)       → waiting for start
    ACCUMULATE (1) → performing MAC iterations: acc += dequant(w4) * act8
    REQUANTIZE (2) → applying scale and shift
    OUTPUT (3)     → result ready, done=true

  Inputs:
    - weight4:   INT4 weight (from weight ROM)
    - activation8: INT8 activation (from activation buffer)
    - scale:     requantization scale
    - shift:     requantization shift
    - bias:      INT32 bias (pre-folded from BatchNorm)
    - start:     begin new convolution
    - macCount:  number of MAC operations (kernel_h * kernel_w * in_channels)

  Outputs:
    - result:    INT8 requantized output
    - done:      single-cycle pulse when result is valid
    - needWeight: request next weight from ROM
    - needAct:   request next activation from buffer
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types
import Examples.YOLOv8.Primitives.Dequant
import Examples.YOLOv8.Primitives.Requantize

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.Primitives.Conv2DEngine

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8.Primitives.Dequant
open Sparkle.Examples.YOLOv8.Primitives.Requantize

/-- Sequential convolution MAC engine.

    Uses Signal.loop with 5 state registers:
      0: accumulator  (BitVec 32) — running MAC sum
      1: counter      (BitVec 16) — remaining MAC operations
      2: fsmState     (BitVec 2)  — IDLE/ACCUMULATE/REQUANTIZE/OUTPUT
      3: resultReg    (BitVec 8)  — final INT8 output
      4: doneReg      (Bool)      — output valid pulse

    The engine performs `macCount` MAC operations sequentially,
    one per clock cycle. After accumulation, it applies requantization
    (multiply-shift-clamp) and outputs the INT8 result. -/
def conv2DEngine {dom : DomainConfig}
    (weight4 : Signal dom (BitVec 4))
    (activation8 : Signal dom (BitVec 8))
    (scale : Signal dom (BitVec 16))
    (shift : Signal dom (BitVec 5))
    (bias32 : Signal dom (BitVec 32))
    (start : Signal dom Bool)
    (macCount : Signal dom (BitVec 16))
    : Signal dom (BitVec 8 × Bool) :=
  let loopState := Signal.loop fun state =>
    let accReg     := projN! state 5 0  -- BitVec 32
    let counterReg := projN! state 5 1  -- BitVec 16
    let fsmReg     := projN! state 5 2  -- BitVec 2
    let resultReg  := projN! state 5 3  -- BitVec 8
    let doneReg    := projN! state 5 4  -- Bool

    -- FSM state decode
    let isIdle        := (· == ·) <$> fsmReg <*> Signal.pure 0#2
    let isAccumulate  := (· == ·) <$> fsmReg <*> Signal.pure 1#2
    let isRequantize  := (· == ·) <$> fsmReg <*> Signal.pure 2#2
    let isOutput      := (· == ·) <$> fsmReg <*> Signal.pure 3#2

    -- Start condition
    let startAndIdle := (· && ·) <$> start <*> isIdle

    -- MAC: sign-extend weight4 to 8-bit, then both to 32-bit, multiply and accumulate
    let w8 := dequantInt4ToInt8 weight4
    let w32 := extendInt8ToInt32 w8
    let a32 := extendInt8ToInt32 activation8
    let product := (· * ·) <$> w32 <*> a32
    let accPlusProduct := (· + ·) <$> accReg <*> product

    -- Counter decrement
    let counterDec := (· - ·) <$> counterReg <*> Signal.pure 1#16
    let counterIsOne := (· == ·) <$> counterReg <*> Signal.pure 1#16

    -- Accumulate done: transition to REQUANTIZE when counter reaches 1
    let accDone := (· && ·) <$> isAccumulate <*> counterIsOne

    -- Requantize: acc * scale >> shift, clamped to INT8
    let requantResult := requantize accReg scale shift

    -- === State transitions ===

    -- Accumulator next
    let accNext :=
      Signal.mux startAndIdle bias32  -- Initialize with bias
        (Signal.mux isAccumulate accPlusProduct  -- MAC
          accReg)

    -- Counter next
    let counterNext :=
      Signal.mux startAndIdle macCount
        (Signal.mux isAccumulate counterDec
          counterReg)

    -- FSM next
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#2)      -- IDLE → ACCUMULATE
        (Signal.mux accDone (Signal.pure 2#2)         -- ACCUMULATE → REQUANTIZE
          (Signal.mux isRequantize (Signal.pure 3#2)  -- REQUANTIZE → OUTPUT
            (Signal.mux isOutput (Signal.pure 0#2)    -- OUTPUT → IDLE
              fsmReg)))

    -- Result register: latch requantized output
    let resultNext :=
      Signal.mux isRequantize requantResult resultReg

    -- Done pulse: true for exactly 1 cycle in OUTPUT state
    let doneNext := isOutput

    bundleAll! [
      Signal.register 0#32 accNext,
      Signal.register 0#16 counterNext,
      Signal.register 0#2 fsmNext,
      Signal.register 0#8 resultNext,
      Signal.register false doneNext
    ]

  let resultOut := projN! loopState 5 3
  let doneOut := projN! loopState 5 4
  bundle2 resultOut doneOut

#synthesizeVerilog conv2DEngine

end Sparkle.Examples.YOLOv8.Primitives.Conv2DEngine
