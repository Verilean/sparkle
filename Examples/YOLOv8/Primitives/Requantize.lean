/-
  Requantization — Signal DSL

  Converts INT32 accumulator → INT8 activation using multiply-and-shift.
  output = clamp((acc * scale) >> shift, -128, 127)
  No runtime division required.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Sparkle.Examples.YOLOv8.Primitives.Requantize

open Sparkle.Core.Domain
open Sparkle.Core.Signal

variable {dom : DomainConfig}

/-- Multiply accumulator by scale factor.
    Synthesizable: sign-extends scale via MSB check + concat. -/
def mulAccScale (acc : Signal dom (BitVec 32)) (scale : Signal dom (BitVec 16))
    : Signal dom (BitVec 32) :=
  -- Sign-extend scale to 32 bits
  let sMsb := scale.map (BitVec.extractLsb' 15 1 ·)
  let sIsNeg := sMsb === 1#1
  let sPadOnes := (· ++ ·) <$> Signal.pure (BitVec.ofNat 16 0xFFFF) <*> scale
  let sPadZeros := (· ++ ·) <$> Signal.pure 0#16 <*> scale
  let scaleExt := Signal.mux sIsNeg sPadOnes sPadZeros
  acc * scaleExt

/-- Arithmetic shift right by a 5-bit shift amount.
    Synthesizable: zero-extends shift to 32-bit, uses ashr. -/
def shiftRight32 (val : Signal dom (BitVec 32)) (shift : Signal dom (BitVec 5))
    : Signal dom (BitVec 32) :=
  -- Zero-extend shift amount to 32 bits (shift is unsigned)
  let shiftExt := (· ++ ·) <$> Signal.pure 0#27 <*> shift
  Signal.ashr val shiftExt

/-- Clamp a 32-bit signed value to INT8 range [-128, 127].
    Synthesizable: uses BitVec.slt for signed comparison. -/
def clampToInt8 (val : Signal dom (BitVec 32)) : Signal dom (BitVec 8) :=
  -- Check overflow: val > 127  ⟺  ¬(val ≤ 127)  ⟺  ¬(val < 128)
  -- Using slt: 127 < val  ⟺  val > 127
  let isOverflow := Signal.slt (Signal.pure (BitVec.ofNat 32 127)) val
  -- Check underflow: val < -128
  let isUnderflow := Signal.slt val (Signal.pure (BitVec.ofInt 32 (-128)))
  -- Truncate to 8 bits (for normal case)
  let truncated := val.map (BitVec.extractLsb' 0 8 ·)
  -- Mux cascade: overflow → 127, underflow → -128, else → truncated
  Signal.mux isOverflow (Signal.pure 127#8)
    (Signal.mux isUnderflow (Signal.pure (BitVec.ofInt 8 (-128)))
      truncated)

/-- Full requantize pipeline: acc × scale >> shift → clamped INT8.
    This is the fundamental operation after each convolution layer. -/
def requantize {dom : DomainConfig}
    (acc : Signal dom (BitVec 32))
    (scale : Signal dom (BitVec 16))
    (shift : Signal dom (BitVec 5))
    : Signal dom (BitVec 8) :=
  let product := mulAccScale acc scale
  let shifted := shiftRight32 product shift
  clampToInt8 shifted

#synthesizeVerilog requantize

end Sparkle.Examples.YOLOv8.Primitives.Requantize
