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
    Result is 32-bit (we keep lower 32 bits of the 48-bit product
    since scale is typically small). -/
def mulAccScale (acc : Signal dom (BitVec 32)) (scale : Signal dom (BitVec 16))
    : Signal dom (BitVec 32) :=
  -- Sign-extend scale to 32 bits, then multiply
  let scaleExt := scale.map (BitVec.signExtend 32 ·)
  (· * ·) <$> acc <*> scaleExt

/-- Arithmetic shift right by a 5-bit shift amount.
    Uses the `ashr` helper from Signal.lean. -/
def shiftRight32 (val : Signal dom (BitVec 32)) (shift : Signal dom (BitVec 5))
    : Signal dom (BitVec 32) :=
  let shiftExt := shift.map (fun s => BitVec.ofNat 32 s.toNat)
  (ashr · ·) <$> val <*> shiftExt

/-- Clamp a 32-bit signed value to INT8 range [-128, 127].
    Uses Signal.mux cascade (no if-then-else). -/
def clampToInt8 (val : Signal dom (BitVec 32)) : Signal dom (BitVec 8) :=
  -- Check overflow: val > 127
  let isOverflow := (fun x => decide (x.toInt > 127)) <$> val
  -- Check underflow: val < -128
  let isUnderflow := (fun x => decide (x.toInt < -128)) <$> val
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

-- Note: `decide` and `ashr` patterns not yet supported by synthesizer.
-- #synthesizeVerilog requantize

end Sparkle.Examples.YOLOv8.Primitives.Requantize
