/-
  Activation Functions — Signal DSL

  - ReLU: max(0, x) for INT8
  - SiLU: x * sigmoid(x) via ROM-based lookup table
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types
import Examples.BitNet.SignalHelpers

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Sparkle.Examples.YOLOv8.Primitives.Activation

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

-- ============================================================================
-- ReLU
-- ============================================================================

/-- ReLU activation for INT8: max(0, x).
    Synthesizable: checks MSB (sign bit) via extractLsb'. -/
def relu {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let msb := x.map (BitVec.extractLsb' 7 1 ·)
  let isNeg := msb === 1#1
  Signal.mux isNeg (Signal.pure 0#8) x

#synthesizeVerilog relu

-- ============================================================================
-- SiLU (Swish) via ROM Lookup Table
-- ============================================================================

/-- Precomputed sigmoid lookup table for INT8 inputs.
    sigmoid_lut[i] = round(sigmoid(i - 128) * 128) as unsigned 8-bit.
    Input is treated as signed INT8 (-128..127), output is Q0.7 (0..128).

    sigmoid(x) = 1 / (1 + exp(-x/16))  (scaled for INT8 range)
    256 entries covering the full INT8 range.

    Generated with: for i in 0..255: sigmoid(signed(i)/16) * 128, rounded & clamped to [0,128] -/
private def sigmoidLut : Array (BitVec 8) :=
  #[ 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 83, 85, 87, 89, 90, 92,
     94, 95, 97, 98, 99, 101, 102, 103, 105, 106, 107, 108, 109, 110, 111, 112,
     113, 114, 114, 115, 116, 116, 117, 118, 118, 119, 119, 120, 120, 121, 121, 122,
     122, 122, 123, 123, 123, 124, 124, 124, 124, 124, 125, 125, 125, 125, 125, 126,
     126, 126, 126, 126, 126, 126, 126, 127, 127, 127, 127, 127, 127, 127, 127, 127,
     127, 127, 127, 127, 127, 127, 127, 127, 127, 128, 128, 128, 128, 128, 128, 128,
     128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
     128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2,
     2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 6,
     6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 12, 12, 13, 14, 14,
     15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 29, 30, 31, 33,
     34, 36, 38, 39, 41, 43, 45, 46, 48, 50, 52, 54, 56, 58, 60, 62 ]

/-- SiLU activation using mux-tree lookup table.
    silu(x) = x * sigmoid(x)
    sigmoid is read from a 256-entry LUT indexed by unsigned interpretation of x.

    Result is (x_signed * sigmoid_unsigned) >> 7, clamped to INT8. -/
def siluLut {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  -- Lookup sigmoid(x) from LUT using mux tree
  let sigVal := lutMuxTree sigmoidLut x
  -- Multiply: x_int8 (signed) * sigmoid_u8 (unsigned Q0.7)
  -- Sign-extend x to 16 bits (synthesizable MSB check)
  let xMsb := x.map (BitVec.extractLsb' 7 1 ·)
  let xIsNeg := xMsb === 1#1
  let xPadOnes := 255#8 ++ x
  let xPadZeros := 0#8 ++ x
  let xExt := Signal.mux xIsNeg xPadOnes xPadZeros
  -- Zero-extend sigmoid to 16 bits
  let sigExt := 0#8 ++ sigVal
  -- Multiply (16-bit signed × 16-bit unsigned = 16-bit result sufficient for INT8)
  let product := xExt * sigExt
  -- Arithmetic shift right by 7 (Q0.7 scaling), then truncate to 8 bits
  let shifted := (ashr · ·) <$> product <*> Signal.pure 7#16
  shifted.map (BitVec.extractLsb' 0 8 ·)

end Sparkle.Examples.YOLOv8.Primitives.Activation
