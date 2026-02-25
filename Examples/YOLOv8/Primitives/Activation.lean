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
  let isNeg := (· == ·) <$> msb <*> Signal.pure 1#1
  Signal.mux isNeg (Signal.pure 0#8) x

#synthesizeVerilog relu

-- ============================================================================
-- SiLU (Swish) via ROM Lookup Table
-- ============================================================================

/-- Precomputed sigmoid lookup table for INT8 inputs.
    sigmoid_lut[i] = round(sigmoid(i - 128) * 128) as unsigned 8-bit.
    Input is treated as signed INT8 (-128..127), output is Q0.7 (0..128).

    sigmoid(x) = 1 / (1 + exp(-x/16))  (scaled for INT8 range)
    We store 256 entries covering the full INT8 range. -/
private def sigmoidLut : Array (BitVec 8) := Id.run do
  let mut table : Array (BitVec 8) := #[]
  for i in [:256] do
    -- i maps to signed value: i < 128 → i, else i - 256
    let signedVal : Float :=
      if i < 128 then Float.ofNat i
      else Float.ofNat i - 256.0
    -- Scale input: divide by 16 to map INT8 range to reasonable sigmoid input
    let scaledInput := signedVal / 16.0
    -- Compute sigmoid
    let sigmoid := 1.0 / (1.0 + Float.exp (-scaledInput))
    -- Quantize to Q0.7: multiply by 128, round, clamp to [0, 128]
    let quantized := (sigmoid * 128.0 + 0.5).toUInt64.toNat
    let clamped := if quantized > 128 then 128 else quantized
    table := table.push (BitVec.ofNat 8 clamped)
  return table

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
  let xIsNeg := (· == ·) <$> xMsb <*> Signal.pure 1#1
  let xPadOnes := (· ++ ·) <$> Signal.pure 255#8 <*> x
  let xPadZeros := (· ++ ·) <$> Signal.pure 0#8 <*> x
  let xExt := Signal.mux xIsNeg xPadOnes xPadZeros
  -- Zero-extend sigmoid to 16 bits
  let sigExt := (· ++ ·) <$> Signal.pure 0#8 <*> sigVal
  -- Multiply (16-bit signed × 16-bit unsigned = 16-bit result sufficient for INT8)
  let product := (· * ·) <$> xExt <*> sigExt
  -- Arithmetic shift right by 7 (Q0.7 scaling), then truncate to 8 bits
  let shifted := (ashr · ·) <$> product <*> Signal.pure 7#16
  shifted.map (BitVec.extractLsb' 0 8 ·)

end Sparkle.Examples.YOLOv8.Primitives.Activation
