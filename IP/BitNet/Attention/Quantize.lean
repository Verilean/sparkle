/-
  BitNet Attention — INT8 Quantization — Signal DSL

  Combinational Q16.16 → INT8 quantizer with saturation.
  Arithmetic shift right by `quantShift`, then clamp to [-128, 127].
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Combinational INT8 quantization from Q16.16 activation.

    1. Arithmetic shift right by `quantShift`
    2. Check if shifted value fits in INT8 (bits [31:8] all match bit 7)
    3. Saturate to [-128, 127] if overflow -/
def quantizeInt8Signal (quantShiftBV : BitVec 32) (x : Signal dom (BitVec 32))
    : Signal dom (BitVec 8) :=
  -- Arithmetic shift right by quantShift
  let shifted := Signal.ashrC x quantShiftBV
  -- Overall sign bit (bit 31) for saturation direction
  let overallSign := shifted.map (BitVec.extractLsb' 31 1 ·)
  -- Upper 24 bits [31:8]
  let upper := shifted.map (BitVec.extractLsb' 8 24 ·)
  -- INT8 sign bit (bit 7)
  let int8Sign := shifted.map (BitVec.extractLsb' 7 1 ·)
  -- Expected upper bits: all copies of bit 7
  let isSignSet := int8Sign === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let allOnes : Signal dom (BitVec 24) := (Signal.pure 0xFFFFFF#24 : Signal dom (BitVec 24))
  let allZeros : Signal dom (BitVec 24) := (Signal.pure 0#24 : Signal dom (BitVec 24))
  let expected := Signal.mux isSignSet allOnes allZeros
  -- No overflow if upper bits match expected sign extension
  let noOverflow := upper === expected
  -- Lower 8 bits (direct result when no overflow)
  let lower8 := shifted.map (BitVec.extractLsb' 0 8 ·)
  -- Saturate: negative overflow → 0x80 (-128), positive overflow → 0x7F (127)
  let isNegSign := overallSign === (Signal.pure 1#1 : Signal dom (BitVec 1))
  Signal.mux noOverflow lower8
    (Signal.mux isNegSign (Signal.pure 0x80#8) (Signal.pure 0x7F#8))

end Sparkle.IP.BitNet.Attention
