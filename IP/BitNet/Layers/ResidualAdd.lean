/-
  BitNet Layers — Saturating Residual Addition — Signal DSL

  Signed 32-bit addition with overflow detection and saturation.
  Uses 33-bit intermediate to detect overflow via top 2 bits.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Saturating signed 32-bit addition using Signal DSL.
    Sign-extend to 33 bits, add, check top 2 bits for overflow,
    saturate to [−2³¹, 2³¹−1]. -/
def residualAddSignal (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  -- Sign-extend both to 33 bits
  let aExt := signExtendSignal 1 a
  let bExt := signExtendSignal 1 b
  -- Add in 33-bit domain
  let sum := aExt + bExt
  -- Extract top 2 bits [32:31]
  let top2 := sum.map (BitVec.extractLsb' 31 2 ·)
  -- Extract lower 32 bits
  let low32 := sum.map (BitVec.extractLsb' 0 32 ·)
  -- Positive overflow: top2 == 0b01
  let posOvf := top2 === 0b01#2
  -- Negative overflow: top2 == 0b10
  let negOvf := top2 === 0b10#2
  -- Mux chain: negOvf → INT32_MIN, posOvf → INT32_MAX, else → low32
  Signal.mux negOvf (Signal.pure 0x80000000#32)
    (Signal.mux posOvf (Signal.pure 0x7FFFFFFF#32) low32)

end Sparkle.IP.BitNet.Layers
