/-
  BitNet BitLinear — Pipelined Scale Multiply — Signal DSL

  Same as Scale.lean but with a pipeline register after the multiply.
  Breaks the critical path for 200 MHz operation.

  Latency: 1 cycle (vs 0 for combinational version).
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.BitLinear

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Pipelined fixed-point scale: (acc48 × scale32) >>> 24, result in 32 bits.
    Pipeline register after multiply — adds 1 cycle latency but
    allows 200 MHz+ by isolating the multiplier from downstream logic. -/
def scaleMultiplyPipelined (acc : Signal dom (BitVec 48)) (scale : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let accExt : Signal dom (BitVec (32 + 48)) := signExtendSignal 32 acc
  let scaleExt : Signal dom (BitVec (48 + 32)) := signExtendSignal 48 scale
  let prod : Signal dom (BitVec 80) := accExt * scaleExt
  -- Pipeline register after multiply
  let prodReg : Signal dom (BitVec 80) := Signal.register 0 prod
  Signal.map (BitVec.extractLsb' 24 32 ·) prodReg

end Sparkle.IP.BitNet.BitLinear
