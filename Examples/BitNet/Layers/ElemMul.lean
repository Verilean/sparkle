/-
  BitNet Layers — Element-wise Multiply — Signal DSL

  Fixed-point Q16.16 element-wise multiplication: (a × b) >>> 16.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers

namespace Sparkle.Examples.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Element-wise multiply in Q16.16: (a × b) >>> 16 using Signal DSL.
    Sign-extend to 64 bits, multiply, extract bits [47:16]. -/
def elemMulSignal (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  -- Sign-extend both to 64 bits
  let aExt := signExtendSignal 32 a
  let bExt := signExtendSignal 32 b
  -- Multiply (64-bit, no overflow for 32-bit signed inputs)
  let prod := aExt * bExt
  -- Extract bits [47:16] = ASR 16 + truncate to 32 bits
  prod.map (BitVec.extractLsb' 16 32 ·)

end Sparkle.Examples.BitNet.Layers
