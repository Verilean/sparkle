/-
  BitNet BitLinear Core — Signal DSL

  Pipelined BitLinear layer using Signal DSL.
  Core operations (MAC stage, adder tree) are in SignalHelpers.
  This module provides the top-level BitLinear function.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.BitLinear

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Top-level pipelined BitLinear layer (Signal DSL).
    Applies ternary weights to activations via MAC stage + adder tree.
    Pipeline registers not yet supported (pipelineEvery ignored). -/
def bitLinearPipelinedSignal (weights : Array Int)
    (activations : Array (Signal dom (BitVec n)))
    : Signal dom (BitVec n) :=
  bitLinearSignal weights activations

end Sparkle.IP.BitNet.BitLinear
