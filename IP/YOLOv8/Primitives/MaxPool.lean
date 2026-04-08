/-
  Max Pooling 2x2 — Signal DSL

  Computes 2x2 max pooling with stride 2 on INT8 activations.
  Uses a 1-line buffer and signed comparison.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.YOLOv8.Types
import IP.BitNet.SignalHelpers

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Sparkle.IP.YOLOv8.Primitives.MaxPool

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Signed max of two INT8 signals.
    Uses Signal.mux with signed less-than (BitVec.slt). -/
def maxInt8Signal (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  -- a > b ⟺ b < a (signed)
  let bLtA := Signal.slt b a
  Signal.mux bLtA a b

/-- Signed max of four INT8 signals (2x2 window).
    Binary reduction tree: max(max(a,b), max(c,d)). -/
def max4Int8 (a b c d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let maxAB := maxInt8Signal a b
  let maxCD := maxInt8Signal c d
  maxInt8Signal maxAB maxCD

/-- Top-level 2x2 max pooling: takes 4 inputs, outputs the signed max.
    In the full pipeline, a controller FSM feeds the correct 4 pixels
    from the line buffer. -/
def maxPool2x2 {dom : DomainConfig}
    (a : Signal dom (BitVec 8))
    (b : Signal dom (BitVec 8))
    (c : Signal dom (BitVec 8))
    (d : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  max4Int8 a b c d

#synthesizeVerilog maxPool2x2

end Sparkle.IP.YOLOv8.Primitives.MaxPool
