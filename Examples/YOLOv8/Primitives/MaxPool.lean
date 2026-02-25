/-
  Max Pooling 2x2 — Signal DSL

  Computes 2x2 max pooling with stride 2 on INT8 activations.
  Uses a 1-line buffer and signed comparison.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types
import Examples.BitNet.SignalHelpers

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Sparkle.Examples.YOLOv8.Primitives.MaxPool

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Signed max of two INT8 signals.
    Uses Signal.mux with signed comparison. -/
def maxInt8Signal (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let aGtB := (fun x y => decide (x.toInt > y.toInt)) <$> a <*> b
  Signal.mux aGtB a b

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

-- Note: Signed comparison via `decide` not yet supported by synthesizer.
-- #synthesizeVerilog maxPool2x2

end Sparkle.Examples.YOLOv8.Primitives.MaxPool
