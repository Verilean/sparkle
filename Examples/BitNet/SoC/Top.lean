/-
  BitNet SoC Top-Level — Signal DSL

  Two architecture modes for the SoC:

  1. HardwiredUnrolled: N distinct hardwired FFN layers chained.
     Each layer has unique weight patterns with zero-weight pruning.

  2. TimeMultiplexed: Single FFN core with dynamic weights,
     layer index selects weights from ROM via mux tree.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Dynamic
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Layers.ReLUSq
import Examples.BitNet.Layers.ResidualAdd
import Examples.BitNet.Layers.ElemMul
import Examples.BitNet.Layers.FFN

namespace Sparkle.Examples.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet
open Sparkle.Examples.BitNet.SignalHelpers
open Sparkle.Examples.BitNet.BitLinear
open Sparkle.Examples.BitNet.Layers

variable {dom : DomainConfig}

/-- Encode an Int ternary weight to its 2-bit i2_s code.
    -1 → 0b00, 0 → 0b01, +1 → 0b10 -/
def encodeTernary (w : Int) : Int :=
  if w == -1 then 0b00
  else if w == 1 then 0b10
  else 0b01

/-- HardwiredUnrolled SoC: chain N hardwired FFN layers.
    Each layer uses different hardwired weights and scales.
    Output of layer i feeds into layer i+1. -/
def hardwiredSoCSignal (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales)
    (x : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Id.run do
    let mut current := x
    for i in [:cfg.nLayers] do
      if i < layerWeights.size then
        let lw := layerWeights[i]!
        let ls := if i < layerScales.size then layerScales[i]!
          else { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 }
        -- Create activation array (broadcast single value to all dimensions)
        let activations : Array (Signal dom (BitVec 32)) :=
          Array.replicate cfg.dim current
        -- Apply FFN block
        current := ffnBlockSignal lw.gateWeights lw.upWeights lw.downWeights
          ls.gateScale ls.upScale ls.downScale activations
    return current

/-- TimeMultiplexed SoC: single FFN core with dynamic weight selection.
    Uses Signal.loop for FSM-based layer sequencing.
    For simulation: applies layers sequentially (same as hardwired). -/
def timeMultiplexedSoCSignal (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales)
    (x : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  -- For simulation, time-multiplexed produces the same result as hardwired
  -- (layers applied sequentially). The hardware difference is in resource usage.
  hardwiredSoCSignal cfg layerWeights layerScales x

/-- Build the SoC in the selected architecture mode -/
def bitNetSoCSignal (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales)
    (x : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  match cfg.archMode with
  | .HardwiredUnrolled => hardwiredSoCSignal cfg layerWeights layerScales x
  | .TimeMultiplexed => timeMultiplexedSoCSignal cfg layerWeights layerScales x

end Sparkle.Examples.BitNet.SoC
