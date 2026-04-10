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
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Core
import IP.BitNet.BitLinear.Dynamic
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.FFN

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Layers

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
  let defaultScale : LayerScales :=
    { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 }
  -- Chain layers via foldl over the layer indices
  (List.range cfg.nLayers).toArray.foldl (init := x) fun current i =>
    let lw := layerWeights.getD i { gateWeights := #[], upWeights := #[], downWeights := #[] }
    let ls := layerScales.getD i defaultScale
    let activations := Array.replicate cfg.dim current
    ffnBlockSignal lw.gateWeights lw.upWeights lw.downWeights
      ls.gateScale ls.upScale ls.downScale activations

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

end Sparkle.IP.BitNet.SoC
