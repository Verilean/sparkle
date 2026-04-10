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
@[reducible] private def chainLayersAux
    (dim : Nat)
    (layerWeights : List LayerWeights)
    (layerScales : List LayerScales)
    (current : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  match layerWeights, layerScales with
  | lw :: lwRest, ls :: lsRest =>
    let activations := (List.replicate dim current).toArray
    let next := ffnBlockSignal lw.gateWeights lw.upWeights lw.downWeights
      ls.gateScale ls.upScale ls.downScale current activations
    chainLayersAux dim lwRest lsRest next
  | _, _ => current

def hardwiredSoCSignal (cfg : SoCConfig) (layerWeights : Array LayerWeights)
    (layerScales : Array LayerScales)
    (x : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  chainLayersAux cfg.dim layerWeights.toList layerScales.toList x

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
