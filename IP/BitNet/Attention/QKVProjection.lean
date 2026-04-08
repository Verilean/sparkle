/-
  BitNet Attention — QKV Projection — Signal DSL

  Computes Q, K, V projections using ternary BitLinear rows:
    For each output row j:
      acc = BitLinear(x, weights[j])
      scaled = ScaleMultiply(acc, scale[j])
      quantized = QuantizeInt8(scaled, quantShift)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Attention.Quantize

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear

variable {dom : DomainConfig}

/-- Project one row: BitLinear → Scale → Quantize.
    Returns an INT8 output signal. -/
def projectRowSignal (rowWeights : Array Int) (scaleVal : Int) (quantShift : Nat)
    (activations : Array (Signal dom (BitVec 32)))
    : Signal dom (BitVec 8) :=
  -- MAC + adder tree
  let acc := bitLinearSignal rowWeights activations
  -- Sign-extend to 48 bits for scale multiply
  let acc48 := signExtendSignal 16 acc
  -- Scale multiply: (acc × scale) >>> 24
  let scaled := scaleMultiplySignal acc48 (Signal.pure (BitVec.ofInt 32 scaleVal))
  -- Quantize to INT8
  quantizeInt8Signal quantShift scaled

/-- Generate QKV projections for one attention head.
    Returns (Q, K, V) arrays of INT8 signals. -/
def qkvProjectionSignal
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (quantShift : Nat)
    (activations : Array (Signal dom (BitVec 32)))
    : Array (Signal dom (BitVec 8)) × Array (Signal dom (BitVec 8)) × Array (Signal dom (BitVec 8)) :=
  let project (weights : Array (Array Int)) (scales : Array Int) :=
    Id.run do
      let mut results : Array (Signal dom (BitVec 8)) := #[]
      for j in [:weights.size] do
        let scaleVal := if j < scales.size then scales[j]! else (2 ^ scaleFracBits : Nat)
        results := results.push (projectRowSignal weights[j]! scaleVal quantShift activations)
      return results
  (project qWeights qScales, project kWeights kScales, project vWeights vScales)

end Sparkle.IP.BitNet.Attention
