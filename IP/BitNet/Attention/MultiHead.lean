/-
  BitNet Attention — Multi-Head Attention — Signal DSL

  Structural composition of multiple attention heads:
    1. Per-head: QKV projection + dot product + softmax + score-V multiply
    2. Concatenate head outputs
    3. Output projection: ternary BitLinear + scale
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Attention.Quantize
import IP.BitNet.Attention.Top

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear

variable {dom : DomainConfig}

/-- Configuration for multi-head attention -/
structure MultiHeadConfig where
  nHeads     : Nat
  headDim    : Nat
  inDim      : Nat
  seqLen     : Nat
  quantShift : Nat := 10
  dkShift    : Nat := 1
  deriving Repr, BEq

def MultiHeadConfig.concatDim (c : MultiHeadConfig) : Nat := c.nHeads * c.headDim

/-- Multi-head attention with output projection.
    Returns array of modelDim output signals (32-bit). -/
def multiHeadAttentionSignal
    (config : MultiHeadConfig)
    (allQWeights allKWeights allVWeights : Array (Array (Array Int)))
    (allQScales allKScales allVScales : Array (Array Int))
    (outProjWeights : Array (Array Int))
    (outProjScales : Array Int)
    (activations : Array (Signal dom (BitVec 32)))
    (allKCache allVCache : Array (Array (Array (Signal dom (BitVec 8)))))
    : Array (Signal dom (BitVec 32)) :=
  -- Per-head computation
  let concatOutputs : Array (Signal dom (BitVec 32)) := Id.run do
    let mut concat : Array (Signal dom (BitVec 32)) := #[]
    for h in [:config.nHeads] do
      let fullCfg : FullAttentionConfig := {
        headDim := config.headDim
        inDim := config.inDim
        quantShift := config.quantShift
        dkShift := config.dkShift
        seqLen := config.seqLen
      }
      let kCache := if h < allKCache.size then allKCache[h]! else #[]
      let vCache := if h < allVCache.size then allVCache[h]! else #[]
      let headOutputs := fullAttentionHeadSignal fullCfg
        allQWeights[h]! allKWeights[h]! allVWeights[h]!
        allQScales[h]! allKScales[h]! allVScales[h]!
        activations kCache vCache
      concat := concat ++ headOutputs
    return concat

  -- Output projection: ternary BitLinear + scale for each output row
  let modelDim := outProjWeights.size
  Id.run do
    let mut outputs : Array (Signal dom (BitVec 32)) := #[]
    for row in [:modelDim] do
      let rowWeights := outProjWeights[row]!
      -- Apply ternary MAC to concatenated head outputs
      let acc := bitLinearSignal rowWeights concatOutputs
      -- Scale
      let acc48 := signExtendSignal 16 acc
      let scaleVal := if row < outProjScales.size then outProjScales[row]!
        else (2 ^ scaleFracBits : Nat)
      let scaled := scaleMultiplySignal acc48 (Signal.pure (BitVec.ofInt 32 scaleVal))
      outputs := outputs.push scaled
    return outputs

end Sparkle.IP.BitNet.Attention
