/-
  BitNet Attention — Full Attention Pipeline — Signal DSL

  Connects QKV Projection, Dot Product, Softmax, and Score-V Multiply
  into a complete single-head attention pipeline.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Attention.Quantize
import Examples.BitNet.Attention.DotProduct
import Examples.BitNet.Attention.QKVProjection
import Examples.BitNet.Attention.Softmax
import Examples.BitNet.Attention.ScoreVMul

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Configuration for one attention head -/
structure AttentionHeadConfig where
  headDim      : Nat
  inDim        : Nat
  quantShift   : Nat := 10
  dkShift      : Nat := 3
  deriving Repr, BEq

/-- Configuration for a full attention head with KV cache -/
structure FullAttentionConfig extends AttentionHeadConfig where
  seqLen : Nat
  deriving Repr, BEq

/-- Generate a single attention head: QKV projection + Q·K^T dot product.
    Returns (score, V_outputs). -/
def attentionHeadSignal
    (config : AttentionHeadConfig)
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (activations : Array (Signal dom (BitVec 32)))
    : Signal dom (BitVec 32) × Array (Signal dom (BitVec 8)) :=
  let (qs, ks, vs) := qkvProjectionSignal qWeights kWeights vWeights
    qScales kScales vScales config.quantShift activations
  let score := dotProductSignal qs ks config.dkShift
  (score, vs)

/-- Full attention head with softmax and weighted V output.
    Uses pre-filled KV cache for multi-position attention.

    kCache/vCache: [seqLen][headDim] arrays of INT8 signals. -/
def fullAttentionHeadSignal
    (config : FullAttentionConfig)
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (activations : Array (Signal dom (BitVec 32)))
    (kCache : Array (Array (Signal dom (BitVec 8))))
    (vCache : Array (Array (Signal dom (BitVec 8))))
    : Array (Signal dom (BitVec 32)) :=
  -- QKV projection for current token (query)
  let (qs, _ks, _vs) := qkvProjectionSignal qWeights kWeights vWeights
    qScales kScales vScales config.quantShift activations

  -- Q·K^T dot product for each cached K position → seqLen scores
  let scores : Array (Signal dom (BitVec 32)) := Id.run do
    let mut sc : Array (Signal dom (BitVec 32)) := #[]
    for pos in [:config.seqLen] do
      if pos < kCache.size then
        sc := sc.push (dotProductSignal qs kCache[pos]! config.dkShift)
    return sc

  -- Softmax over scores
  let weights := softmaxSignal scores

  -- Score-V multiply
  scoreVMulSignal weights vCache config.headDim

end Sparkle.Examples.BitNet.Attention
