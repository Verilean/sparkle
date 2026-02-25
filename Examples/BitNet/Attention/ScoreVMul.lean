/-
  BitNet Attention — Score-V Multiplication — Signal DSL

  Computes attention-weighted V output for one head:
    out[j] = Σ_{i=0}^{seqLen-1} weight[i] × V[i][j] >> 24

  - weight[i]: Q8.24 (32-bit) from softmax
  - V[i][j]: INT8 (8-bit), sign-extended to 32 bits
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Weighted sum for one output element j:
    out[j] = (Σ_i weight[i] × V[i][j]) >> 24

    Each weight is Q8.24 (32-bit), each V is INT8 (sign-extended to 32 bits).
    Product is computed in 64 bits to avoid overflow. -/
def weightedVElementSignal
    (weights : Array (Signal dom (BitVec 32)))
    (vColumn : Array (Signal dom (BitVec 8)))
    : Signal dom (BitVec 32) :=
  let products : Array (Signal dom (BitVec 64)) := Id.run do
    let mut prods : Array (Signal dom (BitVec 64)) := #[]
    for i in [:weights.size] do
      if i < vColumn.size then
        -- Sign-extend weight (32 → 64) and V (8 → 64)
        let wExt := signExtendSignal 32 weights[i]!
        let vExt := signExtendSignal 56 vColumn[i]!   -- 56 + 8 = 64
        prods := prods.push ((· * ·) <$> wExt <*> vExt)
    return prods
  -- Sum via adder tree
  let sum := adderTree products
  -- Shift right by 24 and truncate to 32 bits
  sum.map (BitVec.extractLsb' 24 32 ·)

/-- Score-V multiply for one attention head.
    Computes weighted V output for each element j in [0, headDim). -/
def scoreVMulSignal
    (weights : Array (Signal dom (BitVec 32)))
    (vMatrix : Array (Array (Signal dom (BitVec 8))))
    (headDim : Nat)
    : Array (Signal dom (BitVec 32)) :=
  Id.run do
    let mut outputs : Array (Signal dom (BitVec 32)) := #[]
    for j in [:headDim] do
      -- Extract column j from V matrix
      let vColumn : Array (Signal dom (BitVec 8)) := Id.run do
        let mut col : Array (Signal dom (BitVec 8)) := #[]
        for i in [:vMatrix.size] do
          if j < vMatrix[i]!.size then
            col := col.push vMatrix[i]![j]!
        return col
      outputs := outputs.push (weightedVElementSignal weights vColumn)
    return outputs

end Sparkle.Examples.BitNet.Attention
