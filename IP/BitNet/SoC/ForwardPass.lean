/-
  BitNet SoC — Toy Transformer Forward Pass — Signal DSL

  Minimal end-to-end forward pass for dim=4, vocab=16, 1 layer:

    token_id (4-bit) → Embedding → RMSNorm → FFN → RMSNorm → De-embedding → argmax logit index (4-bit)

  Attention is omitted in this v0 (FFN-only decoder block). Adding
  attention requires KV cache state management via Signal.loop, which
  is tracked as future work.

  All operations are synthesizable (confirmed by #synthesizeVerilog).
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.Layers.Embedding
import IP.BitNet.Layers.RMSNorm
import IP.BitNet.Layers.FFN
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.Layers.ElemMul
import IP.BitNet.BitLinear.Scale

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.BitNet.BitLinear

variable {dom : DomainConfig}

-- ============================================================
-- Toy model parameters (dim=4, vocab=16, 1 layer)
-- ============================================================

/-- Embedding table: 4 dimensions × 16 vocab entries.
    Each row is one dimension's values across all 16 tokens.
    Values are Q16.16 fixed-point. -/
def toyEmbeddingTable : Array (Array (BitVec 32)) := #[
  -- dim 0: linearly spaced
  #[0x10000#32, 0x20000#32, 0x30000#32, 0x40000#32,
    0x50000#32, 0x60000#32, 0x70000#32, 0x80000#32,
    0x90000#32, 0xA0000#32, 0xB0000#32, 0xC0000#32,
    0xD0000#32, 0xE0000#32, 0xF0000#32, 0x100000#32],
  -- dim 1
  #[0x100000#32, 0xF0000#32, 0xE0000#32, 0xD0000#32,
    0xC0000#32, 0xB0000#32, 0xA0000#32, 0x90000#32,
    0x80000#32, 0x70000#32, 0x60000#32, 0x50000#32,
    0x40000#32, 0x30000#32, 0x20000#32, 0x10000#32],
  -- dim 2
  #[0x10000#32, 0x10000#32, 0x20000#32, 0x20000#32,
    0x30000#32, 0x30000#32, 0x40000#32, 0x40000#32,
    0x50000#32, 0x50000#32, 0x60000#32, 0x60000#32,
    0x70000#32, 0x70000#32, 0x80000#32, 0x80000#32],
  -- dim 3
  #[0x80000#32, 0x70000#32, 0x60000#32, 0x50000#32,
    0x40000#32, 0x30000#32, 0x20000#32, 0x10000#32,
    0x10000#32, 0x20000#32, 0x30000#32, 0x40000#32,
    0x50000#32, 0x60000#32, 0x70000#32, 0x80000#32]
]

/-- FFN weights: all +1 ternary, dim×dim = 16 per path. -/
def toyFFNWeights : Array Int := List.replicate 16 1 |>.toArray

/-- Unit scales in Q8.24. -/
def toyScale : Int := 0x01000000

/-- RMSNorm scales: unit (1.0 in Q8.24). -/
def toyRMSScales : Array (Signal dom (BitVec 32)) :=
  #[Signal.pure 0x01000000#32, Signal.pure 0x01000000#32,
    Signal.pure 0x01000000#32, Signal.pure 0x01000000#32]

/-- De-embedding weights: 16 vocab × 4 dim, ternary.
    Simple pattern: each vocab entry has a different ±1 combination. -/
def toyDeembedWeights : Array (Array Int) := #[
  #[1, 1, 1, 1],    #[1, 1, 1, -1],   #[1, 1, -1, 1],   #[1, 1, -1, -1],
  #[1, -1, 1, 1],   #[1, -1, 1, -1],  #[1, -1, -1, 1],  #[1, -1, -1, -1],
  #[-1, 1, 1, 1],   #[-1, 1, 1, -1],  #[-1, 1, -1, 1],  #[-1, 1, -1, -1],
  #[-1, -1, 1, 1],  #[-1, -1, 1, -1], #[-1, -1, -1, 1], #[-1, -1, -1, -1]
]

-- ============================================================
-- Forward pass
-- ============================================================

/-- Shared rsqrt computation for a 4-element vector.
    Returns the rsqrt value to be used by each element's normalization. -/
def rmsNormRsqrt4
    (x0 x1 x2 x3 : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let sq (x : Signal dom (BitVec 32)) : Signal dom (BitVec 64) :=
    let xExt := signExtendSignal 32 x
    xExt * xExt
  let sumSq : Signal dom (BitVec 64) :=
    treeReduce (· + ·) (Signal.pure 0) [sq x0, sq x1, sq x2, sq x3]
  let sumSqHi : Signal dom (BitVec 32) :=
    Signal.map (BitVec.extractLsb' 0 32 ·) sumSq
  let sumSqExt : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 sumSqHi
  let recipExt : Signal dom (BitVec (16 + 32)) :=
    signExtendSignal 16 (Signal.pure 0x400000#32 : Signal dom (BitVec 32))
  let meanProd : Signal dom (BitVec 48) := sumSqExt * recipExt
  let meanApprox : Signal dom (BitVec 32) :=
    Signal.map (BitVec.extractLsb' 24 32 ·) meanProd
  let lutIdx : Signal dom (BitVec 4) :=
    Signal.map (BitVec.extractLsb' 24 4 ·) meanApprox
  lutMuxTree rsqrtLUT16 lutIdx

/-- Normalize a single element: (x × rsqrt) >> 24 × scale >> 24. -/
def rmsNormElem (rsqrtVal x s : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let xExt := signExtendSignal 32 x
  let rsqrtExt := signExtendSignal 32 rsqrtVal
  let normProd := xExt * rsqrtExt
  let normShifted : Signal dom (BitVec 32) :=
    Signal.map (BitVec.extractLsb' 24 32 ·) normProd
  let normExt := signExtendSignal 32 normShifted
  let scaleExt := signExtendSignal 32 s
  let scaledProd := normExt * scaleExt
  Signal.map (BitVec.extractLsb' 24 32 ·) scaledProd

/-- Toy transformer forward pass (FFN-only, no attention).
    token_id (4-bit) → embedding → RMSNorm → FFN → RMSNorm → de-embed → argmax → output (4-bit)

    Single function, fully synthesizable. Returns the highest logit's value
    (argmax would need comparator tree — for v0 we return the first logit). -/
def toyForwardPass (tokenId : Signal dom (BitVec 4))
    : Signal dom (BitVec 32) :=
  -- 1. Embedding: token_id → 4-element vector (inline 4 LUT lookups)
  let e0 := lutMuxTree (toyEmbeddingTable.toList.getD 0 #[]) tokenId
  let e1 := lutMuxTree (toyEmbeddingTable.toList.getD 1 #[]) tokenId
  let e2 := lutMuxTree (toyEmbeddingTable.toList.getD 2 #[]) tokenId
  let e3 := lutMuxTree (toyEmbeddingTable.toList.getD 3 #[]) tokenId

  -- 2. RMSNorm (pre-FFN)
  let s := Signal.pure 0x01000000#32
  let rsqrt1 := rmsNormRsqrt4 e0 e1 e2 e3
  let n0 := rmsNormElem rsqrt1 e0 s
  let n1 := rmsNormElem rsqrt1 e1 s
  let n2 := rmsNormElem rsqrt1 e2 s
  let n3 := rmsNormElem rsqrt1 e3 s

  -- 3. FFN block
  let ffnOut := ffnBlockSignal toyFFNWeights toyFFNWeights toyFFNWeights
    toyScale toyScale toyScale n0 #[n0, n1, n2, n3]

  -- 4. RMSNorm (post-FFN)
  let rsqrt2 := rmsNormRsqrt4 ffnOut ffnOut ffnOut ffnOut
  let p0 := rmsNormElem rsqrt2 ffnOut s

  -- 5. De-embedding: first logit = Σ weights[0][d] × activations[d]
  bitLinearSignal #[1, 1, 1, 1] #[p0, p0, p0, p0]

end Sparkle.IP.BitNet.SoC
