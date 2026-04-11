/-
  BitNet Layers — Embedding and De-embedding — Signal DSL

  Embedding: token_id (4-bit for vocab=16) → dim-element activation vector
  De-embedding: dim-element vector → vocab-size logits via BitLinear projection

  Both are synthesizable. Embedding uses per-dimension lutMuxTree;
  De-embedding uses bitLinearSignal (ternary MAC + adder tree).
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Embedding lookup: token_id → array of dim activation signals.
    `table` is a vocab × dim matrix of Q16.16 constants (pre-computed).
    Each element of the output vector is a separate lutMuxTree on token_id. -/
@[reducible] def embedLookupList
    (tokenId : Signal dom (BitVec 4))
    : List (Array (BitVec 32)) → List (Signal dom (BitVec 32))
  | [] => []
  | col :: rest => lutMuxTree col tokenId :: embedLookupList tokenId rest

/-- Embedding layer: token_id → dim-element activation vector.
    `embeddingTable` is dim arrays of vocab-many BitVec 32 constants.
    embeddingTable[d][v] = the d-th dimension of the embedding for token v. -/
def embeddingSignal (embeddingTable : Array (Array (BitVec 32)))
    (tokenId : Signal dom (BitVec 4))
    : Array (Signal dom (BitVec 32)) :=
  (embedLookupList tokenId embeddingTable.toList).toArray

/-- De-embedding (LM Head): project dim-element vector to vocab-size logits.
    Each output logit[v] = Σ weights[v][d] × activations[d] (ternary BitLinear).
    `projWeights` is vocab-many weight arrays, each of length dim. -/
@[reducible] def deembedProjectList
    (activations : Array (Signal dom (BitVec 32)))
    : List (Array Int) → List (Signal dom (BitVec 32))
  | [] => []
  | weights :: rest =>
    bitLinearSignal weights activations :: deembedProjectList activations rest

def deembeddingSignal (projWeights : Array (Array Int))
    (activations : Array (Signal dom (BitVec 32)))
    : Array (Signal dom (BitVec 32)) :=
  (deembedProjectList activations projWeights.toList).toArray

end Sparkle.IP.BitNet.Layers
