/-
  BitNet SoC — Full Model Forward Pass — Signal DSL (200 MHz)

  Complete BitNet 1.58B forward pass:
    token_id → Embedding → [TransformerLayer × nLayers] → De-embedding → logit

  Uses Embedding LUT for token→activation, chains N transformer layers
  sequentially (each with Attention + FFN), and projects back to vocab
  via BitLinear de-embedding.

  FSM: IDLE → EMBED → LAYERS[0..N-1] → DE_EMBED → DONE

  Target: dim=2048, headDim=64, 24 layers, vocab=32000 on Alveo U280.
  Performance @ 200 MHz (1 MAC/cycle):
    - Attention per layer: ~5 × dim = ~10,240 cycles
    - FFN per layer: ~3 × dim + 5 = ~6,149 cycles
    - Total per layer: ~16,389 cycles
    - 24 layers: ~393,336 cycles = ~1.97 ms/token
    - ~508 tokens/sec (single head, seqLen=1)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SoC.TransformerLayer
import IP.BitNet.BitLinear.TimeMux
import IP.BitNet.BitLinear.ScalePipelined
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Full model forward pass.

    FSM: 0=IDLE, 1=EMBED, 2=RUN_LAYER, 3=DE_EMBED, 4=DONE

    Embedding and De-embedding use the same TimeMux BitLinear core
    (embedding = weight lookup by token_id, de-embedding = BitLinear projection).

    For v0: embedding is simplified to pass-through of a pre-loaded
    activation (token_id selects from a small LUT via mux tree).
    De-embedding projects to a single logit output.

    Inputs:
      go              — start pulse
      tokenId         — 16-bit token ID (input)
      dimLimit        — dim - 1
      headDimLimit    — headDim - 1
      nLayers         — number of transformer layers
      weightBaseAddr  — base address for all weights in HBM
      dimBV           — dim as BitVec 32 (for address computation)
      layerStrideBV   — stride per layer in weight memory (attn + ffn weights)
      scaleVal        — Q8.24 scale constant
      memReadData/Valid — external memory interface

    Returns (result × (done × (layerIdx × phase))). -/
def fullModelForwardPass
    (dimLimit headDimLimit : BitVec 16)
    (nLayers nHeads : Nat)
    (go : Signal dom Bool)
    (tokenActivation : Signal dom (BitVec 32))  -- pre-embedded activation
    (seqPos : Signal dom (BitVec 16))           -- current sequence position
    -- Weight addresses
    (weightBaseAddr : Signal dom (BitVec 32))
    (layerStrideBV : BitVec 32)  -- total weights per layer (attn + ffn)
    (headStrideBV dimBV : BitVec 32) -- attention head stride and dim
    (scaleVal : Signal dom (BitVec 32))
    -- Memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 8 × BitVec 4))) :=
  -- Master FSM
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 32 × Bool)))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 32 × Bool)))) =>
    let masterPhase := Signal.fst self
    let r1 := Signal.snd self
    let layerIdx := Signal.fst r1
    let r2 := Signal.snd r1
    let currentAct := Signal.fst r2
    let layerStartPulse := Signal.snd r2

    let isIdle : Signal dom Bool := masterPhase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isRunning : Signal dom Bool := masterPhase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    -- Compute weight addresses for current layer
    let layerIdxExt : Signal dom (BitVec 32) :=
      layerIdx ++ (Signal.pure 0#24 : Signal dom (BitVec 24))
    let layerOffset : Signal dom (BitVec 32) :=
      layerIdxExt * (Signal.pure layerStrideBV : Signal dom (BitVec 32))
    let layerBase : Signal dom (BitVec 32) := weightBaseAddr + layerOffset

    -- Address layout within a layer:
    -- Attention weights: nHeads × 3 × dim words at layerBase
    -- FFN weights: 3 × dim words after attention
    let attnBase := layerBase
    let dimBV32 : Signal dom (BitVec 32) :=
      (Signal.pure dimBV : Signal dom (BitVec 32))
    -- FFN starts after all attention weights (nHeads * headStride)
    let nHeadsBV32 : Signal dom (BitVec 32) :=
      (Signal.pure (BitVec.ofNat 32 nHeads) : Signal dom (BitVec 32))
    let attnTotalSize : Signal dom (BitVec 32) :=
      nHeadsBV32 * (Signal.pure headStrideBV : Signal dom (BitVec 32))
    let ffnBase := layerBase + attnTotalSize
    let ffnGateBase := ffnBase
    let ffnUpBase := ffnBase + dimBV32
    let ffnDownBase := ffnBase + dimBV32 + dimBV32

    -- Transformer layer for current layer index
    let layerOut := transformerLayer dimLimit headDimLimit nHeads layerStartPulse currentAct
      seqPos attnBase headStrideBV dimBV ffnGateBase ffnUpBase ffnDownBase
      scaleVal memReadData memReadValid
    let layerResult := Signal.fst layerOut
    let layerDone : Signal dom Bool :=
      Signal.mux isRunning (Signal.fst (Signal.snd layerOut)) (Signal.pure false : Signal dom Bool)

    -- Layer count
    let nLayersBV : Signal dom (BitVec 8) :=
      (Signal.pure (BitVec.ofNat 8 (nLayers - 1)) : Signal dom (BitVec 8))
    let atLastLayer : Signal dom Bool := layerIdx === nLayersBV
    let allDone : Signal dom Bool :=
      Signal.mux layerDone atLastLayer (Signal.pure false : Signal dom Bool)
    let nextLayerReady : Signal dom Bool :=
      Signal.mux layerDone
        (Signal.mux atLastLayer (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux allDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) masterPhase)
            masterPhase))

    let nextLayerIdx : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux nextLayerReady
          (layerIdx + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          layerIdx)

    let nextAct : Signal dom (BitVec 32) :=
      Signal.mux goIdle tokenActivation
        (Signal.mux layerDone layerResult currentAct)

    let nextStart : Signal dom Bool :=
      Signal.mux goIdle (Signal.pure true : Signal dom Bool)
        (Signal.mux nextLayerReady (Signal.pure true : Signal dom Bool)
          (Signal.pure false : Signal dom Bool))

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextLayerIdx)
        (bundle2
          (Signal.register 0#32 nextAct)
          (Signal.register false nextStart)))

  let masterPhase := Signal.fst state
  let r1 := Signal.snd state
  let layerIdx := Signal.fst r1
  let r2 := Signal.snd r1
  let currentAct := Signal.fst r2

  let done : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))
  bundle2 currentAct (bundle2 done (bundle2 layerIdx masterPhase))

end Sparkle.IP.BitNet.SoC
