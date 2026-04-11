/-
  BitNet SoC — Autoregressive Token Generation Loop — Signal DSL (200 MHz)

  Orchestrates multi-token generation:
    1. Embedding lookup (token_id → activation from HBM)
    2. Forward pass (transformer layers)
    3. De-embedding (activation → logit)
    4. Argmax (logit → next token_id)  [simplified: pass-through for v0]
    5. Increment seqPos, repeat from 1

  FSM: IDLE → EMBED → FORWARD → ARGMAX → CHECK_STOP → loop back or DONE

  Stop condition: maxTokens reached or EOS token generated.

  This is the top-level inference controller that the host kicks off
  via HostIF registers (go, tokenId, maxTokens).
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SoC.FullModel
import IP.BitNet.Layers.EmbeddingHBM

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.Layers

variable {dom : DomainConfig}

/-- Autoregressive generation loop.

    Inputs:
      go            — start generation
      firstTokenAct — first token's activation (pre-embedded by host or HBM lookup)
      maxTokens     — maximum tokens to generate (BitVec 16)
      dimLimit, headDimLimit — model dimensions
      nLayers, nHeads — model config
      weightBaseAddr, deembedBaseAddr — HBM addresses
      layerStrideBV, headStrideBV, dimBV — address constants
      scaleVal      — Q8.24 scale
      memReadData, memReadValid — memory interface

    Returns (currentToken × (tokenCount × (done × phase))) -/
def autoRegressiveLoop
    (dimLimit headDimLimit : BitVec 16)
    (nLayers nHeads : Nat)
    (go : Signal dom Bool)
    (firstTokenAct : Signal dom (BitVec 32))
    (maxTokens : Signal dom (BitVec 16))
    -- Addresses
    (weightBaseAddr deembedBaseAddr : Signal dom (BitVec 32))
    (layerStrideBV headStrideBV dimBV : BitVec 32)
    (scaleVal : Signal dom (BitVec 32))
    -- Memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (BitVec 16 × (Bool × BitVec 4))) :=
  -- FSM: 0=IDLE, 1=FORWARD, 2=CHECK_STOP, 3=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 16 × (BitVec 16 × Bool))))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 16 × (BitVec 16 × Bool))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let currentAct := Signal.fst r1
    let r2 := Signal.snd r1
    let seqPos := Signal.fst r2
    let r3 := Signal.snd r2
    let tokenCount := Signal.fst r3
    let fwdStartPulse := Signal.snd r3

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isForward : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isCheck : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- Forward pass (FullModel)
    let fwdOut := fullModelForwardPass dimLimit headDimLimit nLayers nHeads
      fwdStartPulse currentAct seqPos
      weightBaseAddr deembedBaseAddr layerStrideBV headStrideBV dimBV
      scaleVal memReadData memReadValid
    let fwdResult := Signal.fst fwdOut
    let fwdDone : Signal dom Bool :=
      Signal.mux isForward (Signal.fst (Signal.snd fwdOut)) (Signal.pure false : Signal dom Bool)

    -- Check stop: tokenCount >= maxTokens
    let atMaxTokens : Signal dom Bool :=
      tokenCount === maxTokens

    -- Phase transitions
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))        -- → FORWARD
        (Signal.mux fwdDone (Signal.pure 2#4 : Signal dom (BitVec 4))   -- → CHECK_STOP
          (Signal.mux isCheck
            (Signal.mux atMaxTokens
              (Signal.pure 3#4 : Signal dom (BitVec 4))                  -- → DONE
              (Signal.pure 1#4 : Signal dom (BitVec 4)))                 -- → FORWARD (next token)
            (Signal.mux isDone
              (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
              phase)))

    -- Current activation: first token on go, forward result after each token
    let nextAct : Signal dom (BitVec 32) :=
      Signal.mux goIdle firstTokenAct
        (Signal.mux fwdDone fwdResult currentAct)

    -- SeqPos: 0 on go, increment after each token
    let nextSeqPos : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux isCheck
          (seqPos + (Signal.pure 1#16 : Signal dom (BitVec 16)))
          seqPos)

    -- Token count: 0 on go, increment after each token
    let nextTokenCount : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux isCheck
          (tokenCount + (Signal.pure 1#16 : Signal dom (BitVec 16)))
          tokenCount)

    -- Forward start pulse: on go (first token) or when looping back
    let nextFwdStart : Signal dom Bool :=
      Signal.mux goIdle (Signal.pure true : Signal dom Bool)
        (Signal.mux (Signal.mux isCheck
          (Signal.mux atMaxTokens (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
          (Signal.pure false : Signal dom Bool))
          (Signal.pure true : Signal dom Bool)
          (Signal.pure false : Signal dom Bool))

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextAct)
        (bundle2
          (Signal.register 0#16 nextSeqPos)
          (bundle2
            (Signal.register 0#16 nextTokenCount)
            (Signal.register false nextFwdStart))))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let currentAct := Signal.fst r1
  let r2 := Signal.snd r1
  let _seqPos := Signal.fst r2
  let r3 := Signal.snd r2
  let tokenCount := Signal.fst r3

  let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
  bundle2 currentAct (bundle2 tokenCount (bundle2 isDone phase))

end Sparkle.IP.BitNet.SoC
