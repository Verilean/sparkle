/-
  BitNet SoC — Full Transformer Layer — Signal DSL (200 MHz)

  One transformer decoder layer:
    input → RMSNorm → Attention → ResidualAdd → RMSNorm → FFN → ResidualAdd → output

  Simplifications for v0:
  - RMSNorm omitted (pass-through) — requires per-element processing FSM
  - Attention is single-head, seqLen=1 (no KV cache accumulation)
  - Residual add is combinational (1 cycle)

  FSM: IDLE → ATTENTION → ATTN_RESIDUAL → FFN → FFN_RESIDUAL → DONE
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Attention.MultiHeadTimeMux
import IP.BitNet.SoC.FFNLayerPipelined
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.Attention
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- One transformer decoder layer (Attention + FFN).

    Inputs:
      go           — start pulse
      input        — activation (32-bit Q16.16)
      dimLimit     — dim - 1 as BitVec 16
      headDimLimit — headDim - 1 as BitVec 16
      attnQBase, attnKBase, attnVBase — attention weight addresses
      ffnGateBase, ffnUpBase, ffnDownBase — FFN weight addresses
      scaleVal     — Q8.24 scale constant
      memReadData, memReadValid — external memory interface

    Returns (result × (done × phase)). -/
def transformerLayer
    (dimLimit headDimLimit : BitVec 16)
    (nHeads : Nat)
    (go : Signal dom Bool)
    (input : Signal dom (BitVec 32))
    (seqPos : Signal dom (BitVec 16))
    -- Attention weight base + stride
    (attnBaseAddr : Signal dom (BitVec 32))
    (headStrideBV dimBV : BitVec 32)
    -- FFN weight addresses
    (ffnGateBase ffnUpBase ffnDownBase : Signal dom (BitVec 32))
    -- Scale
    (scaleVal : Signal dom (BitVec 32))
    -- Memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × BitVec 4)) :=
  -- FSM: 0=IDLE, 1=ATTENTION, 2=ATTN_RESID, 3=FFN, 4=FFN_RESID, 5=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 32 × BitVec 32)))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 32 × BitVec 32)))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let savedInput := Signal.fst r1
    let r2 := Signal.snd r1
    let attnResult := Signal.fst r2
    let ffnResult := Signal.snd r2

    let isIdle      : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isAttn      : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isAttnResid : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isFFN       : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isFFNResid  : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))
    let isDone      : Signal dom Bool := phase === (Signal.pure 5#4 : Signal dom (BitVec 4))

    -- Multi-head attention
    let attnGo : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let attnOut := multiHeadAttentionTimeMux dimLimit headDimLimit nHeads attnGo savedInput
      seqPos attnBaseAddr headStrideBV dimBV scaleVal memReadData memReadValid
    let attnResultNew := Signal.fst attnOut
    let attnDone : Signal dom Bool :=
      Signal.mux isAttn (Signal.fst (Signal.snd attnOut)) (Signal.pure false : Signal dom Bool)

    -- Attention residual: input + attn_output
    let attnResidResult := residualAddSignal savedInput attnResult

    -- FFN layer
    let ffnGo : Signal dom Bool :=
      Signal.mux isAttnResid (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool)
    let ffnOut := ffnLayerPipelined dimLimit ffnGo attnResidResult
      ffnGateBase ffnUpBase ffnDownBase scaleVal scaleVal scaleVal memReadData memReadValid
    let ffnResultNew := Signal.fst ffnOut
    let ffnDone : Signal dom Bool :=
      Signal.mux isFFN (Signal.fst (Signal.snd ffnOut)) (Signal.pure false : Signal dom Bool)

    -- FFN residual: attn_resid_output + ffn_output
    let ffnResidResult := residualAddSignal attnResidResult ffnResult

    -- Phase transitions
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))          -- → ATTN
        (Signal.mux attnDone (Signal.pure 2#4 : Signal dom (BitVec 4))    -- → ATTN_RESID
          (Signal.mux isAttnResid (Signal.pure 3#4 : Signal dom (BitVec 4)) -- → FFN
            (Signal.mux ffnDone (Signal.pure 4#4 : Signal dom (BitVec 4))  -- → FFN_RESID
              (Signal.mux isFFNResid (Signal.pure 5#4 : Signal dom (BitVec 4)) -- → DONE
                (Signal.mux isDone
                  (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
                  phase)))))

    let nextInput : Signal dom (BitVec 32) := Signal.mux goIdle input savedInput
    let nextAttn : Signal dom (BitVec 32) := Signal.mux attnDone attnResultNew attnResult
    let nextFFN : Signal dom (BitVec 32) := Signal.mux ffnDone ffnResidResult ffnResult

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextInput)
        (bundle2
          (Signal.register 0#32 nextAttn)
          (Signal.register 0#32 nextFFN)))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _savedInput := Signal.fst r1
  let r2 := Signal.snd r1
  let _attnResult := Signal.fst r2
  let ffnResult := Signal.snd r2

  let done : Signal dom Bool := phase === (Signal.pure 5#4 : Signal dom (BitVec 4))
  bundle2 ffnResult (bundle2 done phase)

end Sparkle.IP.BitNet.SoC
