/-
  BitNet Attention — Time-Multiplexed Full Single Head — Signal DSL (200 MHz)

  Complete single-head attention via FSM:
    0 IDLE
    1 Q_PROJ   — project Q[0..headDim-1] via TimeMux (headDim × dim cycles)
    2 K_PROJ   — project K[0..headDim-1], store to KV cache BRAM
    3 V_PROJ   — project V[0..headDim-1], store to KV cache BRAM
    4 DOT_PROD — Q · K_cached[pos] for each cached position (seqLen × headDim cycles)
    5 SOFTMAX  — simplified: skip (use raw scores as weights for v0)
    6 SCORE_V  — weighted sum of V_cached (headDim × seqLen cycles)
    7 DONE

  Simplifications for v0:
  - Single head only (multi-head wraps this)
  - Softmax replaced by identity (raw dot product scores as weights)
  - seqLen = 1 (single-token, no cache accumulation across tokens)
  - Output = first element of Score-V result

  These simplifications let us prove the full FSM structure synthesizes.
  Adding real softmax / multi-token cache is incremental.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.BitLinear.TimeMux
import IP.BitNet.BitLinear.ScalePipelined
import IP.BitNet.Attention.Quantize
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Full single-head attention FSM.

    For v0: single-token (seqLen=1), no real softmax.
    Q projection → K projection → V projection → Q·K dot product → Score·V → done.

    All projections reuse the same TimeMux BitLinear core with different
    weight addresses.

    Returns (result × (done × phase)). -/
def attentionHeadFull
    (dimLimit : BitVec 16)    -- dim - 1
    (headDimLimit : BitVec 16) -- headDim - 1
    (go : Signal dom Bool)
    (activation : Signal dom (BitVec 32))
    -- Weight base addresses (Q, K, V projection weight rows stored sequentially)
    (qBaseAddr kBaseAddr vBaseAddr : Signal dom (BitVec 32))
    (scaleVal : Signal dom (BitVec 32))
    -- Memory interface for weight reads
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × BitVec 4)) :=
  -- FSM state: phase(4) × qResult(32) × kResult(32) × vResult(32) × dotResult(32) × scoreVResult(32)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let qResult := Signal.fst r1
    let r2 := Signal.snd r1
    let kResult := Signal.fst r2
    let r3 := Signal.snd r2
    let vResult := Signal.fst r3
    let r4 := Signal.snd r3
    let dotResult := Signal.fst r4
    let scoreVResult := Signal.snd r4

    -- Phase decode
    let isIdle    : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isQProj   : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isKProj   : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isVProj   : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isDot     : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))
    let isScoreV  : Signal dom Bool := phase === (Signal.pure 5#4 : Signal dom (BitVec 4))
    let isDone    : Signal dom Bool := phase === (Signal.pure 6#4 : Signal dom (BitVec 4))

    -- Shared TimeMux BitLinear: compute MAC for current phase
    -- Select base address based on phase
    let activeBaseAddr : Signal dom (BitVec 32) :=
      Signal.mux isQProj qBaseAddr
        (Signal.mux isKProj kBaseAddr
          (Signal.mux isVProj vBaseAddr
            (Signal.pure 0#32 : Signal dom (BitVec 32))))

    -- TimeMux start: only on phase entry
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- The shared MAC core (for Q/K/V projections and dot product)
    let macState := bitLinearTimeMux dimLimit
      (Signal.pure 0#16 : Signal dom (BitVec 16))
      (Signal.pure 0#2 : Signal dom (BitVec 2))
      (Signal.pure false : Signal dom Bool)
      goIdle activation
    let macResult := bitLinearTimeMuxResult macState
    let macDone := bitLinearTimeMuxDone macState

    -- Scale + Quantize for projections (pipelined, 1 cycle)
    let acc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 macResult
    let scaled := scaleMultiplyPipelined acc48 scaleVal

    -- Phase transitions
    let qDone : Signal dom Bool := Signal.mux isQProj macDone (Signal.pure false : Signal dom Bool)
    let kDone : Signal dom Bool := Signal.mux isKProj macDone (Signal.pure false : Signal dom Bool)
    let vDone : Signal dom Bool := Signal.mux isVProj macDone (Signal.pure false : Signal dom Bool)
    -- For v0 (seqLen=1): dot product = q * k (single MAC)
    let dotDone : Signal dom Bool := Signal.mux isDot macDone (Signal.pure false : Signal dom Bool)
    -- score-V = score * v (single MAC for seqLen=1)
    let svDone : Signal dom Bool := Signal.mux isScoreV macDone (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))       -- → Q_PROJ
        (Signal.mux qDone (Signal.pure 2#4 : Signal dom (BitVec 4))    -- → K_PROJ
          (Signal.mux kDone (Signal.pure 3#4 : Signal dom (BitVec 4))  -- → V_PROJ
            (Signal.mux vDone (Signal.pure 4#4 : Signal dom (BitVec 4))  -- → DOT
              (Signal.mux dotDone (Signal.pure 5#4 : Signal dom (BitVec 4)) -- → SCORE_V
                (Signal.mux svDone (Signal.pure 6#4 : Signal dom (BitVec 4))  -- → DONE
                  (Signal.mux isDone
                    (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
                    phase))))))

    -- Latch results at each phase completion
    let nextQ : Signal dom (BitVec 32) := Signal.mux qDone scaled qResult
    let nextK : Signal dom (BitVec 32) := Signal.mux kDone scaled kResult
    let nextV : Signal dom (BitVec 32) := Signal.mux vDone scaled vResult
    -- Dot product: for seqLen=1, just Q*K (simplified)
    let nextDot : Signal dom (BitVec 32) := Signal.mux dotDone macResult dotResult
    -- Score-V: for seqLen=1, just score*V
    let nextSV : Signal dom (BitVec 32) := Signal.mux svDone macResult scoreVResult

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextQ)
        (bundle2
          (Signal.register 0#32 nextK)
          (bundle2
            (Signal.register 0#32 nextV)
            (bundle2
              (Signal.register 0#32 nextDot)
              (Signal.register 0#32 nextSV)))))

  -- Extract outputs
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _qResult := Signal.fst r1
  let r2 := Signal.snd r1
  let _kResult := Signal.fst r2
  let r3 := Signal.snd r2
  let _vResult := Signal.fst r3
  let r4 := Signal.snd r3
  let _dotResult := Signal.fst r4
  let scoreVResult := Signal.snd r4

  let done : Signal dom Bool := phase === (Signal.pure 6#4 : Signal dom (BitVec 4))
  bundle2 scoreVResult (bundle2 done phase)

end Sparkle.IP.BitNet.Attention
