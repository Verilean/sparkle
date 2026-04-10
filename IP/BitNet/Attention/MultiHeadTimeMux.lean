/-
  BitNet Attention — Multi-Head Time-Multiplexed — Signal DSL (200 MHz)

  Executes nHeads attention heads sequentially, accumulating outputs.
  Each head uses attentionHeadFull with different weight addresses.

  FSM: IDLE → HEAD[0] → HEAD[1] → ... → HEAD[nHeads-1] → OUTPUT_PROJ → DONE

  Output projection: sum of all head outputs → BitLinear → final output.
  For v0: simple accumulation (add all head outputs), no output projection weight.

  Weight memory layout per head:
    head i Q weights: attnBaseAddr + i * headStride + 0
    head i K weights: attnBaseAddr + i * headStride + dimWords
    head i V weights: attnBaseAddr + i * headStride + 2 * dimWords
  where headStride = 3 * dimWords (Q + K + V per head)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Attention.TimeMux

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Multi-head attention FSM.

    Runs nHeads attention heads sequentially, accumulates outputs.
    Returns (result × (done × (headIdx × phase))). -/
def multiHeadAttentionTimeMux
    (dimLimit headDimLimit : BitVec 16)
    (nHeads : Nat)
    (go : Signal dom Bool)
    (activation : Signal dom (BitVec 32))
    -- Base address for all attention weights
    (attnBaseAddr : Signal dom (BitVec 32))
    -- Stride per head in weight memory (= 3 * dim, as BitVec 32)
    (headStrideBV : BitVec 32)
    -- Dim as BitVec 32 for address offset computation
    (dimBV : BitVec 32)
    (scaleVal : Signal dom (BitVec 32))
    -- Memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 8 × BitVec 4))) :=
  -- Master FSM: 0=IDLE, 1=RUN_HEAD, 2=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 32 × Bool)))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 32 × Bool)))) =>
    let masterPhase := Signal.fst self
    let r1 := Signal.snd self
    let headIdx := Signal.fst r1
    let r2 := Signal.snd r1
    let accOutput := Signal.fst r2
    let headStartPulse := Signal.snd r2

    let isIdle : Signal dom Bool := masterPhase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isRunning : Signal dom Bool := masterPhase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    -- Compute weight addresses for current head
    let headIdxExt : Signal dom (BitVec 32) :=
      headIdx ++ (Signal.pure 0#24 : Signal dom (BitVec 24))
    let headOffset : Signal dom (BitVec 32) :=
      headIdxExt * (Signal.pure headStrideBV : Signal dom (BitVec 32))
    let headBase : Signal dom (BitVec 32) := attnBaseAddr + headOffset
    let qBase := headBase
    let kBase := headBase + (Signal.pure dimBV : Signal dom (BitVec 32))
    let vBase := headBase + (Signal.pure dimBV : Signal dom (BitVec 32))
                           + (Signal.pure dimBV : Signal dom (BitVec 32))

    -- Run attention head for current index
    let headOut := attentionHeadFull dimLimit headDimLimit headStartPulse activation
      qBase kBase vBase scaleVal memReadData memReadValid
    let headResult := Signal.fst headOut
    let headDone : Signal dom Bool :=
      Signal.mux isRunning (Signal.fst (Signal.snd headOut)) (Signal.pure false : Signal dom Bool)

    -- Head count
    let nHeadsBV : Signal dom (BitVec 8) :=
      (Signal.pure (BitVec.ofNat 8 (nHeads - 1)) : Signal dom (BitVec 8))
    let atLastHead : Signal dom Bool := headIdx === nHeadsBV
    let allDone : Signal dom Bool :=
      Signal.mux headDone atLastHead (Signal.pure false : Signal dom Bool)
    let nextHeadReady : Signal dom Bool :=
      Signal.mux headDone
        (Signal.mux atLastHead (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- Phase transitions
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux allDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) masterPhase)
            masterPhase))

    let nextHeadIdx : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux nextHeadReady
          (headIdx + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          headIdx)

    -- Accumulate: sum of all head outputs
    let nextAcc : Signal dom (BitVec 32) :=
      Signal.mux goIdle (Signal.pure 0#32 : Signal dom (BitVec 32))
        (Signal.mux headDone (accOutput + headResult) accOutput)

    let nextStart : Signal dom Bool :=
      Signal.mux goIdle (Signal.pure true : Signal dom Bool)
        (Signal.mux nextHeadReady (Signal.pure true : Signal dom Bool)
          (Signal.pure false : Signal dom Bool))

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextHeadIdx)
        (bundle2
          (Signal.register 0#32 nextAcc)
          (Signal.register false nextStart)))

  let masterPhase := Signal.fst state
  let r1 := Signal.snd state
  let headIdx := Signal.fst r1
  let r2 := Signal.snd r1
  let accOutput := Signal.fst r2

  let done : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))
  bundle2 accOutput (bundle2 done (bundle2 headIdx masterPhase))

end Sparkle.IP.BitNet.Attention
