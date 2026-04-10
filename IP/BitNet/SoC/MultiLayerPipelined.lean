/-
  BitNet SoC — Multi-Layer Pipelined FFN Executor — Signal DSL (200 MHz)

  Chains N pipelined FFN layers sequentially. Same architecture as
  MultiLayer.lean but using FFNLayerPipelined for 200 MHz operation.

  Target: BitNet 1.58B (dim=2048, 24 layers) on Alveo U280.
  Performance: ~1,357 tokens/sec @ 200 MHz with 1 MAC/cycle.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SoC.FFNLayerPipelined

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Multi-layer pipelined FFN executor (200 MHz target).
    Returns (result × (done × (layerIdx × masterPhase))). -/
def multiLayerFFNPipelined
    (dim nLayers : Nat)
    (go : Signal dom Bool)
    (input : Signal dom (BitVec 32))
    (weightBaseAddr : Signal dom (BitVec 32))
    (scaleVal : Signal dom (BitVec 32))
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 8 × BitVec 4))) :=
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

    -- Address computation for current layer
    let dimBV : Signal dom (BitVec 32) :=
      (Signal.pure (BitVec.ofNat 32 dim) : Signal dom (BitVec 32))
    let layerIdxExt : Signal dom (BitVec 32) :=
      layerIdx ++ (Signal.pure 0#24 : Signal dom (BitVec 24))
    let layerStride : Signal dom (BitVec 32) :=
      (Signal.pure (BitVec.ofNat 32 (3 * dim)) : Signal dom (BitVec 32))
    let layerOffset : Signal dom (BitVec 32) := layerIdxExt * layerStride
    let layerBase : Signal dom (BitVec 32) := weightBaseAddr + layerOffset
    let gateBase : Signal dom (BitVec 32) := layerBase
    let upBase : Signal dom (BitVec 32) := layerBase + dimBV
    let downBase : Signal dom (BitVec 32) := layerBase + dimBV + dimBV

    -- Pipelined FFN layer
    let ffnOut := ffnLayerPipelined dim layerStartPulse currentAct
      gateBase upBase downBase scaleVal scaleVal scaleVal memReadData memReadValid
    let ffnResult := Signal.fst ffnOut
    let ffnDone : Signal dom Bool := Signal.fst (Signal.snd ffnOut)

    -- Layer count
    let nLayersBV : Signal dom (BitVec 8) :=
      (Signal.pure (BitVec.ofNat 8 (nLayers - 1)) : Signal dom (BitVec 8))
    let atLastLayer : Signal dom Bool := layerIdx === nLayersBV
    let layerDone : Signal dom Bool :=
      Signal.mux isRunning ffnDone (Signal.pure false : Signal dom Bool)
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
      Signal.mux goIdle input
        (Signal.mux layerDone ffnResult currentAct)

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
