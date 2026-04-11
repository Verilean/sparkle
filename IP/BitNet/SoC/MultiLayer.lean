/-
  BitNet SoC — Multi-Layer Sequential Executor — Signal DSL

  Chains N FFN layers sequentially. Each layer reads weights from a
  different base address region in external memory.

  FSM: IDLE → LAYER[0] → LAYER[1] → ... → LAYER[N-1] → DONE

  Weight memory layout (per layer, 3 BitLinear paths):
    layer i gate weights: weightBaseAddr + i * layerStride + 0 * pathStride
    layer i up weights:   weightBaseAddr + i * layerStride + 1 * pathStride
    layer i down weights: weightBaseAddr + i * layerStride + 2 * pathStride

  where pathStride = dim (number of weights per BitLinear path)
  and layerStride = 3 * dim.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SoC.FFNLayer

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Multi-layer sequential FFN executor.
    Runs `nLayers` FFN layers sequentially, feeding output of layer i
    into layer i+1.

    Returns (result × (done × (memReadAddr × (layerIdx × masterPhase)))) -/
def multiLayerFFN
    (dim nLayers : Nat)
    (go : Signal dom Bool)
    (input : Signal dom (BitVec 32))
    -- Weight memory base address (all layers)
    (weightBaseAddr : Signal dom (BitVec 32))
    -- Scale constants (same for all layers in v1)
    (scaleVal : Signal dom (BitVec 32))
    -- External memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 32 × (BitVec 8 × BitVec 4)))) :=
  -- Master FSM: 0=IDLE, 1=RUN_LAYER, 2=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 32 × Bool)))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 32 × Bool)))) =>
    let masterPhase := Signal.fst self
    let rest1 := Signal.snd self
    let layerIdx := Signal.fst rest1
    let rest2 := Signal.snd rest1
    let currentActivation := Signal.fst rest2
    let layerStartPulse := Signal.snd rest2

    let isIdle : Signal dom Bool := masterPhase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isRunning : Signal dom Bool := masterPhase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    -- Compute base addresses for current layer
    -- layerStride = 3 * dim, pathStride = dim
    let dimBV : Signal dom (BitVec 32) := (Signal.pure (BitVec.ofNat 32 dim) : Signal dom (BitVec 32))
    let layerIdxExt : Signal dom (BitVec 32) :=
      layerIdx ++ (Signal.pure 0#24 : Signal dom (BitVec 24))
    -- layerOffset = layerIdx * 3 * dim (simplified: layerIdx * layerStride)
    let layerStride : Signal dom (BitVec 32) :=
      (Signal.pure (BitVec.ofNat 32 (3 * dim)) : Signal dom (BitVec 32))
    let layerOffset : Signal dom (BitVec 32) := layerIdxExt * layerStride
    let layerBase : Signal dom (BitVec 32) := weightBaseAddr + layerOffset
    let gateBase : Signal dom (BitVec 32) := layerBase
    let upBase : Signal dom (BitVec 32) := layerBase + dimBV
    let downBase : Signal dom (BitVec 32) := layerBase + dimBV + dimBV

    -- Run FFN layer for current layer
    let ffnOut := ffnLayerSeq dim layerStartPulse currentActivation
      gateBase upBase downBase scaleVal scaleVal scaleVal memReadData memReadValid
    let ffnResult := Signal.fst ffnOut
    let ffnDone : Signal dom Bool := Signal.fst (Signal.snd ffnOut)

    -- Layer count limit
    let nLayersBV : Signal dom (BitVec 8) :=
      (Signal.pure (BitVec.ofNat 8 (nLayers - 1)) : Signal dom (BitVec 8))
    let atLastLayer : Signal dom Bool := layerIdx === nLayersBV
    let layerDone : Signal dom Bool :=
      Signal.mux isRunning ffnDone (Signal.pure false : Signal dom Bool)

    -- Phase transitions
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let allDone : Signal dom Bool :=
      Signal.mux layerDone atLastLayer (Signal.pure false : Signal dom Bool)
    let nextLayerReady : Signal dom Bool :=
      Signal.mux layerDone
        (Signal.mux atLastLayer (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux allDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) masterPhase)
            masterPhase))

    -- Layer index: increment on layer completion (not last)
    let nextLayerIdx : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux nextLayerReady
          (layerIdx + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          layerIdx)

    -- Activation: latch input on go, update with FFN result on layer done
    let nextActivation : Signal dom (BitVec 32) :=
      Signal.mux goIdle input
        (Signal.mux layerDone ffnResult currentActivation)

    -- Layer start pulse: on go (first layer) or next layer ready
    let nextStartPulse : Signal dom Bool :=
      Signal.mux goIdle (Signal.pure true : Signal dom Bool)
        (Signal.mux nextLayerReady (Signal.pure true : Signal dom Bool)
          (Signal.pure false : Signal dom Bool))

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextLayerIdx)
        (bundle2
          (Signal.register 0#32 nextActivation)
          (Signal.register false nextStartPulse)))

  -- Extract outputs
  let masterPhase := Signal.fst state
  let rest1 := Signal.snd state
  let layerIdx := Signal.fst rest1
  let rest2 := Signal.snd rest1
  let currentActivation := Signal.fst rest2

  let done : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))

  -- Memory address from the internal FFN layer (forwarded)
  let memAddr : Signal dom (BitVec 32) := (Signal.pure 0#32 : Signal dom (BitVec 32))  -- TODO: wire through

  bundle2 currentActivation (bundle2 done (bundle2 memAddr (bundle2 layerIdx masterPhase)))

end Sparkle.IP.BitNet.SoC
