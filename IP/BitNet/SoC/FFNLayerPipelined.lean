/-
  BitNet SoC — Pipelined FFN Layer — Signal DSL (200 MHz target)

  Same datapath as FFNLayer.lean but with pipeline registers after
  every multiply. Breaks critical path so DSP48E2 can run at 200 MHz+.

  Latency per FFN layer: 3 × dim + 5 extra pipeline cycles.
  For dim=2048: 6,149 cycles @ 200 MHz = 30.7 μs.

  Uses TimeMux (1 MAC/cycle) — the pipeline registers are only in
  Scale/ReLU²/ElemMul, not in the MAC loop itself (which is already
  register-isolated by the FSM).
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.BitLinear.WeightStreamer
import IP.BitNet.BitLinear.ScalePipelined
import IP.BitNet.Layers.PipelinedOps
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Pipelined FFN layer for 200 MHz.
    Pipeline registers after Scale multiply, ReLU² square, and ElemMul.

    FSM: IDLE → GATE_BL → GATE_SCALE(1cy) → UP_BL → UP_SCALE(1cy) →
         RELU_ELEMMUL(1cy+1cy) → DOWN_BL → DOWN_SCALE(1cy) → RESID → DONE

    Inputs/outputs same as ffnLayerSeq. -/
def ffnLayerPipelined
    (dim : Nat)
    (go : Signal dom Bool)
    (input : Signal dom (BitVec 32))
    (gateBaseAddr upBaseAddr downBaseAddr : Signal dom (BitVec 32))
    (gateScaleVal upScaleVal downScaleVal : Signal dom (BitVec 32))
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × BitVec 4)) :=
  -- FSM: 0=IDLE, 1=GATE_BL, 2=GATE_SCALE, 3=UP_BL, 4=UP_SCALE,
  --      5=RELU_ELEMMUL, 6=DOWN_BL, 7=DOWN_SCALE, 8=RESID, 9=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let gateResult := Signal.fst r1
    let r2 := Signal.snd r1
    let upResult := Signal.fst r2
    let r3 := Signal.snd r2
    let downResult := Signal.fst r3
    let r4 := Signal.snd r3
    let savedInput := Signal.fst r4
    let elemResult := Signal.snd r4

    -- Phase decode
    let isIdle      : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isGateBL    : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isGateScale : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isUpBL      : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isUpScale   : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))
    let isReluElem  : Signal dom Bool := phase === (Signal.pure 5#4 : Signal dom (BitVec 4))
    let isDownBL    : Signal dom Bool := phase === (Signal.pure 6#4 : Signal dom (BitVec 4))
    let isDownScale : Signal dom Bool := phase === (Signal.pure 7#4 : Signal dom (BitVec 4))
    let isResid     : Signal dom Bool := phase === (Signal.pure 8#4 : Signal dom (BitVec 4))
    let isDone      : Signal dom Bool := phase === (Signal.pure 9#4 : Signal dom (BitVec 4))

    -- Shared WeightStreamer
    let activeBaseAddr : Signal dom (BitVec 32) :=
      Signal.mux isGateBL gateBaseAddr
        (Signal.mux isUpBL upBaseAddr
          (Signal.mux isDownBL downBaseAddr
            (Signal.pure 0#32 : Signal dom (BitVec 32))))
    let stageGo : Signal dom Bool :=
      Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let streamerOut := weightStreamerBitLinear dim stageGo activeBaseAddr memReadData memReadValid input
    let stageResult := wsResult streamerOut
    let stageDone := wsDone streamerOut

    -- Pipelined Scale (1 cycle latency each)
    let gateAcc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 gateResult
    let gateScaled := scaleMultiplyPipelined gateAcc48 gateScaleVal
    let gateActivated := reluSqPipelined gateScaled

    let upAcc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 upResult
    let upScaled := scaleMultiplyPipelined upAcc48 upScaleVal

    let elemOut := elemMulPipelined gateActivated upScaled

    let downAcc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 downResult
    let downScaled := scaleMultiplyPipelined downAcc48 downScaleVal
    let finalResult := residualAddSignal savedInput downScaled

    -- Phase transitions
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let gateBLDone : Signal dom Bool := Signal.mux isGateBL stageDone (Signal.pure false : Signal dom Bool)
    let upBLDone : Signal dom Bool := Signal.mux isUpBL stageDone (Signal.pure false : Signal dom Bool)
    let downBLDone : Signal dom Bool := Signal.mux isDownBL stageDone (Signal.pure false : Signal dom Bool)

    -- 1-cycle phases auto-advance
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))           -- → GATE_BL
        (Signal.mux gateBLDone (Signal.pure 2#4 : Signal dom (BitVec 4))    -- → GATE_SCALE
          (Signal.mux isGateScale (Signal.pure 3#4 : Signal dom (BitVec 4)) -- → UP_BL
            (Signal.mux upBLDone (Signal.pure 4#4 : Signal dom (BitVec 4))  -- → UP_SCALE
              (Signal.mux isUpScale (Signal.pure 5#4 : Signal dom (BitVec 4))   -- → RELU_ELEMMUL
                (Signal.mux isReluElem (Signal.pure 6#4 : Signal dom (BitVec 4))  -- → DOWN_BL
                  (Signal.mux downBLDone (Signal.pure 7#4 : Signal dom (BitVec 4)) -- → DOWN_SCALE
                    (Signal.mux isDownScale (Signal.pure 8#4 : Signal dom (BitVec 4)) -- → RESID
                      (Signal.mux isResid (Signal.pure 9#4 : Signal dom (BitVec 4))   -- → DONE
                        (Signal.mux isDone
                          (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
                          phase)))))))))

    -- Latch results
    let nextGate : Signal dom (BitVec 32) := Signal.mux gateBLDone stageResult gateResult
    let nextUp : Signal dom (BitVec 32) := Signal.mux upBLDone stageResult upResult
    let nextElem : Signal dom (BitVec 32) := Signal.mux isReluElem elemOut elemResult
    let nextDown : Signal dom (BitVec 32) := Signal.mux isResid finalResult downResult
    let nextInput : Signal dom (BitVec 32) := Signal.mux goIdle input savedInput

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextGate)
        (bundle2
          (Signal.register 0#32 nextUp)
          (bundle2
            (Signal.register 0#32 nextDown)
            (bundle2
              (Signal.register 0#32 nextInput)
              (Signal.register 0#32 nextElem)))))

  -- Extract outputs
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _gateResult := Signal.fst r1
  let r2 := Signal.snd r1
  let _upResult := Signal.fst r2
  let r3 := Signal.snd r2
  let downResult := Signal.fst r3

  let done : Signal dom Bool := phase === (Signal.pure 9#4 : Signal dom (BitVec 4))
  bundle2 downResult (bundle2 done phase)

end Sparkle.IP.BitNet.SoC
