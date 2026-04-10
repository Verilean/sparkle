/-
  BitNet SoC — Sequential FFN Layer — Signal DSL

  Full FFN block via time-multiplexed BitLinear:
    input → gate_BL → scale → ReLU² ──┐
         → up_BL   → scale ────────────┤
                                        ▼
                                   ElemMul(gate, up)
                                        │
                                   down_BL → scale → ResidualAdd(input, down)

  Each BitLinear runs sequentially (dim cycles). Scale/ReLU²/ElemMul/ResidualAdd
  are combinational (1 cycle each, negligible vs dim).

  Top-level FSM sequences the three BitLinear stages via WeightStreamer.

  For simplicity, gate and up paths run sequentially (not parallel).
  Parallel execution would halve latency but double BRAM — future optimization.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.BitLinear.WeightStreamer
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Sequential FFN layer using time-multiplexed BitLinear.

    Inputs:
      go         — pulse to start
      input      — input activation (32-bit Q16.16)
      gateBaseAddr, upBaseAddr, downBaseAddr — weight memory addresses
      gateScale, upScale, downScale — Q8.24 scale constants
      memReadData, memReadValid — external memory response

    The FSM sequences: gate_BL → up_BL → down_BL with combinational
    scale/ReLU²/ElemMul/ResidualAdd between stages.

    Returns (result × (done × (memReadAddr × phase))) -/
def ffnLayerSeq
    (dim : Nat)
    (go : Signal dom Bool)
    (input : Signal dom (BitVec 32))
    -- Weight base addresses for 3 BitLinear paths
    (gateBaseAddr upBaseAddr downBaseAddr : Signal dom (BitVec 32))
    -- Scale constants (compile-time known, passed as signals)
    (gateScaleVal upScaleVal downScaleVal : Signal dom (BitVec 32))
    -- External memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 32 × BitVec 4))) :=
  -- Master FSM: 0=IDLE, 1=GATE_BL, 2=UP_BL, 3=DOWN_BL, 4=DONE
  let masterState := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) =>
    let masterPhase := Signal.fst self
    let rest1 := Signal.snd self
    let gateResult := Signal.fst rest1
    let rest2 := Signal.snd rest1
    let upResult := Signal.fst rest2
    let rest3 := Signal.snd rest2
    let downResult := Signal.fst rest3
    let savedInput := Signal.snd rest3

    let isIdle    : Signal dom Bool := masterPhase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isGateBL  : Signal dom Bool := masterPhase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isUpBL    : Signal dom Bool := masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDownBL  : Signal dom Bool := masterPhase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isDone    : Signal dom Bool := masterPhase === (Signal.pure 4#4 : Signal dom (BitVec 4))

    -- WeightStreamer for current active stage
    -- All 3 stages share the same memory interface; only the active one drives
    -- For now: select baseAddr based on phase
    let activeBaseAddr : Signal dom (BitVec 32) :=
      Signal.mux isGateBL gateBaseAddr
        (Signal.mux isUpBL upBaseAddr
          (Signal.mux isDownBL downBaseAddr
            (Signal.pure 0#32 : Signal dom (BitVec 32))))

    -- Active stage start: pulse on phase transition
    -- Gate starts when go from IDLE, up starts when gate done, etc.
    -- We use a single shared WeightStreamer and re-trigger it
    let stageGo : Signal dom Bool :=
      Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- The shared streamer
    let streamerOut := weightStreamerBitLinear dimLimit stageGo activeBaseAddr memReadData memReadValid input
    let stageResult := wsResult streamerOut
    let stageDone := wsDone streamerOut

    -- Gate path: BL result → signExtend → scale → ReLU²
    let gateAcc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 gateResult
    let gateScaleExt : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 gateScaleVal
    let gateScaled48 : Signal dom (BitVec 48) := gateAcc48 * gateScaleExt
    let gateScaled : Signal dom (BitVec 32) := Signal.map (BitVec.extractLsb' 24 32 ·) gateScaled48
    let gateActivated := reluSqSignal gateScaled

    -- Up path: BL result → signExtend → scale
    let upAcc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 upResult
    let upScaleExt : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 upScaleVal
    let upScaled48 : Signal dom (BitVec 48) := upAcc48 * upScaleExt
    let upScaled : Signal dom (BitVec 32) := Signal.map (BitVec.extractLsb' 24 32 ·) upScaled48

    -- ElemMul: gate × up
    let elemResult := elemMulSignal gateActivated upScaled

    -- Down path: BL input is elemResult (but we use single-element for now)
    -- Down scale
    let downAcc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 downResult
    let downScaleExt : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 downScaleVal
    let downScaled48 : Signal dom (BitVec 48) := downAcc48 * downScaleExt
    let downScaled : Signal dom (BitVec 32) := Signal.map (BitVec.extractLsb' 24 32 ·) downScaled48

    -- ResidualAdd: input + down
    let finalResult := residualAddSignal savedInput downScaled

    -- Phase transitions
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let gateBLDone : Signal dom Bool := Signal.mux isGateBL stageDone (Signal.pure false : Signal dom Bool)
    let upBLDone : Signal dom Bool := Signal.mux isUpBL stageDone (Signal.pure false : Signal dom Bool)
    let downBLDone : Signal dom Bool := Signal.mux isDownBL stageDone (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))         -- → GATE_BL
        (Signal.mux gateBLDone (Signal.pure 2#4 : Signal dom (BitVec 4))  -- → UP_BL
          (Signal.mux upBLDone (Signal.pure 3#4 : Signal dom (BitVec 4))  -- → DOWN_BL
            (Signal.mux downBLDone (Signal.pure 4#4 : Signal dom (BitVec 4)) -- → DONE
              (Signal.mux isDone
                (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) masterPhase)
                masterPhase))))

    -- Latch results at each stage completion
    let nextGateResult : Signal dom (BitVec 32) :=
      Signal.mux gateBLDone stageResult gateResult
    let nextUpResult : Signal dom (BitVec 32) :=
      Signal.mux upBLDone stageResult upResult
    let nextDownResult : Signal dom (BitVec 32) :=
      Signal.mux downBLDone finalResult downResult  -- latch final after residual add
    let nextSavedInput : Signal dom (BitVec 32) :=
      Signal.mux goIdle input savedInput

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextGateResult)
        (bundle2
          (Signal.register 0#32 nextUpResult)
          (bundle2
            (Signal.register 0#32 nextDownResult)
            (Signal.register 0#32 nextSavedInput))))

  -- Extract outputs
  let masterPhase := Signal.fst masterState
  let rest1 := Signal.snd masterState
  let _gateResult := Signal.fst rest1
  let rest2 := Signal.snd rest1
  let _upResult := Signal.fst rest2
  let rest3 := Signal.snd rest2
  let downResult := Signal.fst rest3
  let _savedInput := Signal.snd rest3

  let done : Signal dom Bool := masterPhase === (Signal.pure 4#4 : Signal dom (BitVec 4))
  let memAddr := wsMemReadAddr (weightStreamerBitLinear dimLimit
    (Signal.mux (masterPhase === (Signal.pure 0#4 : Signal dom (BitVec 4))) go (Signal.pure false : Signal dom Bool))
    (Signal.mux (masterPhase === (Signal.pure 1#4 : Signal dom (BitVec 4))) gateBaseAddr
      (Signal.mux (masterPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))) upBaseAddr downBaseAddr))
    memReadData memReadValid input)

  bundle2 downResult (bundle2 done (bundle2 memAddr masterPhase))

end Sparkle.IP.BitNet.SoC
