/-
  BitNet BitLinear — Time-Multiplexed Core — Signal DSL

  Sequential ternary BitLinear: processes one weight-activation pair per clock.
  Uses Signal.loop FSM + BRAM for weight storage.

  FSM states:
    IDLE (0): waiting for `start` pulse
    ACCUMULATE (1): processing one element per clock, dim cycles total
    DONE (2): result ready, stays until next `start`
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.BitNet.BitLinear

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Time-multiplexed BitLinear core.
    Returns bundled (phase × (counter × (acc × resultLatch))) state.
    Use `bitLinearTimeMuxResult/Done/Busy/Counter` projections to extract. -/
def bitLinearTimeMux
    (dim : Nat)
    (weightWriteAddr : Signal dom (BitVec 16))
    (weightWriteData : Signal dom (BitVec 2))
    (weightWriteEn : Signal dom Bool)
    (start : Signal dom Bool)
    (activation : Signal dom (BitVec 32))
    : Signal dom (BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32))) :=
  Signal.loop (dom := dom) (α := BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32)))
    fun (self : Signal dom (BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32)))) =>
    -- Destructure state
    let phase := Signal.fst self
    let rest1 := Signal.snd self
    let counter := Signal.fst rest1
    let rest2 := Signal.snd rest1
    let acc := Signal.fst rest2
    let resultLatch := Signal.snd rest2

    -- Weight BRAM: read at counter address
    let weightCode := Signal.memoryComboRead weightWriteAddr weightWriteData weightWriteEn counter

    -- Decode ternary weight
    let isPlus1  : Signal dom Bool := weightCode === (Signal.pure 0b10#2 : Signal dom (BitVec 2))
    let isMinus1 : Signal dom Bool := weightCode === (Signal.pure 0b00#2 : Signal dom (BitVec 2))

    -- MAC: ternary add/sub/skip
    let macResult : Signal dom (BitVec 32) :=
      Signal.mux isPlus1 (acc + activation)
        (Signal.mux isMinus1 (acc - activation) acc)

    -- Dimension limit
    let dimLimit : Signal dom (BitVec 16) := (Signal.pure (BitVec.ofNat 16 (dim - 1)) : Signal dom (BitVec 16))
    let atEnd : Signal dom Bool := counter === dimLimit

    -- FSM decode
    let isIdle  : Signal dom Bool := phase === (Signal.pure 0#2 : Signal dom (BitVec 2))
    let isAccum : Signal dom Bool := phase === (Signal.pure 1#2 : Signal dom (BitVec 2))
    let isDone  : Signal dom Bool := phase === (Signal.pure 2#2 : Signal dom (BitVec 2))

    -- Bool AND via mux
    let startIdle   : Signal dom Bool := Signal.mux isIdle start (Signal.pure false : Signal dom Bool)
    let endAccum    : Signal dom Bool := Signal.mux isAccum atEnd (Signal.pure false : Signal dom Bool)
    let restartDone : Signal dom Bool := Signal.mux isDone start (Signal.pure false : Signal dom Bool)

    -- Next phase
    let nextPhase : Signal dom (BitVec 2) :=
      Signal.mux startIdle (Signal.pure 1#2 : Signal dom (BitVec 2))
        (Signal.mux endAccum (Signal.pure 2#2 : Signal dom (BitVec 2))
          (Signal.mux restartDone (Signal.pure 1#2 : Signal dom (BitVec 2)) phase))

    -- Next counter
    let counterInc : Signal dom (BitVec 16) := counter + (Signal.pure 1#16 : Signal dom (BitVec 16))
    let nextCounter : Signal dom (BitVec 16) :=
      Signal.mux startIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux isAccum counterInc
          (Signal.mux restartDone (Signal.pure 0#16 : Signal dom (BitVec 16)) counter))

    -- Next accumulator
    let nextAcc : Signal dom (BitVec 32) :=
      Signal.mux startIdle (Signal.pure 0#32 : Signal dom (BitVec 32))
        (Signal.mux isAccum macResult
          (Signal.mux restartDone (Signal.pure 0#32 : Signal dom (BitVec 32)) acc))

    -- Latch result when done
    let nextResult : Signal dom (BitVec 32) :=
      Signal.mux endAccum macResult resultLatch

    bundle2
      (Signal.register 0#2 nextPhase)
      (bundle2
        (Signal.register 0#16 nextCounter)
        (bundle2
          (Signal.register 0#32 nextAcc)
          (Signal.register 0#32 nextResult)))

/-- Extract result from time-mux state. -/
def bitLinearTimeMuxResult (state : Signal dom (BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32))))
    : Signal dom (BitVec 32) :=
  Signal.snd (Signal.snd (Signal.snd state))

/-- Extract done flag from time-mux state. -/
def bitLinearTimeMuxDone (state : Signal dom (BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32))))
    : Signal dom Bool :=
  Signal.fst state === (Signal.pure 2#2 : Signal dom (BitVec 2))

/-- Extract counter (= activation read address) from time-mux state. -/
def bitLinearTimeMuxCounter (state : Signal dom (BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32))))
    : Signal dom (BitVec 16) :=
  Signal.fst (Signal.snd state)

end Sparkle.IP.BitNet.BitLinear
