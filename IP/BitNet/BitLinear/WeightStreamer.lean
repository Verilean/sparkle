/-
  BitNet BitLinear — Weight Streamer — Signal DSL

  FSM that loads ternary weights from an external memory interface
  into the TimeMux BRAM, triggers computation, and waits for result.

  Orchestrates the full sequence:
    IDLE → LOAD_WEIGHTS (dim cycles) → COMPUTE (dim cycles) → DONE

  External memory interface (simple, AXI-agnostic):
    memReadAddr  : output — address to read (baseAddr + offset)
    memReadData  : input  — 2-bit weight data returned
    memReadValid : input  — data is valid this cycle

  Integration: connect memReadAddr/Data/Valid to an AXI master or
  direct BRAM port. The streamer doesn't care about the transport.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.BitLinear.TimeMux

namespace Sparkle.IP.BitNet.BitLinear

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Weight streamer + TimeMux combo.
    Loads `dim` weights starting from `baseAddr`, then runs BitLinear.

    Inputs:
      go          — pulse to start a new computation
      baseAddr    — starting address for weight reads
      memReadData — 2-bit weight data from memory
      memReadValid— memory read data is valid
      activation  — activation input (must be valid during COMPUTE phase)

    Outputs bundled as (result × (done × (memReadAddr × phase)))
-/
def weightStreamerBitLinear
    (dimLimit : BitVec 16)  -- dim - 1, as a literal
    (go : Signal dom Bool)
    (baseAddr : Signal dom (BitVec 32))
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    (activation : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (Bool × (BitVec 32 × BitVec 4))) :=
  -- Streamer FSM phases: 0=IDLE, 1=LOAD_WEIGHTS, 2=COMPUTE, 3=DONE
  let streamerState := Signal.loop (dom := dom) (α := BitVec 4 × (BitVec 16 × BitVec 32))
    fun (self : Signal dom (BitVec 4 × (BitVec 16 × BitVec 32))) =>
    let phase := Signal.fst self
    let rest := Signal.snd self
    let loadCounter := Signal.fst rest
    let savedBaseAddr := Signal.snd rest

    let isIdle    : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isLoading : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isCompute : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDone    : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    let dimLimit : Signal dom (BitVec 16) :=
      (Signal.pure dimLimit : Signal dom (BitVec 16))
    let loadAtEnd : Signal dom Bool :=
      Signal.mux isLoading
        (Signal.mux memReadValid (loadCounter === dimLimit) (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    -- start/idle transition
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- Next phase
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))        -- IDLE → LOAD
        (Signal.mux loadAtEnd (Signal.pure 2#4 : Signal dom (BitVec 4))  -- LOAD → COMPUTE
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase) -- DONE → restart or stay
            phase))

    -- Load counter: increment on valid read during LOAD
    let loadInc : Signal dom Bool :=
      Signal.mux isLoading memReadValid (Signal.pure false : Signal dom Bool)
    let counterInc : Signal dom (BitVec 16) :=
      loadCounter + (Signal.pure 1#16 : Signal dom (BitVec 16))
    let nextCounter : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux loadInc counterInc loadCounter)

    -- Save base addr on go
    let nextBaseAddr : Signal dom (BitVec 32) :=
      Signal.mux goIdle baseAddr savedBaseAddr

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#16 nextCounter)
        (Signal.register 0#32 nextBaseAddr))

  let streamerPhase := Signal.fst streamerState
  let streamerRest := Signal.snd streamerState
  let loadCounter := Signal.fst streamerRest
  let savedBaseAddr := Signal.snd streamerRest

  let isLoading : Signal dom Bool := streamerPhase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isCompute : Signal dom Bool := streamerPhase === (Signal.pure 2#4 : Signal dom (BitVec 4))
  let isDone    : Signal dom Bool := streamerPhase === (Signal.pure 3#4 : Signal dom (BitVec 4))

  -- Memory read address: baseAddr + loadCounter (during LOAD phase)
  let counterExt : Signal dom (BitVec 32) :=
    loadCounter ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let readAddr : Signal dom (BitVec 32) := savedBaseAddr + counterExt

  -- TimeMux: write weights during LOAD, compute during COMPUTE
  let loadWriteEn : Signal dom Bool :=
    Signal.mux isLoading memReadValid (Signal.pure false : Signal dom Bool)
  let computeStart : Signal dom Bool :=
    Signal.mux isCompute
      -- pulse start on first cycle of COMPUTE (counter == 0 trick: use phase transition)
      (streamerPhase === (Signal.pure 2#4 : Signal dom (BitVec 4)))
      (Signal.pure false : Signal dom Bool)

  let tmState := bitLinearTimeMux dimLimit loadCounter memReadData loadWriteEn computeStart activation
  let result := bitLinearTimeMuxResult tmState
  let tmDone := bitLinearTimeMuxDone tmState

  -- Output
  bundle2 result (bundle2 tmDone (bundle2 readAddr streamerPhase))

/-- Extract result from weight streamer output. -/
def wsResult (out : Signal dom (BitVec 32 × (Bool × (BitVec 32 × BitVec 4))))
    : Signal dom (BitVec 32) := Signal.fst out

/-- Extract done flag. -/
def wsDone (out : Signal dom (BitVec 32 × (Bool × (BitVec 32 × BitVec 4))))
    : Signal dom Bool := Signal.fst (Signal.snd out)

/-- Extract memory read address. -/
def wsMemReadAddr (out : Signal dom (BitVec 32 × (Bool × (BitVec 32 × BitVec 4))))
    : Signal dom (BitVec 32) := Signal.fst (Signal.snd (Signal.snd out))

end Sparkle.IP.BitNet.BitLinear
