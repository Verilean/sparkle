/-
  AXI4 Burst Read Master — Signal DSL (200 MHz)

  Issues a single AXI4 burst read and collects the response beats.
  Designed for HBM weight streaming: 1 burst = 16 beats × 256 bit
  = 512 bytes = 2048 ternary weights.

  FSM: IDLE → ISSUE_AR → WAIT_DATA → DONE

  Interface matches Xilinx HBM IP AXI3 ports:
    - ARADDR  33-bit (8 GB address space)
    - ARLEN   4-bit (0-15 = 1-16 beats, AXI3)
    - ARSIZE  3-bit (5 = 32 bytes per beat)
    - ARBURST 2-bit (1 = INCR)
    - 256-bit RDATA per beat

  For the test primitive, we use 32-bit data width (fits in Signal DSL
  without wide integer complexity). Real HBM uses 256-bit.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Bus.AXI4

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- AXI4 burst read master FSM.
    Issues one burst read of `burstLen` beats (0-indexed, so burstLen=15 → 16 beats).
    Collects response data beat-by-beat.

    Inputs:
      go       — start a burst read
      baseAddr — starting address (32-bit for simplicity)
      arready  — AXI AR channel ready (from slave)
      rdata    — AXI R channel data (from slave)
      rvalid   — AXI R channel valid
      rlast    — AXI R channel last beat

    Returns bundled:
      (araddr × (arvalid × (rready × (beatData × (beatValid × (done × (beatCount × phase)))))))
-/
def axiburstReadMaster
    (burstLen : BitVec 4)   -- number of beats - 1 (e.g. 15 for 16 beats)
    (go : Signal dom Bool)
    (baseAddr : Signal dom (BitVec 32))
    -- AXI slave response
    (arready : Signal dom Bool)
    (rdata : Signal dom (BitVec 32))
    (rvalid : Signal dom Bool)
    (rlast : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (Bool × (BitVec 32 × (Bool × (Bool × (BitVec 4 × BitVec 4))))))) :=
  -- FSM: 0=IDLE, 1=ISSUE_AR, 2=WAIT_DATA, 3=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 4 × BitVec 32)))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 4 × BitVec 32)))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let savedAddr := Signal.fst r1
    let r2 := Signal.snd r1
    let beatCount := Signal.fst r2
    let lastBeatData := Signal.snd r2

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isIssueAR : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isWaitData : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    -- AR accepted
    let arAccepted : Signal dom Bool :=
      Signal.mux isIssueAR arready (Signal.pure false : Signal dom Bool)
    -- Last beat received
    let lastBeat : Signal dom Bool :=
      Signal.mux isWaitData
        (Signal.mux rvalid rlast (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))          -- → ISSUE_AR
        (Signal.mux arAccepted (Signal.pure 2#4 : Signal dom (BitVec 4))   -- → WAIT_DATA
          (Signal.mux lastBeat (Signal.pure 3#4 : Signal dom (BitVec 4))   -- → DONE
            (Signal.mux isDone
              (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
              phase)))

    let nextAddr : Signal dom (BitVec 32) :=
      Signal.mux goIdle baseAddr savedAddr

    -- Beat counter increments on each valid rdata
    let beatInc : Signal dom Bool :=
      Signal.mux isWaitData rvalid (Signal.pure false : Signal dom Bool)
    let nextBeatCount : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 0#4 : Signal dom (BitVec 4))
        (Signal.mux beatInc
          (beatCount + (Signal.pure 1#4 : Signal dom (BitVec 4)))
          beatCount)

    let nextLastData : Signal dom (BitVec 32) :=
      Signal.mux beatInc rdata lastBeatData

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextAddr)
        (bundle2
          (Signal.register 0#4 nextBeatCount)
          (Signal.register 0#32 nextLastData)))

  -- Extract state
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let savedAddr := Signal.fst r1
  let r2 := Signal.snd r1
  let beatCount := Signal.fst r2
  let lastBeatData := Signal.snd r2

  let isIssueAR : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isWaitData : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
  let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

  -- Output signals
  let araddr := savedAddr
  let arvalid := isIssueAR
  let rready := isWaitData
  -- Per-beat output: data + valid (forwarded from AXI R channel)
  let beatData := rdata
  let beatValid : Signal dom Bool :=
    Signal.mux isWaitData rvalid (Signal.pure false : Signal dom Bool)

  bundle2 araddr (bundle2 arvalid (bundle2 rready
    (bundle2 beatData (bundle2 beatValid (bundle2 isDone
      (bundle2 beatCount phase))))))

end Sparkle.IP.Bus.AXI4
