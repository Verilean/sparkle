/-
  HBM Simulation Primitive — Signal DSL

  Test-only AXI slave that simulates HBM behavior:
  - Accepts burst read requests (AR channel)
  - Returns data from an internal BRAM (pre-loaded)
  - Fixed latency: 1 cycle AR accept, 1 cycle per data beat

  This is NOT synthesizable on FPGA — it's for co-simulation testing.
  On real hardware, this is replaced by Xilinx HBM IP instantiation.

  Uses Signal.loop + memoryComboRead for the backing store.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Bus.AXI4

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- HBM simulation primitive.
    Acts as an AXI slave: accepts AR requests, returns data from BRAM.

    Inputs:
      -- AR channel (from master)
      araddr   — read address
      arvalid  — address valid
      arlen    — burst length (0-15)
      -- R channel (from master)
      rready   — master ready to accept data
      -- BRAM pre-load (for test setup)
      preloadAddr — address to write during setup
      preloadData — data to write during setup
      preloadEn   — write enable during setup

    Returns (arready × (rdata × (rvalid × rlast))) -/
def hbmSimPrimitive
    -- AR channel from master
    (araddr : Signal dom (BitVec 32))
    (arvalid : Signal dom Bool)
    (arlen : Signal dom (BitVec 4))
    -- R channel from master
    (rready : Signal dom Bool)
    -- Pre-load port (test setup)
    (preloadAddr : Signal dom (BitVec 16))
    (preloadData : Signal dom (BitVec 32))
    (preloadEn : Signal dom Bool)
    : Signal dom (Bool × (BitVec 32 × (Bool × Bool))) :=
  -- FSM: 0=IDLE (accept AR), 1=SEND_DATA (return beats)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 4 × (BitVec 4 × Bool))))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 4 × (BitVec 4 × Bool))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let currentAddr := Signal.fst r1
    let r2 := Signal.snd r1
    let remainBeats := Signal.fst r2
    let r3 := Signal.snd r2
    let totalBeats := Signal.fst r3
    let sending := Signal.snd r3

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isSending : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))

    -- Accept AR request in IDLE
    let arAccepted : Signal dom Bool :=
      Signal.mux isIdle arvalid (Signal.pure false : Signal dom Bool)

    -- Beat sent when master accepts (rready && sending)
    let beatSent : Signal dom Bool :=
      Signal.mux isSending rready (Signal.pure false : Signal dom Bool)
    let lastBeatSent : Signal dom Bool :=
      Signal.mux beatSent
        (remainBeats === (Signal.pure 0#4 : Signal dom (BitVec 4)))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux arAccepted (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux lastBeatSent (Signal.pure 0#4 : Signal dom (BitVec 4))
          phase)

    -- Address: latch on AR accept, increment on each beat sent
    let nextAddr : Signal dom (BitVec 32) :=
      Signal.mux arAccepted araddr
        (Signal.mux beatSent
          (currentAddr + (Signal.pure 1#32 : Signal dom (BitVec 32)))
          currentAddr)

    -- Remaining beats: load from arlen on accept, decrement on send
    let nextRemain : Signal dom (BitVec 4) :=
      Signal.mux arAccepted arlen
        (Signal.mux beatSent
          (remainBeats - (Signal.pure 1#4 : Signal dom (BitVec 4)))
          remainBeats)

    let nextTotal : Signal dom (BitVec 4) :=
      Signal.mux arAccepted arlen totalBeats

    let nextSending : Signal dom Bool :=
      Signal.mux arAccepted (Signal.pure true : Signal dom Bool)
        (Signal.mux lastBeatSent (Signal.pure false : Signal dom Bool) sending)

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextAddr)
        (bundle2
          (Signal.register 0#4 nextRemain)
          (bundle2
            (Signal.register 0#4 nextTotal)
            (Signal.register false nextSending))))

  -- Extract state
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let currentAddr := Signal.fst r1
  let r2 := Signal.snd r1
  let remainBeats := Signal.fst r2
  let r3 := Signal.snd r2
  let _totalBeats := Signal.fst r3
  let sending := Signal.snd r3

  let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
  let isSending : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))

  -- Backing BRAM: written during preload, read at currentAddr during send
  let readAddr : Signal dom (BitVec 16) :=
    Signal.map (BitVec.extractLsb' 0 16 ·) currentAddr
  let bramData := Signal.memoryComboRead preloadAddr preloadData preloadEn readAddr

  -- AXI output signals
  let arready := isIdle                    -- accept AR when idle
  let rdata := bramData                    -- data from BRAM
  let rvalid := sending                    -- valid when sending beats
  let rlast : Signal dom Bool :=           -- last beat of burst
    Signal.mux isSending
      (remainBeats === (Signal.pure 0#4 : Signal dom (BitVec 4)))
      (Signal.pure false : Signal dom Bool)

  bundle2 arready (bundle2 rdata (bundle2 rvalid rlast))

end Sparkle.IP.Bus.AXI4
