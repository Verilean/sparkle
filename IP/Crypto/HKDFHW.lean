/-
  IP.Crypto.HKDFHW — HKDF-Expand counter datapath (Signal DSL).

  HKDF-Expand (RFC 5869 §2.3) is a counter loop:

      T(0) = ∅
      T(i) = HMAC(PRK, T(i-1) ‖ info ‖ octet(i))

  The SHA-specific/HMAC-specific piece is delegated to the
  SHA-256 HW engine (or an external HMAC-SHA-256 combinator);
  what's *HKDF-specific* is:

    * the block counter `i` (1..N),
    * gating the previous T(i-1) into the HMAC input for i ≥ 2,
    * concatenating info + counter byte on each round,
    * emitting T(i) chunks to an output stream until L bytes
      have been produced.

  This module implements the counter + T-block latching FSM:

      inputs  start (Bool pulse)          — clear all state
              blockDone (Bool)            — HMAC output valid
              blockIn (BitVec 256)        — the latest T(i)
              nBlocks (BitVec 8)          — number of expand
                                            rounds (up to 255,
                                            i.e. 32*255 = 8160 B)
      outputs counter    (BitVec 8)       — current i (1..N)
              tPrev      (BitVec 256)     — T(i-1) to feed HMAC
              hmacTrig   (Bool)           — pulse the HMAC each
                                            round after start
              done       (Bool)           — final T emitted
              round      (BitVec 8)       — current round index

  Behaviourally, on `start`:
    * cycle 1..N: emit a round pulse, wait for blockDone,
      latch blockIn into tPrev, increment counter.
    * cycle when counter > N: assert done.

  This is compact because HMAC is a plug-in — the elaborator
  can synthesise the counter/T-block/done FSM cleanly without
  hauling in SHA-256.
-/
import Sparkle
import IP.Crypto.Codec.HKDF

namespace Sparkle.IP.Crypto.HKDFHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output record. -/
structure HkdfExpandOut (dom : DomainConfig) where
  /-- Current round index (1..nBlocks). -/
  counter    : Signal dom (BitVec 8)
  /-- T(i-1) — feeds the HMAC message on rounds ≥ 2. -/
  tPrev      : Signal dom (BitVec 256)
  /-- Pulse asking the external HMAC-SHA-256 to run one round. -/
  hmacTrig   : Signal dom Bool
  /-- High when all rounds complete and the last T has been latched. -/
  done       : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HkdfExpandOut dom) dom := ⟨⟩

/-- HKDF-Expand counter FSM.

    `start`   pulses at cycle 0 to reset state.
    `nBlocks` latched on `start` = N (number of rounds).
    `blockIn`, `blockDone` are the external HMAC handshake.

    The FSM issues `hmacTrig` for one cycle per round, then
    waits for `blockDone`, latches `blockIn` into `tPrev`,
    and either advances or completes. -/
def hkdfExpandHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (nBlocks : Signal dom (BitVec 8))
    (blockIn : Signal dom (BitVec 256))
    (blockDone : Signal dom Bool) :
    HkdfExpandOut dom :=
  circuit do
    -- Round counter i (0 = idle before start; 1..N during work).
    let cntR ← Signal.reg (0#8)
    -- T(i-1) accumulator.
    let tR ← Signal.reg (0#256)
    -- Latched nBlocks.
    let nR ← Signal.reg (0#8)
    -- FSM state: 0 = idle, 1 = triggering hmac, 2 = waiting for done, 3 = complete.
    let stR ← Signal.reg (0#2)
    -- Done flag (sticky after last round).
    let doneR ← Signal.reg false

    let cntSig := (cntR : Signal dom (BitVec 8))
    let tSig := (tR : Signal dom (BitVec 256))
    let nSig := (nR : Signal dom (BitVec 8))
    let stSig := (stR : Signal dom (BitVec 2))
    let doneSig := (doneR : Signal dom Bool)

    -- Constants.
    let p0_8   := (Signal.pure 0#8 : Signal dom (BitVec 8))
    let p1_8   := (Signal.pure 1#8 : Signal dom (BitVec 8))
    let p0_2   := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let p1_2   := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2   := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2   := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_256 := (Signal.pure 0#256 : Signal dom (BitVec 256))

    let isIdle   := (stSig === p0_2 : Signal dom Bool)
    let isTrig   := (stSig === p1_2 : Signal dom Bool)
    let isWait   := (stSig === p2_2 : Signal dom Bool)
    let isDone   := (stSig === p3_2 : Signal dom Bool)

    -- The current round is complete when we're waiting AND blockDone arrives.
    let waitAck := (isWait &&& blockDone : Signal dom Bool)

    -- After latching a T, if the counter reached nBlocks we're done;
    -- else move to the next round.
    let atLast := (cntSig === nSig : Signal dom Bool)

    -- hmacTrig: pulse in the isTrig state.
    let hmacTrig := isTrig

    -- Register updates.
    -- State transitions:
    --   start ⇒ isTrig, cnt=1, t=0
    --   isTrig  → isWait (one cycle later)
    --   isWait & blockDone: cnt < N ⇒ isTrig, cnt++, latch t
    --                        cnt = N ⇒ isDone, latch t
    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux waitAck
                  (Signal.mux atLast p3_2 p1_2)
                  stSig))

    -- cntR update.
    let cntInc := (cntSig + p1_8 : Signal dom (BitVec 8))
    -- On start ⇒ 1.  On waitAck & not last ⇒ cnt+1.  On isDone ⇒ hold.
    let advanceCnt := ((fun w a => w && !a) <$> waitAck <*> atLast : Signal dom Bool)
    cntR <~ Signal.mux start p1_8
              (Signal.mux advanceCnt cntInc cntSig)

    -- tR update: on start ⇒ 0.  On waitAck ⇒ latch blockIn.  Else hold.
    tR <~ Signal.mux start p0_256
            (Signal.mux waitAck blockIn tSig)

    -- nR update: on start ⇒ latch nBlocks.
    nR <~ Signal.mux start nBlocks nSig

    -- doneR: sticky after entering isDone.
    let enterDone := (waitAck &&& atLast : Signal dom Bool)
    doneR <~ Signal.mux start (Signal.pure false : Signal dom Bool)
              (Signal.mux enterDone (Signal.pure true : Signal dom Bool) doneSig)

    -- (`isIdle` and `isDone` are computed above but unused in
    --  the final outputs; the elaborator will DCE them.)

    return ({ counter  := cntSig
            , tPrev    := tSig
            , hmacTrig := hmacTrig
            , done     := doneSig
            } : HkdfExpandOut dom)

end Sparkle.IP.Crypto.HKDFHW
