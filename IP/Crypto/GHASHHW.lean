/-
  IP.Crypto.GHASHHW — multi-cycle GF(2^128) multiplier in
  Sparkle Signal DSL.  Targets the GHASH round used inside
  AES-GCM (NIST SP 800-38D §6.3).

  Algorithm: NIST right-shift method, 128 bits per multiply
  (= 128 cycles per multiplier).  Two 128-bit registers
  hold the running accumulator `z` and the shifted operand
  `v`; a third 128-bit register holds the consume-from-MSB
  shifter of the other operand `x`.

  Interface:
    inputs  start (Bool), xIn (BitVec 128), yIn (BitVec 128)
    outputs result (BitVec 128), done (Bool pulse)

  Pipeline:
    cycle 0   — start asserted ⇒ z=0, v=yIn, x=xIn, cnt=0, busy=true
    cycle 1..128 — one bit per cycle
    cycle 129 — done pulses, result valid

  Sparkle sim caveat (Lean 4.28 Nat-backed BitVec for n > 64):
    `result.val k` for k > ~500 takes ~360ms/cycle.  See
    `Sparkle/Core/Signal.lean`'s `loop` doc-block for full
    notes.  Synth (`#synthesizeVerilog`) and FPGA-fit
    (`#verify_fpga`) are unaffected — they're IR-level.
    For interactive validation use:
      * `probe-ghash` exe (this file: one cycle, ~60s)
      * iverilog/Verilator on the emitted SV for many-cycle
        runs

  Cycle-by-cycle sim against the pure-data reference is in
  Tests/IP/Crypto/GHASHHWTest.lean.
-/
import Sparkle
import IP.Crypto.GHASH

namespace Sparkle.IP.Crypto.GHASHHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- The GHASH reduction constant: top byte 0xE1, rest zero.
    Reproduced here as a `BitVec 128` for HW arithmetic. -/
def R : BitVec 128 := Sparkle.IP.Crypto.GHASH.R

/-- Output record. -/
structure GMulOut (dom : DomainConfig) where
  /-- The 128-bit product accumulator. -/
  result : Signal dom (BitVec 128)
  /-- Pulses for one cycle when the multiply finishes
      (cycle 129 after `start`). -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (GMulOut dom) dom := ⟨⟩

/-- One-cycle conditional XOR helper.  Returns `a ^^^ b`
    when `cond` is true, else `a`.  Reducible so the IR
    elaborator unfolds it directly into the Signal.mux. -/
@[reducible, inline] def xorIf {dom : DomainConfig}
    (cond : Signal dom Bool)
    (a b : Signal dom (BitVec 128)) :
    Signal dom (BitVec 128) :=
  Signal.mux cond ((· ^^^ ·) <$> a <*> b) a

/-- Multi-cycle GHASH multiplier.

    `start` is a one-cycle pulse that captures `xIn`/`yIn`
    and resets internal state.  After 128 cycles the `done`
    output pulses and `result` holds the product. -/
def gmulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (xIn yIn : Signal dom (BitVec 128)) :
    GMulOut dom :=
  circuit do
    -- 128-bit accumulator, shifted operand, consumed-from-MSB operand.
    let zR ← Signal.reg (0#128)
    let vR ← Signal.reg (0#128)
    let xR ← Signal.reg (0#128)
    -- 8-bit counter (0..128).
    let cntR ← Signal.reg (0#8)
    -- doneR pulses for one cycle when cnt reaches 128.
    let doneR ← Signal.reg false

    let zSig := (zR : Signal dom (BitVec 128))
    let vSig := (vR : Signal dom (BitVec 128))
    let xSig := (xR : Signal dom (BitVec 128))
    let cntSig := (cntR : Signal dom (BitVec 8))

    -- Constants.
    let p0_8   := (Signal.pure 0#8   : Signal dom (BitVec 8))
    let p1_8   := (Signal.pure 1#8   : Signal dom (BitVec 8))
    let p128_8 := (Signal.pure 128#8 : Signal dom (BitVec 8))
    let pR     := (Signal.pure R     : Signal dom (BitVec 128))

    -- Predicates.
    let isIdle   := (· == ·) <$> cntSig <*> p0_8
    let isFinish := (· == ·) <$> cntSig <*> p128_8
    let busy     := (fun b => !b) <$> ((fun a b => a || b) <$> isIdle <*> isFinish)

    -- One bit per cycle: read top bit of x and low bit of v.
    -- Use Signal-level shift + eq so the IR elaborator can lower
    -- each step to standard ops.  `!=` is not in the synth op
    -- table, so we use `==` against 0 then `!`.
    let p127 := (Signal.pure 127#128 : Signal dom (BitVec 128))
    let p1c  := (Signal.pure 1#128   : Signal dom (BitVec 128))
    let p0c  := (Signal.pure 0#128   : Signal dom (BitVec 128))
    let xHi  := ((· >>> ·) <$> xSig <*> p127 : Signal dom (BitVec 128))
    let vLo  := ((· &&& ·) <$> vSig <*> p1c  : Signal dom (BitVec 128))
    let xHiZ := ((· == ·) <$> xHi <*> p0c : Signal dom Bool)
    let vLoZ := ((· == ·) <$> vLo <*> p0c : Signal dom Bool)
    let xMsbBit := ((fun b => !b) <$> xHiZ : Signal dom Bool)
    let vLsbBit := ((fun b => !b) <$> vLoZ : Signal dom Bool)

    -- z' = z XOR v   if xMsbBit, else z
    let zNext := (xorIf xMsbBit zSig vSig : Signal dom (BitVec 128))
    -- v' = (v >>> 1) XOR R   if vLsbBit, else v >>> 1
    let vShifted :=
      ((· >>> ·) <$> vSig <*> (Signal.pure 1#128 : Signal dom (BitVec 128))
        : Signal dom (BitVec 128))
    let vNext := (xorIf vLsbBit vShifted pR : Signal dom (BitVec 128))
    -- x' = x << 1
    let xNext :=
      ((· <<< ·) <$> xSig <*> (Signal.pure 1#128 : Signal dom (BitVec 128))
        : Signal dom (BitVec 128))
    -- cnt' = cnt + 1
    let cntInc := ((· + ·) <$> cntSig <*> p1_8 : Signal dom (BitVec 8))

    -- Updates:
    --   on start: load xR=xIn, vR=yIn, zR=0, cnt=1, done=false
    --   on busy:  z<-zNext, v<-vNext, x<-xNext, cnt<-cnt+1
    --   on isFinish: done<-true, hold others, cnt<-0
    --   on isIdle: hold

    zR <~ Signal.mux start (Signal.pure 0#128 : Signal dom (BitVec 128))
            (Signal.mux busy zNext zSig)
    vR <~ Signal.mux start yIn
            (Signal.mux busy vNext vSig)
    xR <~ Signal.mux start xIn
            (Signal.mux busy xNext xSig)
    cntR <~ Signal.mux start p1_8
            (Signal.mux isFinish p0_8
              (Signal.mux busy cntInc cntSig))
    doneR <~ isFinish

    return ({ result := zSig
            , done   := (doneR : Signal dom Bool)
            } : GMulOut dom)

/-! ### Multi-block GHASH FSM.

    Wraps `gmulHW` in a state machine that consumes a
    stream of 128-bit blocks and folds them with H:

      Y_0 = 0
      Y_i = (Y_{i-1} XOR X_i) · H

    Caller asserts `start` once with `hIn` set to the hash
    subkey; then on each cycle they assert `blockValid` with
    `blockIn` set to the next 128-bit block.  The FSM
    accepts a block only when `ready` is high (this happens
    every ~129 cycles, after gmulHW has finished the
    previous round).

    `result` always holds the current Y_i (= digest after
    the last accepted block). -/

structure GHashOut (dom : DomainConfig) where
  /-- Current GHASH accumulator (= digest after the last
      consumed block; 0 before any block is consumed). -/
  result : Signal dom (BitVec 128)
  /-- High when the FSM can accept a new block on
      `blockValid`. -/
  ready  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (GHashOut dom) dom := ⟨⟩

/-- Multi-block GHASH HW engine.

    State machine:
      IDLE: ready=1.  On blockValid, fire gmulHW with
                       xIn = y XOR block, yIn = H.  Go to BUSY.
      BUSY: ready=0.  Wait for gmulHW.done; latch y, go to IDLE.

    `start` resets y to 0 and latches `hIn` into the H
    register. -/
def ghashFullHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (hIn blockIn : Signal dom (BitVec 128))
    (blockValid : Signal dom Bool) :
    GHashOut dom :=
  circuit do
    -- Accumulator Y_i and hash subkey H (latched on start).
    let yR ← Signal.reg (0#128)
    let hR ← Signal.reg (0#128)
    -- Single-bit state: false = IDLE (ready), true = BUSY.
    let stateR ← Signal.reg false

    let ySig := (yR : Signal dom (BitVec 128))
    let hSig := (hR : Signal dom (BitVec 128))
    let stSig := (stateR : Signal dom Bool)

    let isIdle := ((fun b => !b) <$> stSig : Signal dom Bool)

    -- Combinational firing signal: in IDLE and caller has
    -- blockValid.
    let fire := ((fun i v => i && v) <$> isIdle <*> blockValid
                   : Signal dom Bool)

    -- Multiplier inputs.  In IDLE+blockValid cycle, xIn = y XOR block;
    -- otherwise the multiplier ignores them (its own start is low).
    let mulX := ((· ^^^ ·) <$> ySig <*> blockIn : Signal dom (BitVec 128))

    -- Inner multi-cycle multiplier.  Driven by `fire` as start
    -- pulse; the engine is independent of our state otherwise.
    let mul := gmulHW fire mulX hSig

    -- y update: on `start`, reset to 0; on mul.done, latch the
    -- product; otherwise hold.
    let p0c := (Signal.pure 0#128 : Signal dom (BitVec 128))
    yR <~ Signal.mux start p0c
            (Signal.mux mul.done mul.result ySig)
    -- H update: latch on start.
    hR <~ Signal.mux start hIn hSig
    -- State: IDLE → BUSY on fire; BUSY → IDLE on mul.done;
    -- `start` forces IDLE.
    stateR <~ Signal.mux start (Signal.pure false : Signal dom Bool)
                (Signal.mux fire (Signal.pure true : Signal dom Bool)
                   (Signal.mux mul.done (Signal.pure false : Signal dom Bool) stSig))

    return ({ result := ySig
            , ready  := isIdle
            } : GHashOut dom)

end Sparkle.IP.Crypto.GHASHHW
