/-
  IP.Crypto.ModInvHW — Fermat modular inverse (a^(m-2) mod m)
  by square-and-multiply, reusing an external field multiplier
  over a start/done handshake.

  Algorithm (right-to-left / LSB-first square-and-multiply of the
  exponent `e = m - 2`):

      result = 1
      b      = a
      for i = 0 .. 255:
        if bit_i(e):  result = mul(result, b)   -- mod m
        b = mul(b, b)                            -- mod m
      return result                              -- = a^e mod m

  Because the *wired-in* multiplier reduces mod whatever modulus
  the caller chooses (mod p for `Secp256k1FieldHW.mulHW`, mod n for
  the order multiplier), this engine is **modulus-agnostic**: the
  caller decides mod-p vs mod-n by which multiplier it wires across
  the handshake ports, and passes `expBits = m - 2` for that
  modulus.  A plain `1` is a valid identity in either modulus'
  domain (both are ordinary residues, not Montgomery form).

  Sequencing.  There is ONE shared multiplier port, so the two
  multiplies per bit are issued as two separate engine invocations:

      phase 1  issue  the (optional) result*b multiply
      phase 2  wait   for it   → latch into result (only if bit set)
      phase 3  issue  the b*b (square)
      phase 4  wait   for it   → latch into b, advance bit index

  When `bit_i(e) = 0` the result-multiply phases (1,2) still run a
  multiply but the result register is simply not updated — this
  keeps the FSM's timing data-independent (constant-time), which
  is desirable for a signer.

  Composition.  Like `Secp256k1PointOpHW`, this module does NOT
  instantiate the multiplier (a record-returning sub-module, which
  `#synthesizeVerilog` rejects when projected).  It exposes
  `mulStart`/`mulA`/`mulB` outputs and takes `mulResult`/`mulDone`
  inputs; the caller wires one `mulHW` across those ports.

  Interface:
    inputs  start (Bool pulse)      — latch a + expBits, begin
            aIn (BitVec 256)        — the value to invert
            expBits (BitVec 256)    — the exponent m-2 (LSB-first scan)
            mulResult (BitVec 256)  — field-multiplier result in
            mulDone (Bool)          — field-multiplier done in
    outputs result (BitVec 256)     — a^(m-2) mod m (valid at done)
            done (Bool pulse)       — result ready
            mulStart (Bool)         — pulse the multiplier
            mulA,mulB (BitVec 256)  — operands for the multiplier

  Cost ≈ 256 bits · 2 multiplies/bit · ~258 cyc/mul ≈ 132 k cycles
  per inverse with the bit-serial multiplier.
-/
import Sparkle
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1FieldHW

namespace Sparkle.IP.Crypto.ModInvHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output record. -/
structure ModInvOut (dom : DomainConfig) where
  /-- a^(m-2) mod m (valid when `done` pulses). -/
  result : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the inverse finishes. -/
  done   : Signal dom Bool
  /-- Pulse to trigger the external multiplier. -/
  mulStart : Signal dom Bool
  /-- Multiplier operand A. -/
  mulA : Signal dom (BitVec 256)
  /-- Multiplier operand B. -/
  mulB : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ModInvOut dom) dom := ⟨⟩

/-- Bit `i` of a 256-bit signal, as a Bool (i supplied as a BitVec
    256 so it feeds the shifter directly). -/
private def bitAt {dom : DomainConfig}
    (v : Signal dom (BitVec 256)) (iSig : Signal dom (BitVec 256)) :
    Signal dom Bool :=
  let sh := ((· >>> ·) <$> v <*> iSig : Signal dom (BitVec 256))
  let lo := (sh.map (fun x => x &&& 1#256) : Signal dom (BitVec 256))
  ((· == ·) <$> lo <*> (Signal.pure 1#256 : Signal dom (BitVec 256)))

/-- Fermat modular-inverse FSM. -/
def modInvHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (aIn : Signal dom (BitVec 256))
    (expBits : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256))
    (mulDone : Signal dom Bool) :
    ModInvOut dom :=
  circuit do
    -- Phase: 0 idle, 1 issue result-mul, 2 wait result-mul,
    --        3 issue square, 4 wait square, 5 complete.
    let phR ← Signal.reg (0#3)
    -- Bit index i, counts 0 upward to 255 (stored as BitVec 256 to
    -- feed the shifter directly).
    let biR ← Signal.reg (0#256)
    -- Latched exponent.
    let eR ← Signal.reg (0#256)
    -- Accumulator `result` (starts at 1).
    let resR ← Signal.reg (1#256)
    -- Running base `b` (starts at a).
    let bR ← Signal.reg (0#256)
    -- Done pulse.
    let doneR ← Signal.reg false

    let phSig  := (phR : Signal dom (BitVec 3))
    let biSig  := (biR : Signal dom (BitVec 256))
    let eSig   := (eR : Signal dom (BitVec 256))
    let resSig := (resR : Signal dom (BitVec 256))
    let bSig   := (bR : Signal dom (BitVec 256))

    -- Phase constants.
    let ph1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let ph2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let ph3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let ph4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let ph5 := (Signal.pure 5#3 : Signal dom (BitVec 3))

    let isResIssue := ((· == ·) <$> phSig <*> ph1 : Signal dom Bool)
    let isResWait  := ((· == ·) <$> phSig <*> ph2 : Signal dom Bool)
    let isSqIssue  := ((· == ·) <$> phSig <*> ph3 : Signal dom Bool)
    let isSqWait   := ((· == ·) <$> phSig <*> ph4 : Signal dom Bool)

    -- Current exponent bit.
    let bit := bitAt eSig biSig

    -- Multiplier operands: on the result-mul phase feed (result, b);
    -- on the square phase feed (b, b).
    let mulA := (Signal.mux isSqIssue bSig resSig : Signal dom (BitVec 256))
    let mulB := bSig
    -- Trigger the multiplier at either issue phase.
    let mulStart := ((· || ·) <$> isResIssue <*> isSqIssue : Signal dom Bool)

    -- Acks: the multiply completed in the corresponding wait phase.
    let resAck := ((· && ·) <$> isResWait <*> mulDone : Signal dom Bool)
    let sqAck  := ((· && ·) <$> isSqWait <*> mulDone : Signal dom Bool)

    -- Are we at the last bit (i = 255)?
    let atLast := ((· == ·) <$> biSig <*> (Signal.pure 255#256 : Signal dom (BitVec 256))
                    : Signal dom Bool)

    -- result register: on start ⇒ 1; on resAck with bit set ⇒ mulResult.
    let wrRes := ((· && ·) <$> resAck <*> bit : Signal dom Bool)
    resR <~ Signal.mux start (Signal.pure 1#256 : Signal dom (BitVec 256))
              (Signal.mux wrRes mulResult resSig)

    -- b register: on start ⇒ a; on sqAck ⇒ mulResult (the square).
    bR <~ Signal.mux start aIn
            (Signal.mux sqAck mulResult bSig)

    -- Phase sequencing:
    --   start        ⇒ 1 (issue result-mul), bi = 0
    --   isResIssue   ⇒ 2 (wait result-mul)
    --   resAck       ⇒ 3 (issue square)
    --   isSqIssue    ⇒ 4 (wait square)
    --   sqAck & i<255 ⇒ 1 (next bit), bi++
    --   sqAck & i=255 ⇒ 5 (complete)
    let nextBit := ((fun s l => s && !l) <$> sqAck <*> atLast : Signal dom Bool)
    let finish  := ((· && ·) <$> sqAck <*> atLast : Signal dom Bool)

    phR <~ Signal.mux start ph1
             (Signal.mux isResIssue ph2
               (Signal.mux resAck ph3
                 (Signal.mux isSqIssue ph4
                   (Signal.mux nextBit ph1
                     (Signal.mux finish ph5 phSig)))))

    let biInc := ((· + ·) <$> biSig <*> (Signal.pure 1#256 : Signal dom (BitVec 256))
                    : Signal dom (BitVec 256))
    biR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
             (Signal.mux nextBit biInc biSig)

    -- Latch exponent on start.
    eR <~ Signal.mux start expBits eSig

    -- Done pulse when finishing the last bit.
    doneR <~ finish

    return ({ result := resSig
            , done := (doneR : Signal dom Bool)
            , mulStart := mulStart
            , mulA := mulA
            , mulB := mulB
            } : ModInvOut dom)

end Sparkle.IP.Crypto.ModInvHW
