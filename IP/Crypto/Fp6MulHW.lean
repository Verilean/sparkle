/-
  IP.Crypto.Fp6MulHW — BLS12-381 Fp6 multiplication as a
  `circuit do` FSM that drives ONE Fp2 multiplier
  (`Fp2MulHW.fp2MulHW`) over a start/done handshake.

  Fp6 = Fp2[v]/(v³ - ξ), ξ = u+1.  An element is `c0 + c1·v + c2·v²`,
  with each cᵢ ∈ Fp2 carried as a pair of BitVec 384 (Montgomery).

  The product uses the Karatsuba form (matching `BLS12_381.Fp6.mul`):

      v0 = a0·b0
      v1 = a1·b1
      v2 = a2·b2
      m3 = (a1+a2)·(b1+b2)
      m4 = (a0+a1)·(b0+b1)
      m5 = (a0+a2)·(b0+b2)
      c0 = v0 + ξ·(m3 - v1 - v2)
      c1 = (m4 - v0 - v1) + ξ·v2
      c2 = (m5 - v0 - v2) + v1

  The six Fp2 multiplies run on the shared Fp2 multiplier, one at a
  time, sequenced by a 3-bit step counter.  The operand sums and the
  output combinations are combinational Fp2 add/sub/mulByXi (each is
  componentwise on the two BitVec-384 halves, so they carry through
  the Montgomery domain unchanged).

  Composition (the synthesizable style the whole stack uses): the Fp2
  multiplier is NOT instantiated here — it is driven over the exposed
  `fp2Start`/`fp2A0`/`fp2A1`/`fp2B0`/`fp2B1` ports and its
  `c0Out`/`c1Out`/`done` come back through `fp2C0`/`fp2C1`/`fp2Done`,
  wired at the level up.

  Timing: each Fp2 multiply is ~48 cycles + 2 handshake ≈ 50 cyc/step;
  6 steps ⇒ ~300 cycles/Fp6-mul.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.Fp2MulHW

namespace Sparkle.IP.Crypto.Fp6MulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- BLS12-381 base-field prime as a 385-bit constant (headroom for
    combinational reductions, < 2p < 2^385). -/
def pBv385 : BitVec 385 := BitVec.ofNat 385 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- Output record.  Three Fp2 coordinates as six BitVec-384 signals. -/
structure Fp6MulOut (dom : DomainConfig) where
  /-- c0 = low(c0) + high(c0)·u. -/
  c0aOut : Signal dom (BitVec 384)
  c0bOut : Signal dom (BitVec 384)
  /-- c1. -/
  c1aOut : Signal dom (BitVec 384)
  c1bOut : Signal dom (BitVec 384)
  /-- c2. -/
  c2aOut : Signal dom (BitVec 384)
  c2bOut : Signal dom (BitVec 384)
  /-- Pulses for one cycle when the Fp6 multiply finishes. -/
  done : Signal dom Bool
  /-- Pulses for one cycle to trigger the external Fp2 multiplier. -/
  fp2Start : Signal dom Bool
  /-- Operand A (a0 + a1·u) for the external Fp2 multiplier. -/
  fp2A0 : Signal dom (BitVec 384)
  fp2A1 : Signal dom (BitVec 384)
  /-- Operand B for the external Fp2 multiplier. -/
  fp2B0 : Signal dom (BitVec 384)
  fp2B1 : Signal dom (BitVec 384)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (Fp6MulOut dom) dom := ⟨⟩

/-- Fp add mod p (combinational): widen to 385, add, single
    conditional subtract of p. -/
private def fAddP {dom : DomainConfig}
    (a b : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  let z1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
  let aw := (z1 ++ a : Signal dom (BitVec 385))
  let bw := (z1 ++ b : Signal dom (BitVec 385))
  let s  := (aw + bw : Signal dom (BitVec 385))
  let pP := (Signal.pure pBv385 : Signal dom (BitVec 385))
  let ge := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - pP) s : Signal dom (BitVec 385))
  ((BitVec.extractLsb' 0 384 ·) <$> red : Signal dom (BitVec 384))

/-- Fp sub mod p (combinational): a + p − b in 385 bits, one
    conditional subtract. -/
private def fSubP {dom : DomainConfig}
    (a b : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  let z1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
  let aw := (z1 ++ a : Signal dom (BitVec 385))
  let bw := (z1 ++ b : Signal dom (BitVec 385))
  let pP := (Signal.pure pBv385 : Signal dom (BitVec 385))
  let apb := (aw + pP : Signal dom (BitVec 385))
  let s   := (apb - bw : Signal dom (BitVec 385))
  let ge  := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - pP) s : Signal dom (BitVec 385))
  ((BitVec.extractLsb' 0 384 ·) <$> red : Signal dom (BitVec 384))

/-- `stepSig == k` (3-bit step compare). -/
private def stepEq {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 3)) (k : Nat) : Signal dom Bool :=
  (stepSig === (Signal.pure (BitVec.ofNat 3 k) : Signal dom (BitVec 3)))

/-- Latch the engine result half into scratch `k` on a step-`k` ack. -/
private def latchStep {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 3))
    (engRes : Signal dom (BitVec 384)) (k : Nat)
    (cur : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  Signal.mux (stepAck &&& stepEq stepSig k) engRes cur

/-- Fp6 multiply FSM. -/
def fp6MulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (a0a a0b a1a a1b a2a a2b : Signal dom (BitVec 384))
    (b0a b0b b1a b1b b2a b2b : Signal dom (BitVec 384))
    (fp2C0 fp2C1 : Signal dom (BitVec 384))
    (fp2Done : Signal dom Bool) :
    Fp6MulOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger, 2 wait, 3 complete.
    let stR ← Signal.reg (0#2)
    -- Step: which of the 6 Fp2-muls (0..5).
    let stepR ← Signal.reg (0#3)
    -- Latched operands (3 Fp2 coords each, a and b).
    let a0aR ← Signal.reg (0#384); let a0bR ← Signal.reg (0#384)
    let a1aR ← Signal.reg (0#384); let a1bR ← Signal.reg (0#384)
    let a2aR ← Signal.reg (0#384); let a2bR ← Signal.reg (0#384)
    let b0aR ← Signal.reg (0#384); let b0bR ← Signal.reg (0#384)
    let b1aR ← Signal.reg (0#384); let b1bR ← Signal.reg (0#384)
    let b2aR ← Signal.reg (0#384); let b2bR ← Signal.reg (0#384)
    -- Scratch for the 6 Fp2-mul results (each an Fp2 = a+b·u).
    let v0aR ← Signal.reg (0#384); let v0bR ← Signal.reg (0#384)
    let v1aR ← Signal.reg (0#384); let v1bR ← Signal.reg (0#384)
    let v2aR ← Signal.reg (0#384); let v2bR ← Signal.reg (0#384)
    let m3aR ← Signal.reg (0#384); let m3bR ← Signal.reg (0#384)
    let m4aR ← Signal.reg (0#384); let m4bR ← Signal.reg (0#384)
    let m5aR ← Signal.reg (0#384); let m5bR ← Signal.reg (0#384)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 3))
    let a0aS := (a0aR : Signal dom (BitVec 384)); let a0bS := (a0bR : Signal dom (BitVec 384))
    let a1aS := (a1aR : Signal dom (BitVec 384)); let a1bS := (a1bR : Signal dom (BitVec 384))
    let a2aS := (a2aR : Signal dom (BitVec 384)); let a2bS := (a2bR : Signal dom (BitVec 384))
    let b0aS := (b0aR : Signal dom (BitVec 384)); let b0bS := (b0bR : Signal dom (BitVec 384))
    let b1aS := (b1aR : Signal dom (BitVec 384)); let b1bS := (b1bR : Signal dom (BitVec 384))
    let b2aS := (b2aR : Signal dom (BitVec 384)); let b2bS := (b2bR : Signal dom (BitVec 384))
    let v0aS := (v0aR : Signal dom (BitVec 384)); let v0bS := (v0bR : Signal dom (BitVec 384))
    let v1aS := (v1aR : Signal dom (BitVec 384)); let v1bS := (v1bR : Signal dom (BitVec 384))
    let v2aS := (v2aR : Signal dom (BitVec 384)); let v2bS := (v2bR : Signal dom (BitVec 384))
    let m3aS := (m3aR : Signal dom (BitVec 384)); let m3bS := (m3bR : Signal dom (BitVec 384))
    let m4aS := (m4aR : Signal dom (BitVec 384)); let m4bS := (m4bR : Signal dom (BitVec 384))
    let m5aS := (m5aR : Signal dom (BitVec 384)); let m5bS := (m5bR : Signal dom (BitVec 384))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_3 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let p1_3 := (Signal.pure 1#3 : Signal dom (BitVec 3))

    let isTrig := (stSig === p1_2 : Signal dom Bool)
    let isWait := (stSig === p2_2 : Signal dom Bool)

    -- Combinational operand sums for the cross-product steps.
    let s12a := fAddP a1aS a2aS; let s12b := fAddP a1bS a2bS  -- a1+a2
    let t12a := fAddP b1aS b2aS; let t12b := fAddP b1bS b2bS  -- b1+b2
    let s01a := fAddP a0aS a1aS; let s01b := fAddP a0bS a1bS  -- a0+a1
    let t01a := fAddP b0aS b1aS; let t01b := fAddP b0bS b1bS  -- b0+b1
    let s02a := fAddP a0aS a2aS; let s02b := fAddP a0bS a2bS  -- a0+a2
    let t02a := fAddP b0aS b2aS; let t02b := fAddP b0bS b2bS  -- b0+b2

    -- Operand routing per step (each an Fp2 pair).
    let engA0 :=
      (Signal.mux (stepEq stepSig 0) a0aS
        (Signal.mux (stepEq stepSig 1) a1aS
          (Signal.mux (stepEq stepSig 2) a2aS
            (Signal.mux (stepEq stepSig 3) s12a
              (Signal.mux (stepEq stepSig 4) s01a s02a)))) : Signal dom (BitVec 384))
    let engA1 :=
      (Signal.mux (stepEq stepSig 0) a0bS
        (Signal.mux (stepEq stepSig 1) a1bS
          (Signal.mux (stepEq stepSig 2) a2bS
            (Signal.mux (stepEq stepSig 3) s12b
              (Signal.mux (stepEq stepSig 4) s01b s02b)))) : Signal dom (BitVec 384))
    let engB0 :=
      (Signal.mux (stepEq stepSig 0) b0aS
        (Signal.mux (stepEq stepSig 1) b1aS
          (Signal.mux (stepEq stepSig 2) b2aS
            (Signal.mux (stepEq stepSig 3) t12a
              (Signal.mux (stepEq stepSig 4) t01a t02a)))) : Signal dom (BitVec 384))
    let engB1 :=
      (Signal.mux (stepEq stepSig 0) b0bS
        (Signal.mux (stepEq stepSig 1) b1bS
          (Signal.mux (stepEq stepSig 2) b2bS
            (Signal.mux (stepEq stepSig 3) t12b
              (Signal.mux (stepEq stepSig 4) t01b t02b)))) : Signal dom (BitVec 384))

    let engDone := fp2Done

    let lastStep := stepEq stepSig 5
    let stepAck := (isWait &&& engDone : Signal dom Bool)
    let atLast := (stepAck &&& lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    -- Phase transitions.
    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    -- Step index.
    let stepInc := (stepSig + p1_3 : Signal dom (BitVec 3))
    stepR <~ Signal.mux start p0_3
              (Signal.mux advance stepInc stepSig)

    -- Operand latches.
    a0aR <~ Signal.mux start a0a a0aS; a0bR <~ Signal.mux start a0b a0bS
    a1aR <~ Signal.mux start a1a a1aS; a1bR <~ Signal.mux start a1b a1bS
    a2aR <~ Signal.mux start a2a a2aS; a2bR <~ Signal.mux start a2b a2bS
    b0aR <~ Signal.mux start b0a b0aS; b0bR <~ Signal.mux start b0b b0bS
    b1aR <~ Signal.mux start b1a b1aS; b1bR <~ Signal.mux start b1b b1bS
    b2aR <~ Signal.mux start b2a b2aS; b2bR <~ Signal.mux start b2b b2bS

    -- Scratch latches (both Fp2 halves per step).
    v0aR <~ latchStep stepAck stepSig fp2C0 0 v0aS; v0bR <~ latchStep stepAck stepSig fp2C1 0 v0bS
    v1aR <~ latchStep stepAck stepSig fp2C0 1 v1aS; v1bR <~ latchStep stepAck stepSig fp2C1 1 v1bS
    v2aR <~ latchStep stepAck stepSig fp2C0 2 v2aS; v2bR <~ latchStep stepAck stepSig fp2C1 2 v2bS
    m3aR <~ latchStep stepAck stepSig fp2C0 3 m3aS; m3bR <~ latchStep stepAck stepSig fp2C1 3 m3bS
    m4aR <~ latchStep stepAck stepSig fp2C0 4 m4aS; m4bR <~ latchStep stepAck stepSig fp2C1 4 m4bS
    m5aR <~ latchStep stepAck stepSig fp2C0 5 m5aS; m5bR <~ latchStep stepAck stepSig fp2C1 5 m5bS

    doneR <~ atLast

    -- Combinational output combine (Fp2 ops on the latched results).
    -- Fp2.mulByXi (x0 + x1·u) = (x0 − x1) + (x0 + x1)·u.
    -- c0 = v0 + Xi(m3 − v1 − v2)
    let t0a := fSubP (fSubP m3aS v1aS) v2aS
    let t0b := fSubP (fSubP m3bS v1bS) v2bS
    let xi0a := fSubP t0a t0b
    let xi0b := fAddP t0a t0b
    let c0a := fAddP v0aS xi0a
    let c0b := fAddP v0bS xi0b
    -- c1 = (m4 − v0 − v1) + Xi(v2)
    let t1a := fSubP (fSubP m4aS v0aS) v1aS
    let t1b := fSubP (fSubP m4bS v0bS) v1bS
    let xiv2a := fSubP v2aS v2bS
    let xiv2b := fAddP v2aS v2bS
    let c1a := fAddP t1a xiv2a
    let c1b := fAddP t1b xiv2b
    -- c2 = (m5 − v0 − v2) + v1
    let t2a := fSubP (fSubP m5aS v0aS) v2aS
    let t2b := fSubP (fSubP m5bS v0bS) v2bS
    let c2a := fAddP t2a v1aS
    let c2b := fAddP t2b v1bS

    return ({ c0aOut := c0a, c0bOut := c0b
            , c1aOut := c1a, c1bOut := c1b
            , c2aOut := c2a, c2bOut := c2b
            , done := (doneR : Signal dom Bool)
            , fp2Start := isTrig
            , fp2A0 := engA0, fp2A1 := engA1
            , fp2B0 := engB0, fp2B1 := engB1
            } : Fp6MulOut dom)

end Sparkle.IP.Crypto.Fp6MulHW
