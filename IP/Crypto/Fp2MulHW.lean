/-
  IP.Crypto.Fp2MulHW — BLS12-381 Fp2 multiplication as a
  `circuit do` FSM that drives ONE Fp381 Montgomery multiplier
  (`Fp381MontMulHW.montMulHW`) over a start/done handshake.

  Fp2 = Fp[u]/(u²+1); an element is `c0 + c1·u`.  The product uses
  the 3-multiply Karatsuba form (matching `BLS12_381.Fp2.mul`):

      t0    = a0 · b0
      t1    = a1 · b1
      cross = (a0 + a1) · (b0 + b1)
      c0    = t0 − t1
      c1    = cross − t0 − t1        (= a0·b1 + a1·b0)

  The three multiplies (t0, t1, cross) run on the shared Fp
  multiplier, one at a time, sequenced by a 2-bit step counter.
  The operand sums `a0+a1`, `b0+b1` and the output combinations
  `t0−t1`, `cross−t0−t1` are combinational Fp add/sub mod p.

  All values are in the MONTGOMERY DOMAIN (R = 2^384); add/sub are
  linear so they carry through unchanged, and the Fp multiplier
  already performs the R^-1 folding.  Domain conversion is the
  caller's job (done once at the boundary of a G2 scalar-mul).

  Composition (the synthesizable style the whole stack uses): the
  Fp multiplier is NOT instantiated here — it is driven over the
  exposed `mulStart`/`mulA`/`mulB` ports and its `result`/`done`
  come back through `mulResult`/`mulDone`, wired at the level up.

  Interface:
    inputs  start (Bool pulse)   — latch operands, begin
            a0,a1,b0,b1          — Fp2 operands (BitVec 384, Mont)
            mulResult            — Fp multiplier result in
            mulDone (Bool)       — Fp multiplier done in
    outputs c0Out,c1Out          — Fp2 product (valid at done)
            done (Bool pulse)    — result ready
            mulStart (Bool)      — pulse the Fp multiplier
            mulA,mulB            — operands for the Fp multiplier

  Timing: each Fp multiply is 14 cycles + 2 handshake ≈ 16 cyc/step;
  3 steps ⇒ ~48 cycles/Fp2-mul.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.Fp381MontMulHW

namespace Sparkle.IP.Crypto.Fp2MulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- BLS12-381 base-field prime as a 385-bit constant (headroom for
    a+b and a+p−b combinational reductions, both < 2p < 2^385). -/
def pBv385 : BitVec 385 := BitVec.ofNat 385 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- Output record. -/
structure Fp2MulOut (dom : DomainConfig) where
  /-- Product component c0 (valid at `done`). -/
  c0Out : Signal dom (BitVec 384)
  /-- Product component c1 (valid at `done`). -/
  c1Out : Signal dom (BitVec 384)
  /-- Pulses for one cycle when the Fp2 multiply finishes. -/
  done : Signal dom Bool
  /-- Pulses for one cycle to trigger the external Fp multiplier. -/
  mulStart : Signal dom Bool
  /-- Operand A for the external Fp multiplier. -/
  mulA : Signal dom (BitVec 384)
  /-- Operand B for the external Fp multiplier. -/
  mulB : Signal dom (BitVec 384)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (Fp2MulOut dom) dom := ⟨⟩

/-- Fp add mod p (combinational): widen to 385, add, single
    conditional subtract of p. -/
private def fAddP {dom : DomainConfig}
    (a b : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  let z1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
  let aw := ((· ++ ·) <$> z1 <*> a : Signal dom (BitVec 385))
  let bw := ((· ++ ·) <$> z1 <*> b : Signal dom (BitVec 385))
  let s  := ((· + ·) <$> aw <*> bw : Signal dom (BitVec 385))
  let pP := (Signal.pure pBv385 : Signal dom (BitVec 385))
  let ge := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> pP) s : Signal dom (BitVec 385))
  ((BitVec.extractLsb' 0 384 ·) <$> red : Signal dom (BitVec 384))

/-- Fp sub mod p (combinational): compute a + p − b in 385 bits
    (always in [0, 2p)), then one conditional subtract. -/
private def fSubP {dom : DomainConfig}
    (a b : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  let z1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
  let aw := ((· ++ ·) <$> z1 <*> a : Signal dom (BitVec 385))
  let bw := ((· ++ ·) <$> z1 <*> b : Signal dom (BitVec 385))
  let pP := (Signal.pure pBv385 : Signal dom (BitVec 385))
  let apb := ((· + ·) <$> aw <*> pP : Signal dom (BitVec 385))    -- a + p
  let s   := ((· - ·) <$> apb <*> bw : Signal dom (BitVec 385))   -- a + p − b
  let ge  := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> pP) s : Signal dom (BitVec 385))
  ((BitVec.extractLsb' 0 384 ·) <$> red : Signal dom (BitVec 384))

/-- `stepSig == k` (2-bit step compare). -/
private def stepEq {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 2)) (k : Nat) : Signal dom Bool :=
  ((· == ·) <$> stepSig <*> (Signal.pure (BitVec.ofNat 2 k) : Signal dom (BitVec 2)))

/-- Latch the engine result into scratch `k` on a step-`k` ack. -/
private def latchStep {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 2))
    (engRes : Signal dom (BitVec 384)) (k : Nat)
    (cur : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  Signal.mux ((· && ·) <$> stepAck <*> stepEq stepSig k) engRes cur

/-- Fp2 multiply FSM. -/
def fp2MulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (a0 a1 b0 b1 : Signal dom (BitVec 384))
    (mulResult : Signal dom (BitVec 384))
    (mulDone : Signal dom Bool) :
    Fp2MulOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger, 2 wait, 3 complete.
    let stR ← Signal.reg (0#2)
    -- Step: which of the 3 muls (0=t0, 1=t1, 2=cross).
    let stepR ← Signal.reg (0#2)
    -- Latched operands.
    let a0R ← Signal.reg (0#384)
    let a1R ← Signal.reg (0#384)
    let b0R ← Signal.reg (0#384)
    let b1R ← Signal.reg (0#384)
    -- Scratch for the 3 mul results.
    let m0R ← Signal.reg (0#384)   -- t0 = a0·b0
    let m1R ← Signal.reg (0#384)   -- t1 = a1·b1
    let m2R ← Signal.reg (0#384)   -- cross = (a0+a1)·(b0+b1)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 2))
    let a0S := (a0R : Signal dom (BitVec 384))
    let a1S := (a1R : Signal dom (BitVec 384))
    let b0S := (b0R : Signal dom (BitVec 384))
    let b1S := (b1R : Signal dom (BitVec 384))
    let m0S := (m0R : Signal dom (BitVec 384))
    let m1S := (m1R : Signal dom (BitVec 384))
    let m2S := (m2R : Signal dom (BitVec 384))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_2 := (Signal.pure 0#2 : Signal dom (BitVec 2))

    let isTrig := ((· == ·) <$> stSig <*> p1_2 : Signal dom Bool)
    let isWait := ((· == ·) <$> stSig <*> p2_2 : Signal dom Bool)

    -- Combinational operand sums for the cross product.
    let aSum := fAddP a0S a1S
    let bSum := fAddP b0S b1S

    -- Operand routing per step.
    let engA :=
      (Signal.mux (stepEq stepSig 0) a0S
        (Signal.mux (stepEq stepSig 1) a1S aSum) : Signal dom (BitVec 384))
    let engB :=
      (Signal.mux (stepEq stepSig 0) b0S
        (Signal.mux (stepEq stepSig 1) b1S bSum) : Signal dom (BitVec 384))

    let engRes := mulResult
    let engDone := mulDone

    -- Last step is step 2 (cross).
    let lastStep := stepEq stepSig 2
    let stepAck := ((· && ·) <$> isWait <*> engDone : Signal dom Bool)
    let atLast := ((· && ·) <$> stepAck <*> lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    -- Phase transitions.
    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    -- Step index.
    let stepInc := ((· + ·) <$> stepSig <*> p1_2 : Signal dom (BitVec 2))
    stepR <~ Signal.mux start p0_2
              (Signal.mux advance stepInc stepSig)

    -- Operand latches.
    a0R <~ Signal.mux start a0 a0S
    a1R <~ Signal.mux start a1 a1S
    b0R <~ Signal.mux start b0 b0S
    b1R <~ Signal.mux start b1 b1S

    -- Scratch latches.
    m0R <~ latchStep stepAck stepSig engRes 0 m0S
    m1R <~ latchStep stepAck stepSig engRes 1 m1S
    m2R <~ latchStep stepAck stepSig engRes 2 m2S

    doneR <~ atLast

    -- Outputs (combinational from the latched mul results).
    let c0 := fSubP m0S m1S                 -- t0 − t1
    let c1 := fSubP m2S (fAddP m0S m1S)     -- cross − (t0 + t1)

    return ({ c0Out := c0
            , c1Out := c1
            , done := (doneR : Signal dom Bool)
            , mulStart := isTrig
            , mulA := engA
            , mulB := engB
            } : Fp2MulOut dom)

end Sparkle.IP.Crypto.Fp2MulHW
