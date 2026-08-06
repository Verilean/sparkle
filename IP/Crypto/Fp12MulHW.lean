/-
  IP.Crypto.Fp12MulHW — BLS12-381 Fp12 multiplication as a
  `circuit do` FSM that drives ONE Fp6 multiplier
  (`Fp6MulHW.fp6MulHW`) over a start/done handshake.

  Fp12 = Fp6[w]/(w² - v).  An element is `c0 + c1·w` with each cᵢ ∈ Fp6
  (= 3 Fp2 = 6 BitVec 384), so an Fp12 value is 12 BitVec-384 signals.

  The product uses the Karatsuba form (matching `BLS12_381.Fp12.mul`):

      v0    = a0·b0
      v1    = a1·b1
      cross = (a0+a1)·(b0+b1)
      c0    = v0 + v·v1              (v = Fp6.mulByV, combinational)
      c1    = cross - v0 - v1

  The three Fp6 multiplies run on the shared Fp6 multiplier, one at a
  time, sequenced by a 2-bit step counter.  `Fp6.mulByV`, the operand
  sums and the output combinations are combinational Fp6 add/sub over
  the six BitVec-384 halves (carry through the Montgomery domain).

  Composition: the Fp6 multiplier is NOT instantiated here — it is
  driven over the exposed `f6Start` + 12 operand ports and its 6
  result coords + `done` come back through the `f6C*`/`f6Done` ports,
  wired at the level up (which itself drives an Fp2 mul, which drives
  the Fp381 Montgomery mul).

  Timing: each Fp6 multiply is ~300 cycles; 3 steps ⇒ ~900 cyc/Fp12-mul.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.Fp6MulHW

namespace Sparkle.IP.Crypto.Fp12MulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- BLS12-381 base-field prime as a 385-bit constant. -/
def pBv385 : BitVec 385 := BitVec.ofNat 385 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- Output record.  Two Fp6 coordinates (c0, c1); each Fp6 is three
    Fp2 pairs, so 12 BitVec-384 signals total.  Names: `c<hi><coord><half>`
    where hi ∈ {0,1} is the w-degree, coord ∈ {0,1,2} the Fp6 index,
    half ∈ {a,b} the Fp2 u-part. -/
structure Fp12MulOut (dom : DomainConfig) where
  c00a : Signal dom (BitVec 384)
  c00b : Signal dom (BitVec 384)
  c01a : Signal dom (BitVec 384)
  c01b : Signal dom (BitVec 384)
  c02a : Signal dom (BitVec 384)
  c02b : Signal dom (BitVec 384)
  c10a : Signal dom (BitVec 384)
  c10b : Signal dom (BitVec 384)
  c11a : Signal dom (BitVec 384)
  c11b : Signal dom (BitVec 384)
  c12a : Signal dom (BitVec 384)
  c12b : Signal dom (BitVec 384)
  done : Signal dom Bool
  /-- Trigger + 12 operands for the external Fp6 multiplier
      (operand A = a0a..a2b, operand B = b0a..b2b). -/
  f6Start : Signal dom Bool
  f6A0a : Signal dom (BitVec 384)
  f6A0b : Signal dom (BitVec 384)
  f6A1a : Signal dom (BitVec 384)
  f6A1b : Signal dom (BitVec 384)
  f6A2a : Signal dom (BitVec 384)
  f6A2b : Signal dom (BitVec 384)
  f6B0a : Signal dom (BitVec 384)
  f6B0b : Signal dom (BitVec 384)
  f6B1a : Signal dom (BitVec 384)
  f6B1b : Signal dom (BitVec 384)
  f6B2a : Signal dom (BitVec 384)
  f6B2b : Signal dom (BitVec 384)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (Fp12MulOut dom) dom := ⟨⟩

/-- Fp add mod p (combinational). -/
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

/-- Fp sub mod p (combinational). -/
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

/-- `stepSig == k` (2-bit step compare). -/
private def stepEq {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 2)) (k : Nat) : Signal dom Bool :=
  (stepSig === (Signal.pure (BitVec.ofNat 2 k) : Signal dom (BitVec 2)))

/-- Latch an engine result half into scratch `k` on a step-`k` ack. -/
private def latchStep {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 2))
    (engRes : Signal dom (BitVec 384)) (k : Nat)
    (cur : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  Signal.mux (stepAck &&& stepEq stepSig k) engRes cur

/-- Fp12 multiply FSM. -/
def fp12MulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    -- operand A = a0 + a1·w; each Fp6 = 3 Fp2 pairs (a0: a00..a02, a1: a10..a12)
    (a00a a00b a01a a01b a02a a02b : Signal dom (BitVec 384))
    (a10a a10b a11a a11b a12a a12b : Signal dom (BitVec 384))
    (b00a b00b b01a b01b b02a b02b : Signal dom (BitVec 384))
    (b10a b10b b11a b11b b12a b12b : Signal dom (BitVec 384))
    -- Fp6-mul result (6 coords) + done from the sub-engine.
    (f6R0a f6R0b f6R1a f6R1b f6R2a f6R2b : Signal dom (BitVec 384))
    (f6Done : Signal dom Bool) :
    Fp12MulOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger, 2 wait, 3 complete.
    let stR ← Signal.reg (0#2)
    -- Step: which of the 3 Fp6-muls (0=v0, 1=v1, 2=cross).
    let stepR ← Signal.reg (0#2)
    -- Latched operands (2 Fp6 each, a and b: 12 + 12 regs).
    let a00aR ← Signal.reg (0#384); let a00bR ← Signal.reg (0#384)
    let a01aR ← Signal.reg (0#384); let a01bR ← Signal.reg (0#384)
    let a02aR ← Signal.reg (0#384); let a02bR ← Signal.reg (0#384)
    let a10aR ← Signal.reg (0#384); let a10bR ← Signal.reg (0#384)
    let a11aR ← Signal.reg (0#384); let a11bR ← Signal.reg (0#384)
    let a12aR ← Signal.reg (0#384); let a12bR ← Signal.reg (0#384)
    let b00aR ← Signal.reg (0#384); let b00bR ← Signal.reg (0#384)
    let b01aR ← Signal.reg (0#384); let b01bR ← Signal.reg (0#384)
    let b02aR ← Signal.reg (0#384); let b02bR ← Signal.reg (0#384)
    let b10aR ← Signal.reg (0#384); let b10bR ← Signal.reg (0#384)
    let b11aR ← Signal.reg (0#384); let b11bR ← Signal.reg (0#384)
    let b12aR ← Signal.reg (0#384); let b12bR ← Signal.reg (0#384)
    -- Scratch for v0, v1, cross (each an Fp6 = 6 halves).
    let v00aR ← Signal.reg (0#384); let v00bR ← Signal.reg (0#384)
    let v01aR ← Signal.reg (0#384); let v01bR ← Signal.reg (0#384)
    let v02aR ← Signal.reg (0#384); let v02bR ← Signal.reg (0#384)
    let v10aR ← Signal.reg (0#384); let v10bR ← Signal.reg (0#384)
    let v11aR ← Signal.reg (0#384); let v11bR ← Signal.reg (0#384)
    let v12aR ← Signal.reg (0#384); let v12bR ← Signal.reg (0#384)
    let cr0aR ← Signal.reg (0#384); let cr0bR ← Signal.reg (0#384)
    let cr1aR ← Signal.reg (0#384); let cr1bR ← Signal.reg (0#384)
    let cr2aR ← Signal.reg (0#384); let cr2bR ← Signal.reg (0#384)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 2))
    -- operand signal views
    let a00aS := (a00aR : Signal dom (BitVec 384)); let a00bS := (a00bR : Signal dom (BitVec 384))
    let a01aS := (a01aR : Signal dom (BitVec 384)); let a01bS := (a01bR : Signal dom (BitVec 384))
    let a02aS := (a02aR : Signal dom (BitVec 384)); let a02bS := (a02bR : Signal dom (BitVec 384))
    let a10aS := (a10aR : Signal dom (BitVec 384)); let a10bS := (a10bR : Signal dom (BitVec 384))
    let a11aS := (a11aR : Signal dom (BitVec 384)); let a11bS := (a11bR : Signal dom (BitVec 384))
    let a12aS := (a12aR : Signal dom (BitVec 384)); let a12bS := (a12bR : Signal dom (BitVec 384))
    let b00aS := (b00aR : Signal dom (BitVec 384)); let b00bS := (b00bR : Signal dom (BitVec 384))
    let b01aS := (b01aR : Signal dom (BitVec 384)); let b01bS := (b01bR : Signal dom (BitVec 384))
    let b02aS := (b02aR : Signal dom (BitVec 384)); let b02bS := (b02bR : Signal dom (BitVec 384))
    let b10aS := (b10aR : Signal dom (BitVec 384)); let b10bS := (b10bR : Signal dom (BitVec 384))
    let b11aS := (b11aR : Signal dom (BitVec 384)); let b11bS := (b11bR : Signal dom (BitVec 384))
    let b12aS := (b12aR : Signal dom (BitVec 384)); let b12bS := (b12bR : Signal dom (BitVec 384))
    let v00aS := (v00aR : Signal dom (BitVec 384)); let v00bS := (v00bR : Signal dom (BitVec 384))
    let v01aS := (v01aR : Signal dom (BitVec 384)); let v01bS := (v01bR : Signal dom (BitVec 384))
    let v02aS := (v02aR : Signal dom (BitVec 384)); let v02bS := (v02bR : Signal dom (BitVec 384))
    let v10aS := (v10aR : Signal dom (BitVec 384)); let v10bS := (v10bR : Signal dom (BitVec 384))
    let v11aS := (v11aR : Signal dom (BitVec 384)); let v11bS := (v11bR : Signal dom (BitVec 384))
    let v12aS := (v12aR : Signal dom (BitVec 384)); let v12bS := (v12bR : Signal dom (BitVec 384))
    let cr0aS := (cr0aR : Signal dom (BitVec 384)); let cr0bS := (cr0bR : Signal dom (BitVec 384))
    let cr1aS := (cr1aR : Signal dom (BitVec 384)); let cr1bS := (cr1bR : Signal dom (BitVec 384))
    let cr2aS := (cr2aR : Signal dom (BitVec 384)); let cr2bS := (cr2bR : Signal dom (BitVec 384))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_2 := (Signal.pure 0#2 : Signal dom (BitVec 2))

    let isTrig := (stSig === p1_2 : Signal dom Bool)
    let isWait := (stSig === p2_2 : Signal dom Bool)

    -- Combinational Fp6 operand sums for the cross step (a0+a1, b0+b1).
    let sa0a := fAddP a00aS a10aS; let sa0b := fAddP a00bS a10bS
    let sa1a := fAddP a01aS a11aS; let sa1b := fAddP a01bS a11bS
    let sa2a := fAddP a02aS a12aS; let sa2b := fAddP a02bS a12bS
    let sb0a := fAddP b00aS b10aS; let sb0b := fAddP b00bS b10bS
    let sb1a := fAddP b01aS b11aS; let sb1b := fAddP b01bS b11bS
    let sb2a := fAddP b02aS b12aS; let sb2b := fAddP b02bS b12bS

    -- Operand routing per step: step0 = (a0,b0), step1 = (a1,b1),
    -- step2 = (a0+a1, b0+b1).  Each is an Fp6 (6 halves).
    let selA0a := (Signal.mux (stepEq stepSig 0) a00aS (Signal.mux (stepEq stepSig 1) a10aS sa0a) : Signal dom (BitVec 384))
    let selA0b := (Signal.mux (stepEq stepSig 0) a00bS (Signal.mux (stepEq stepSig 1) a10bS sa0b) : Signal dom (BitVec 384))
    let selA1a := (Signal.mux (stepEq stepSig 0) a01aS (Signal.mux (stepEq stepSig 1) a11aS sa1a) : Signal dom (BitVec 384))
    let selA1b := (Signal.mux (stepEq stepSig 0) a01bS (Signal.mux (stepEq stepSig 1) a11bS sa1b) : Signal dom (BitVec 384))
    let selA2a := (Signal.mux (stepEq stepSig 0) a02aS (Signal.mux (stepEq stepSig 1) a12aS sa2a) : Signal dom (BitVec 384))
    let selA2b := (Signal.mux (stepEq stepSig 0) a02bS (Signal.mux (stepEq stepSig 1) a12bS sa2b) : Signal dom (BitVec 384))
    let selB0a := (Signal.mux (stepEq stepSig 0) b00aS (Signal.mux (stepEq stepSig 1) b10aS sb0a) : Signal dom (BitVec 384))
    let selB0b := (Signal.mux (stepEq stepSig 0) b00bS (Signal.mux (stepEq stepSig 1) b10bS sb0b) : Signal dom (BitVec 384))
    let selB1a := (Signal.mux (stepEq stepSig 0) b01aS (Signal.mux (stepEq stepSig 1) b11aS sb1a) : Signal dom (BitVec 384))
    let selB1b := (Signal.mux (stepEq stepSig 0) b01bS (Signal.mux (stepEq stepSig 1) b11bS sb1b) : Signal dom (BitVec 384))
    let selB2a := (Signal.mux (stepEq stepSig 0) b02aS (Signal.mux (stepEq stepSig 1) b12aS sb2a) : Signal dom (BitVec 384))
    let selB2b := (Signal.mux (stepEq stepSig 0) b02bS (Signal.mux (stepEq stepSig 1) b12bS sb2b) : Signal dom (BitVec 384))

    let engDone := f6Done
    let lastStep := stepEq stepSig 2
    let stepAck := (isWait &&& engDone : Signal dom Bool)
    let atLast := (stepAck &&& lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    let stepInc := (stepSig + p1_2 : Signal dom (BitVec 2))
    stepR <~ Signal.mux start p0_2
              (Signal.mux advance stepInc stepSig)

    -- Operand latches.
    a00aR <~ Signal.mux start a00a a00aS; a00bR <~ Signal.mux start a00b a00bS
    a01aR <~ Signal.mux start a01a a01aS; a01bR <~ Signal.mux start a01b a01bS
    a02aR <~ Signal.mux start a02a a02aS; a02bR <~ Signal.mux start a02b a02bS
    a10aR <~ Signal.mux start a10a a10aS; a10bR <~ Signal.mux start a10b a10bS
    a11aR <~ Signal.mux start a11a a11aS; a11bR <~ Signal.mux start a11b a11bS
    a12aR <~ Signal.mux start a12a a12aS; a12bR <~ Signal.mux start a12b a12bS
    b00aR <~ Signal.mux start b00a b00aS; b00bR <~ Signal.mux start b00b b00bS
    b01aR <~ Signal.mux start b01a b01aS; b01bR <~ Signal.mux start b01b b01bS
    b02aR <~ Signal.mux start b02a b02aS; b02bR <~ Signal.mux start b02b b02bS
    b10aR <~ Signal.mux start b10a b10aS; b10bR <~ Signal.mux start b10b b10bS
    b11aR <~ Signal.mux start b11a b11aS; b11bR <~ Signal.mux start b11b b11bS
    b12aR <~ Signal.mux start b12a b12aS; b12bR <~ Signal.mux start b12b b12bS

    -- Scratch latches: step 0 → v0, step 1 → v1, step 2 → cross.
    v00aR <~ latchStep stepAck stepSig f6R0a 0 v00aS; v00bR <~ latchStep stepAck stepSig f6R0b 0 v00bS
    v01aR <~ latchStep stepAck stepSig f6R1a 0 v01aS; v01bR <~ latchStep stepAck stepSig f6R1b 0 v01bS
    v02aR <~ latchStep stepAck stepSig f6R2a 0 v02aS; v02bR <~ latchStep stepAck stepSig f6R2b 0 v02bS
    v10aR <~ latchStep stepAck stepSig f6R0a 1 v10aS; v10bR <~ latchStep stepAck stepSig f6R0b 1 v10bS
    v11aR <~ latchStep stepAck stepSig f6R1a 1 v11aS; v11bR <~ latchStep stepAck stepSig f6R1b 1 v11bS
    v12aR <~ latchStep stepAck stepSig f6R2a 1 v12aS; v12bR <~ latchStep stepAck stepSig f6R2b 1 v12bS
    cr0aR <~ latchStep stepAck stepSig f6R0a 2 cr0aS; cr0bR <~ latchStep stepAck stepSig f6R0b 2 cr0bS
    cr1aR <~ latchStep stepAck stepSig f6R1a 2 cr1aS; cr1bR <~ latchStep stepAck stepSig f6R1b 2 cr1bS
    cr2aR <~ latchStep stepAck stepSig f6R2a 2 cr2aS; cr2bR <~ latchStep stepAck stepSig f6R2b 2 cr2bS

    doneR <~ atLast

    -- Output combine (combinational Fp6 ops):
    --   c0 = v0 + mulByV(v1);  mulByV(x) = ⟨Xi(x.c2), x.c0, x.c1⟩,
    --      Xi(y0 + y1·u) = (y0 − y1) + (y0 + y1)·u.
    let mv0a := fSubP v12aS v12bS   -- Xi(v1.c2).c0 = v1.c2.a − v1.c2.b
    let mv0b := fAddP v12aS v12bS   -- Xi(v1.c2).c1 = v1.c2.a + v1.c2.b
    let mv1a := v10aS; let mv1b := v10bS  -- v1.c0
    let mv2a := v11aS; let mv2b := v11bS  -- v1.c1
    let c00a := fAddP v00aS mv0a; let c00b := fAddP v00bS mv0b
    let c01a := fAddP v01aS mv1a; let c01b := fAddP v01bS mv1b
    let c02a := fAddP v02aS mv2a; let c02b := fAddP v02bS mv2b
    --   c1 = cross − v0 − v1  (per Fp6 coordinate/half)
    let c10a := fSubP (fSubP cr0aS v00aS) v10aS; let c10b := fSubP (fSubP cr0bS v00bS) v10bS
    let c11a := fSubP (fSubP cr1aS v01aS) v11aS; let c11b := fSubP (fSubP cr1bS v01bS) v11bS
    let c12a := fSubP (fSubP cr2aS v02aS) v12aS; let c12b := fSubP (fSubP cr2bS v02bS) v12bS

    return ({ c00a := c00a, c00b := c00b, c01a := c01a, c01b := c01b, c02a := c02a, c02b := c02b
            , c10a := c10a, c10b := c10b, c11a := c11a, c11b := c11b, c12a := c12a, c12b := c12b
            , done := (doneR : Signal dom Bool)
            , f6Start := isTrig
            , f6A0a := selA0a, f6A0b := selA0b, f6A1a := selA1a, f6A1b := selA1b
            , f6A2a := selA2a, f6A2b := selA2b
            , f6B0a := selB0a, f6B0b := selB0b, f6B1a := selB1a, f6B1b := selB1b
            , f6B2a := selB2a, f6B2b := selB2b
            } : Fp12MulOut dom)

end Sparkle.IP.Crypto.Fp12MulHW
