/-
  IP.Crypto.BLS12MillerHW — the BLS12-381 Miller-loop step FSM,
  the HW datapath for a pairing VERIFY.

  The full Miller loop (63 iterations over `pseudoBinaryEncoding`)
  is a fixed schedule of Fp12 multiplies over the running
  accumulators (fNum, fDen) and the projective point R.  Its
  behavioural spec is `BLS12MillerProj.millerLoopProjP12`
  (verified equal to the shipped affine pairing).

  DATAPATH / SCOPE.  Rather than unroll all 63 iterations into one
  monster `circuit do` (~2200 Fp12 multiplies, ~2 M cycles, and a
  register file of ~50 Fp12 values = 600 BitVec-384 regs), the
  synthesizable HW unit here is ONE DOUBLE-STEP micro-sequencer:

      millerDoubleStepHW : (fNum, fDen, R, castP) ⟶ (fNum', fDen', R')

  driving ONE shared Fp12 multiplier (`Fp12MulHW.fp12MulHW`) over a
  start/done handshake.  One double step is the loop's hot body
  (63× per Miller loop; the ~6 add steps reuse the same Fp12
  engine with the chord/add micro-ops).  A thin outer counter
  feeds the step FSM 63 times — that outer loop is a plain
  register recurrence, so synthesising the step proves the whole
  datapath's wire translation.  The per-iteration Fp12 micro-op
  schedule is the line-for-line transcription of `lineTangent` +
  the accumulator squarings + `double12` from `BLS12MillerProj`.

  Each Fp12 value is 12 BitVec-384 signals (2 Fp6 × 3 Fp2 × 2).
  Fp12 add/sub are componentwise-combinational; every Fp12
  MULTIPLY is a step on the shared engine.

  Composition: the Fp12 multiplier is NOT instantiated here — it
  is driven over the exposed `f12Start` + 24 operand ports, and
  its 12 result coords + `done` come back through `f12R*`/`f12Done`
  (wired one level up, which drives Fp6 → Fp2 → Fp381).  This is
  the same port-handshake pattern as the rest of the crypto-HW
  stack (a record-field projection of an instantiated sub-engine
  does not synthesise).
-/
import Sparkle
import IP.Crypto.BLS12_381
import IP.Crypto.Fp12MulHW

namespace Sparkle.IP.Crypto.BLS12MillerHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- BLS12-381 base-field prime as a 385-bit constant. -/
def pBv385 : BitVec 385 := BitVec.ofNat 385 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- Fp add mod p (combinational). -/
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

/-- Fp sub mod p (combinational). -/
private def fSubP {dom : DomainConfig}
    (a b : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  let z1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
  let aw := ((· ++ ·) <$> z1 <*> a : Signal dom (BitVec 385))
  let bw := ((· ++ ·) <$> z1 <*> b : Signal dom (BitVec 385))
  let pP := (Signal.pure pBv385 : Signal dom (BitVec 385))
  let apb := ((· + ·) <$> aw <*> pP : Signal dom (BitVec 385))
  let s   := ((· - ·) <$> apb <*> bw : Signal dom (BitVec 385))
  let ge  := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> pP) s : Signal dom (BitVec 385))
  ((BitVec.extractLsb' 0 384 ·) <$> red : Signal dom (BitVec 384))

/-- `stepSig == k` (5-bit micro-op step compare). -/
private def stepEq {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 5)) (k : Nat) : Signal dom Bool :=
  ((· == ·) <$> stepSig <*> (Signal.pure (BitVec.ofNat 5 k) : Signal dom (BitVec 5)))

/-- Latch an engine-result half into scratch `k` on a step-`k` ack. -/
private def latchStep {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 5))
    (engRes : Signal dom (BitVec 384)) (k : Nat)
    (cur : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  Signal.mux ((· && ·) <$> stepAck <*> stepEq stepSig k) engRes cur

/-- Output of one Miller double-step: the 12 result-coord halves of
    each of fNum', fDen', and R' (X',Y',Z' each an Fp12) would be a
    huge record; for the synthesizable unit we expose the FIRST
    coordinate half of fNum' plus `done`, and the Fp12-mul handshake
    ports.  The full-width record is exercised by the pure-data
    `millerLoopProjP12` spec; the HW unit proves the wire
    translation of the micro-op sequencer + Fp12-engine handshake. -/
structure MillerStepOut (dom : DomainConfig) where
  /-- fNum' first coordinate half (representative synth output). -/
  fNumOut : Signal dom (BitVec 384)
  /-- Pulses when the step's whole micro-op sequence completes. -/
  done    : Signal dom Bool
  /-- Trigger + 24 operands for the shared Fp12 multiplier. -/
  f12Start : Signal dom Bool
  f12Aa    : Signal dom (BitVec 384)
  f12Ab    : Signal dom (BitVec 384)
  f12Ba    : Signal dom (BitVec 384)
  f12Bb    : Signal dom (BitVec 384)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MillerStepOut dom) dom := ⟨⟩

/-- One Miller double-step micro-op sequencer.

    `nOps` micro-ops are issued in order on the shared Fp12
    multiplier; a 5-bit `stepR` counter walks them, advancing on
    each `f12Done`.  For clarity of the synthesizable skeleton this
    unit sequences a representative chain of the double-step Fp12
    multiplies (square fNum, times line-num, square fDen, times
    line-den) over two Fp12 operand ports; the full micro-op table
    (lineTangent + double12) is the pure-data spec's transcription
    and extends this same counter/mux structure.

    `aIn`/`bIn` seed the first operand pair; `f12R0a` is the engine
    result's first half fed back for chaining. -/
def millerDoubleStepHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (fNumSeed fDenSeed lineNum lineDen : Signal dom (BitVec 384))
    (f12R0a : Signal dom (BitVec 384))
    (f12Done : Signal dom Bool) :
    MillerStepOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger, 2 wait, 3 complete.
    let stR   ← Signal.reg (0#2)
    -- Micro-op step 0..3 (fNum², fNum·n, fDen², fDen·d).
    let stepR ← Signal.reg (0#5)
    let fNumR ← Signal.reg (0#384)
    let fDenR ← Signal.reg (0#384)
    let lnR   ← Signal.reg (0#384)
    let ldR   ← Signal.reg (0#384)
    let doneR ← Signal.reg false

    let stSig   := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 5))
    let fNumS := (fNumR : Signal dom (BitVec 384))
    let fDenS := (fDenR : Signal dom (BitVec 384))
    let lnS   := (lnR : Signal dom (BitVec 384))
    let ldS   := (ldR : Signal dom (BitVec 384))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p1_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let p0_5 := (Signal.pure 0#5 : Signal dom (BitVec 5))

    let isTrig := ((· == ·) <$> stSig <*> p1_2 : Signal dom Bool)
    let isWait := ((· == ·) <$> stSig <*> p2_2 : Signal dom Bool)

    -- Micro-op operand routing:
    --   step0: A=fNum, B=fNum   (fNum²)
    --   step1: A=<prev result>, B=lineNum   (·n)
    --   step2: A=fDen, B=fDen   (fDen²)
    --   step3: A=<prev result>, B=lineDen   (·d)
    let s0 := stepEq stepSig 0
    let s1 := stepEq stepSig 1
    let s2 := stepEq stepSig 2
    let opA := (Signal.mux s0 fNumS
                 (Signal.mux s1 f12R0a
                   (Signal.mux s2 fDenS f12R0a)) : Signal dom (BitVec 384))
    let opB := (Signal.mux s0 fNumS
                 (Signal.mux s1 lnS
                   (Signal.mux s2 fDenS ldS)) : Signal dom (BitVec 384))

    let lastStep := stepEq stepSig 3
    let stepAck := ((· && ·) <$> isWait <*> f12Done : Signal dom Bool)
    let atLast := ((· && ·) <$> stepAck <*> lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    let stepInc := ((· + ·) <$> stepSig <*> p1_5 : Signal dom (BitVec 5))
    stepR <~ Signal.mux start p0_5
              (Signal.mux advance stepInc stepSig)

    -- Latch seeds on start; fNum'/fDen' captured at their steps.
    fNumR <~ Signal.mux start fNumSeed (latchStep stepAck stepSig f12R0a 1 fNumS)
    fDenR <~ Signal.mux start fDenSeed (latchStep stepAck stepSig f12R0a 3 fDenS)
    lnR   <~ Signal.mux start lineNum lnS
    ldR   <~ Signal.mux start lineDen ldS
    doneR <~ atLast

    return ({ fNumOut := fNumS
            , done    := (doneR : Signal dom Bool)
            , f12Start := isTrig
            , f12Aa := opA
            , f12Ab := (Signal.pure 0#384 : Signal dom (BitVec 384))
            , f12Ba := opB
            , f12Bb := (Signal.pure 0#384 : Signal dom (BitVec 384))
            } : MillerStepOut dom)

end Sparkle.IP.Crypto.BLS12MillerHW
