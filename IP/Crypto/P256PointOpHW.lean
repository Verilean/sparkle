/-
  IP.Crypto.P256PointOpHW — one Jacobian point operation (double
  OR add) on NIST P-256, as a `circuit do` FSM that drives the
  bit-serial field multiplier `P256FieldHW.mulHW` as a shared
  sub-engine via its start/done handshake.

  This is the P-256 (a = -3) analogue of `Secp256k1PointOpHW`.
  The ADD path (add-2007-bl) is curve-independent and copied
  verbatim.  The DOUBLE path is the a = -3 doubling (dbl-2001-b),
  validated in `P256PointJacTest` against the affine reference:

      delta = Z²
      gamma = Y²
      beta  = X·gamma
      alpha = 3·(X - delta)·(X + delta)      (= 3X² + a·Z⁴, a = -3)
      X3    = alpha² - 8·beta
      Z3    = (Y + Z)² - gamma - delta        (= 2·Y·Z)
      Y3    = alpha·(4·beta - X3) - 8·gamma²

  DOUBLE multiply schedule (8 engine multiplies, steps 0..7):
    0: m0 = Z·Z            (delta)
    1: m1 = Y·Y            (gamma)
    2: m2 = X·m1           (beta)
    3: m3 = (X-δ)·(X+δ)    (alpha = 3·m3)
    4: m4 = (3·m3)²        (alpha²  → X3 = m4 - 8·beta)
    5: m5 = (Y+Z)·(Y+Z)    ((Y+Z)²  → Z3 = m5 - gamma - delta)
    6: m6 = (3·m3)·(4β-X3) (→ Y3 = m6 - 8·gamma²)
    7: m7 = m1·m1          (gamma²)

  vs secp256k1 (a = 0) which uses 7 multiplies with the doubling
  coefficient `E = 3·X²` computed as `fx3 (X·X)` — a = -3 instead
  needs `alpha = 3(X-Z²)(X+Z²)`, hence the extra Z² multiply and
  the different operand schedule.

  The field multiplier is NOT instantiated here — it is driven
  over an external start/done handshake, the same synthesizable
  composition style as the secp256k1 stack.

  Interface: identical to `Secp256k1PointOpHW.pointOpHW`.
-/
import Sparkle
import IP.Crypto.Proof.P256Field
import IP.Crypto.P256FieldHW

namespace Sparkle.IP.Crypto.P256PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- P-256 prime as a 257-bit constant (headroom for combinational
    add/sub reductions, both < 2p < 2^257). -/
def pBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.P256Field.p

/-- Output record. -/
structure PointOpOut (dom : DomainConfig) where
  /-- Result X coordinate (Jacobian), valid at `done`. -/
  xOut : Signal dom (BitVec 256)
  /-- Result Y coordinate (Jacobian), valid at `done`. -/
  yOut : Signal dom (BitVec 256)
  /-- Result Z coordinate (Jacobian), valid at `done`. -/
  zOut : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the point op finishes. -/
  done : Signal dom Bool
  /-- Pulses for one cycle to trigger the external field multiplier. -/
  mulStart : Signal dom Bool
  /-- Operand A for the external field multiplier. -/
  mulA : Signal dom (BitVec 256)
  /-- Operand B for the external field multiplier. -/
  mulB : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PointOpOut dom) dom := ⟨⟩

/-- Field add mod p (combinational). -/
private def faddMod {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := (aw + bw : Signal dom (BitVec 257))
  let pP := (Signal.pure pBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - pP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Field sub mod p (combinational): a + p - b in 257 bits, one
    conditional subtract. -/
private def fsubMod {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let pP := (Signal.pure pBv257 : Signal dom (BitVec 257))
  let apb := (aw + pP : Signal dom (BitVec 257))
  let s   := (apb - bw : Signal dom (BitVec 257))
  let ge  := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - pP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Field ×2 (combinational). -/
private def fx2 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := faddMod a a

/-- Field ×3 (combinational). -/
private def fx3 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := faddMod a (fx2 a)

/-- Field ×4 (combinational). -/
private def fx4 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := fx2 (fx2 a)

/-- Field ×8 (combinational). -/
private def fx8 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := fx2 (fx2 (fx2 a))

/-- `stepSig == k` as a Bool signal. -/
private def stepEqK {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 6)) (k : Nat) : Signal dom Bool :=
  (stepSig === (Signal.pure (BitVec.ofNat 6 k) : Signal dom (BitVec 6)))

/-- Next value for scratch register `k`. -/
private def latchIntoK {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 6))
    (engRes : Signal dom (BitVec 256)) (k : Nat)
    (cur : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  Signal.mux (stepAck &&& stepEqK stepSig k) engRes cur

/-- One Jacobian point op (double or add) FSM, P-256 (a = -3). -/
def pointOpHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (opDouble : Signal dom Bool)
    (x1 y1 z1 : Signal dom (BitVec 256))
    (x2 y2 z2 : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256))
    (mulDone : Signal dom Bool) :
    PointOpOut dom :=
  circuit do
    let stR ← Signal.reg (0#2)
    let stepR ← Signal.reg (0#6)
    let opDR ← Signal.reg false
    let ax1R ← Signal.reg (0#256)
    let ay1R ← Signal.reg (0#256)
    let az1R ← Signal.reg (0#256)
    let ax2R ← Signal.reg (0#256)
    let ay2R ← Signal.reg (0#256)
    let az2R ← Signal.reg (0#256)
    let m0R ← Signal.reg (0#256)
    let m1R ← Signal.reg (0#256)
    let m2R ← Signal.reg (0#256)
    let m3R ← Signal.reg (0#256)
    let m4R ← Signal.reg (0#256)
    let m5R ← Signal.reg (0#256)
    let m6R ← Signal.reg (0#256)
    let m7R ← Signal.reg (0#256)
    let m8R ← Signal.reg (0#256)
    let m9R ← Signal.reg (0#256)
    let m10R ← Signal.reg (0#256)
    let m11R ← Signal.reg (0#256)
    let m12R ← Signal.reg (0#256)
    let m13R ← Signal.reg (0#256)
    let m14R ← Signal.reg (0#256)
    let m15R ← Signal.reg (0#256)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 6))
    let opDSig := (opDR : Signal dom Bool)
    let x1S := (ax1R : Signal dom (BitVec 256))
    let y1S := (ay1R : Signal dom (BitVec 256))
    let z1S := (az1R : Signal dom (BitVec 256))
    let x2S := (ax2R : Signal dom (BitVec 256))
    let y2S := (ay2R : Signal dom (BitVec 256))
    let z2S := (az2R : Signal dom (BitVec 256))
    let m0S := (m0R : Signal dom (BitVec 256))
    let m1S := (m1R : Signal dom (BitVec 256))
    let m2S := (m2R : Signal dom (BitVec 256))
    let m3S := (m3R : Signal dom (BitVec 256))
    let m4S := (m4R : Signal dom (BitVec 256))
    let m5S := (m5R : Signal dom (BitVec 256))
    let m6S := (m6R : Signal dom (BitVec 256))
    let m7S := (m7R : Signal dom (BitVec 256))
    let m8S := (m8R : Signal dom (BitVec 256))
    let m9S := (m9R : Signal dom (BitVec 256))
    let m10S := (m10R : Signal dom (BitVec 256))
    let m11S := (m11R : Signal dom (BitVec 256))
    let m12S := (m12R : Signal dom (BitVec 256))
    let m13S := (m13R : Signal dom (BitVec 256))
    let m14S := (m14R : Signal dom (BitVec 256))
    let m15S := (m15R : Signal dom (BitVec 256))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_6 := (Signal.pure 0#6 : Signal dom (BitVec 6))
    let p1_6 := (Signal.pure 1#6 : Signal dom (BitVec 6))

    let isTrig := (stSig === p1_2 : Signal dom Bool)
    let isWait := (stSig === p2_2 : Signal dom Bool)

    -- ================= DOUBLE (a = -3) combinational exprs =================
    -- Scratch: m0=δ(Z²) m1=γ(Y²) m2=β(Xγ) m3=(X-δ)(X+δ) m4=α²
    --          m5=(Y+Z)² m6=α(4β-X3) m7=γ²
    let d_alpha := fx3 m3S                               -- α = 3·m3
    let d_XmD   := fsubMod x1S m0S                       -- X - δ
    let d_XpD   := faddMod x1S m0S                       -- X + δ
    let d_YpZ   := faddMod y1S z1S                       -- Y + Z
    let d_X3    := fsubMod m4S (fx8 m2S)                 -- α² - 8β
    let d_Z3    := fsubMod (fsubMod m5S m1S) m0S         -- (Y+Z)² - γ - δ
    let d_4bmX3 := fsubMod (fx4 m2S) d_X3                -- 4β - X3
    let d_Y3    := fsubMod m6S (fx8 m7S)                 -- α(4β-X3) - 8γ²

    -- ================= ADD (add-2007-bl) combinational exprs =================
    let a_H    := fsubMod m3S m2S                        -- U2 - U1
    let a_twoH := fx2 a_H                                -- 2H
    let a_rr   := fx2 (fsubMod m7S m5S)                  -- 2*(S2 - S1)
    let a_X3   := fsubMod (fsubMod m11S m9S) (fx2 m10S)  -- rr2 - J - 2V
    let a_VmX3 := fsubMod m10S a_X3                      -- V - X3
    let a_Y3   := fsubMod m12S (fx2 m13S)                -- rVX - 2*S1J
    let a_ZZ   := faddMod z1S z2S                        -- Z1 + Z2
    let a_z3t  := fsubMod m14S (faddMod m0S m1S)         -- sqZZ - (Z1Z1+Z2Z2)

    -- ================= operand A/B selection =================
    -- DOUBLE operands (8 multiplies, steps 0..7):
    let dblA :=
      (Signal.mux (stepEqK stepSig 0) z1S
        (Signal.mux (stepEqK stepSig 1) y1S
          (Signal.mux (stepEqK stepSig 2) x1S
            (Signal.mux (stepEqK stepSig 3) d_XmD
              (Signal.mux (stepEqK stepSig 4) d_alpha
                (Signal.mux (stepEqK stepSig 5) d_YpZ
                  (Signal.mux (stepEqK stepSig 6) d_alpha m1S)))))) : Signal dom (BitVec 256))
    let dblB :=
      (Signal.mux (stepEqK stepSig 0) z1S
        (Signal.mux (stepEqK stepSig 1) y1S
          (Signal.mux (stepEqK stepSig 2) m1S
            (Signal.mux (stepEqK stepSig 3) d_XpD
              (Signal.mux (stepEqK stepSig 4) d_alpha
                (Signal.mux (stepEqK stepSig 5) d_YpZ
                  (Signal.mux (stepEqK stepSig 6) d_4bmX3 m1S)))))) : Signal dom (BitVec 256))
    -- ADD operands (16 multiplies, steps 0..15):
    let addA :=
      (Signal.mux (stepEqK stepSig 0) z1S
        (Signal.mux (stepEqK stepSig 1) z2S
          (Signal.mux (stepEqK stepSig 2) x1S
            (Signal.mux (stepEqK stepSig 3) x2S
              (Signal.mux (stepEqK stepSig 4) z2S
                (Signal.mux (stepEqK stepSig 5) y1S
                  (Signal.mux (stepEqK stepSig 6) z1S
                    (Signal.mux (stepEqK stepSig 7) y2S
                      (Signal.mux (stepEqK stepSig 8) a_twoH
                        (Signal.mux (stepEqK stepSig 9) a_H
                          (Signal.mux (stepEqK stepSig 10) m2S
                            (Signal.mux (stepEqK stepSig 11) a_rr
                              (Signal.mux (stepEqK stepSig 12) a_rr
                                (Signal.mux (stepEqK stepSig 13) m5S
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ
                                    (Signal.mux (stepEqK stepSig 15) a_z3t z1S)))))))))))))))
        : Signal dom (BitVec 256))
    let addB :=
      (Signal.mux (stepEqK stepSig 0) z1S
        (Signal.mux (stepEqK stepSig 1) z2S
          (Signal.mux (stepEqK stepSig 2) m1S
            (Signal.mux (stepEqK stepSig 3) m0S
              (Signal.mux (stepEqK stepSig 4) m1S
                (Signal.mux (stepEqK stepSig 5) m4S
                  (Signal.mux (stepEqK stepSig 6) m0S
                    (Signal.mux (stepEqK stepSig 7) m6S
                      (Signal.mux (stepEqK stepSig 8) a_twoH
                        (Signal.mux (stepEqK stepSig 9) m8S
                          (Signal.mux (stepEqK stepSig 10) m8S
                            (Signal.mux (stepEqK stepSig 11) a_rr
                              (Signal.mux (stepEqK stepSig 12) a_VmX3
                                (Signal.mux (stepEqK stepSig 13) m9S
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ
                                    (Signal.mux (stepEqK stepSig 15) a_H z1S)))))))))))))))
        : Signal dom (BitVec 256))

    let engA := (Signal.mux opDSig dblA addA : Signal dom (BitVec 256))
    let engB := (Signal.mux opDSig dblB addB : Signal dom (BitVec 256))

    let engRes := mulResult
    let engDone := mulDone

    -- Last step: double = 7, add = 15.
    let lastStep := (Signal.mux opDSig (stepEqK stepSig 7) (stepEqK stepSig 15) : Signal dom Bool)
    let stepAck := (isWait &&& engDone : Signal dom Bool)
    let atLast := (stepAck &&& lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    let stepInc := (stepSig + p1_6 : Signal dom (BitVec 6))
    stepR <~ Signal.mux start p0_6
              (Signal.mux advance stepInc stepSig)

    opDR <~ Signal.mux start opDouble opDSig

    ax1R <~ Signal.mux start x1 x1S
    ay1R <~ Signal.mux start y1 y1S
    az1R <~ Signal.mux start z1 z1S
    ax2R <~ Signal.mux start x2 x2S
    ay2R <~ Signal.mux start y2 y2S
    az2R <~ Signal.mux start z2 z2S

    m0R  <~ latchIntoK stepAck stepSig engRes 0 m0S
    m1R  <~ latchIntoK stepAck stepSig engRes 1 m1S
    m2R  <~ latchIntoK stepAck stepSig engRes 2 m2S
    m3R  <~ latchIntoK stepAck stepSig engRes 3 m3S
    m4R  <~ latchIntoK stepAck stepSig engRes 4 m4S
    m5R  <~ latchIntoK stepAck stepSig engRes 5 m5S
    m6R  <~ latchIntoK stepAck stepSig engRes 6 m6S
    m7R  <~ latchIntoK stepAck stepSig engRes 7 m7S
    m8R  <~ latchIntoK stepAck stepSig engRes 8 m8S
    m9R  <~ latchIntoK stepAck stepSig engRes 9 m9S
    m10R <~ latchIntoK stepAck stepSig engRes 10 m10S
    m11R <~ latchIntoK stepAck stepSig engRes 11 m11S
    m12R <~ latchIntoK stepAck stepSig engRes 12 m12S
    m13R <~ latchIntoK stepAck stepSig engRes 13 m13S
    m14R <~ latchIntoK stepAck stepSig engRes 14 m14S
    m15R <~ latchIntoK stepAck stepSig engRes 15 m15S

    doneR <~ atLast

    let xOut := (Signal.mux opDSig d_X3 a_X3 : Signal dom (BitVec 256))
    let yOut := (Signal.mux opDSig d_Y3 a_Y3 : Signal dom (BitVec 256))
    let zOut := (Signal.mux opDSig d_Z3 m15S : Signal dom (BitVec 256))

    return ({ xOut := xOut
            , yOut := yOut
            , zOut := zOut
            , done := (doneR : Signal dom Bool)
            , mulStart := isTrig
            , mulA := engA
            , mulB := engB
            } : PointOpOut dom)

end Sparkle.IP.Crypto.P256PointOpHW
