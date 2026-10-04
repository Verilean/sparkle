/-
  IP.Crypto.G2PointOpHW — one Jacobian point operation (double
  OR add) on the BLS12-381 G2 curve, as a `circuit do` FSM that
  drives the Fp2 multiplier `Fp2MulHW.fp2MulHW` as a shared
  sub-engine over a start/done handshake.

  This is the exact structural twin of `Secp256k1PointOpHW`:
  the same a = 0 Jacobian schedules (dbl-2009-l, 7 multiplies;
  add-2007-bl generic branch, 16 multiplies), but every operation
  is over Fp2 instead of Fp.  Each coordinate is an Fp2 element
  carried as TWO `BitVec 384` signals (c0, c1); each engine
  "multiply" is an Fp2-mul (3 Fp muls under the hood); the
  `×2/×3/×8` scalings are `Fp2.scaleFp`, i.e. componentwise Fp
  small-constant multiply, done combinationally as repeated
  conditional-reduce adds on each Fp coordinate.

  All Fp values are in the MONTGOMERY DOMAIN (R = 2^384); add/sub
  and ×k are linear so they carry through unchanged, and the Fp2
  multiplier already folds R^-1.  Domain conversion is the
  caller's job (once at the G2 scalar-mul boundary).

  Composition: the Fp2 multiplier is NOT instantiated here — it is
  driven over the exposed `fp2Start`/`fp2A0..fp2B1` ports and its
  `fp2C0`/`fp2C1`/`fp2Done` come back as inputs, wired one level
  up.  (Same synthesizable style as the secp256k1 stack.)

  Interface:
    inputs  start (Bool pulse), opDouble (Bool)
            x1_0,x1_1, y1_0,y1_1, z1_0,z1_1   — point 1 (Fp2 coords)
            x2_0,x2_1, y2_0,y2_1, z2_0,z2_1   — point 2 (ADD)
            fp2C0,fp2C1 — Fp2-multiplier result in
            fp2Done     — Fp2-multiplier done in
    outputs x0Out,x1Out, y0Out,y1Out, z0Out,z1Out — result Fp2 coords
            done (Bool pulse)
            fp2Start (Bool)          — pulse the Fp2 multiplier
            fp2A0,fp2A1, fp2B0,fp2B1 — Fp2 operands

  Timing: each Fp2-mul ≈ 48 cycles (3 Fp muls); DOUBLE ≈ 7 steps
  (~340 cyc), ADD ≈ 16 steps (~770 cyc).
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.Fp2MulHW

namespace Sparkle.IP.Crypto.G2PointOpHW

-- The flat `Circuit.SigList` pending-write accumulator makes `whnf` on these
-- wide Fp12/G2 records more expensive than the 200k default allows.  The
-- elaboration is linear, just over budget — raise the ceiling rather than
-- reshape the design.
set_option maxHeartbeats 1000000


open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- BLS12-381 base-field prime as a 385-bit constant. -/
def pBv385 : BitVec 385 := BitVec.ofNat 385 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- Output record.  G2 point coords are Fp2 (each two BitVec 384). -/
structure G2PointOpOut (dom : DomainConfig) where
  x0Out : Signal dom (BitVec 384)
  x1Out : Signal dom (BitVec 384)
  y0Out : Signal dom (BitVec 384)
  y1Out : Signal dom (BitVec 384)
  z0Out : Signal dom (BitVec 384)
  z1Out : Signal dom (BitVec 384)
  /-- Pulses for one cycle when the point op finishes. -/
  done : Signal dom Bool
  /-- Pulses for one cycle to trigger the external Fp2 multiplier. -/
  fp2Start : Signal dom Bool
  /-- Fp2 operand A (two components). -/
  fp2A0 : Signal dom (BitVec 384)
  fp2A1 : Signal dom (BitVec 384)
  /-- Fp2 operand B (two components). -/
  fp2B0 : Signal dom (BitVec 384)
  fp2B1 : Signal dom (BitVec 384)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (G2PointOpOut dom) dom := ⟨⟩

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

/-- Fp sub mod p (combinational): a + p − b, one conditional subtract. -/
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

-- Fp small-constant scalings.
private def fx2 {dom : DomainConfig} (a : Signal dom (BitVec 384)) : Signal dom (BitVec 384) := fAddP a a
private def fx3 {dom : DomainConfig} (a : Signal dom (BitVec 384)) : Signal dom (BitVec 384) := fAddP a (fx2 a)
private def fx8 {dom : DomainConfig} (a : Signal dom (BitVec 384)) : Signal dom (BitVec 384) := fx2 (fx2 (fx2 a))

/-- `stepSig == k` (5-bit step compare). -/
private def stepEqK {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 5)) (k : Nat) : Signal dom Bool :=
  (stepSig === (Signal.pure (BitVec.ofNat 5 k) : Signal dom (BitVec 5)))

/-- Latch the Fp2-mul result component into scratch `k` on a step-`k` ack. -/
private def latchIntoK {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 5))
    (engRes : Signal dom (BitVec 384)) (k : Nat)
    (cur : Signal dom (BitVec 384)) : Signal dom (BitVec 384) :=
  Signal.mux (stepAck &&& stepEqK stepSig k) engRes cur

/-- One G2 Jacobian point op (double or add) FSM. -/
def g2PointOpHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (opDouble : Signal dom Bool)
    (x1_0 x1_1 y1_0 y1_1 z1_0 z1_1 : Signal dom (BitVec 384))
    (x2_0 x2_1 y2_0 y2_1 z2_0 z2_1 : Signal dom (BitVec 384))
    (fp2C0 fp2C1 : Signal dom (BitVec 384))
    (fp2Done : Signal dom Bool) :
    G2PointOpOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger, 2 wait, 3 complete.
    let stR ← Signal.reg (0#2)
    -- Step index 0..15.
    let stepR ← Signal.reg (0#5)
    -- Op selector.
    let opDR ← Signal.reg false
    -- Latched input coords (Fp2 = two BitVec 384 each).
    let ax1_0R ← Signal.reg (0#384)
    let ax1_1R ← Signal.reg (0#384)
    let ay1_0R ← Signal.reg (0#384)
    let ay1_1R ← Signal.reg (0#384)
    let az1_0R ← Signal.reg (0#384)
    let az1_1R ← Signal.reg (0#384)
    let ax2_0R ← Signal.reg (0#384)
    let ax2_1R ← Signal.reg (0#384)
    let ay2_0R ← Signal.reg (0#384)
    let ay2_1R ← Signal.reg (0#384)
    let az2_0R ← Signal.reg (0#384)
    let az2_1R ← Signal.reg (0#384)
    -- Scratch for the 16 Fp2-mul results (each two components).
    let m0_0R ← Signal.reg (0#384); let m0_1R ← Signal.reg (0#384)
    let m1_0R ← Signal.reg (0#384); let m1_1R ← Signal.reg (0#384)
    let m2_0R ← Signal.reg (0#384); let m2_1R ← Signal.reg (0#384)
    let m3_0R ← Signal.reg (0#384); let m3_1R ← Signal.reg (0#384)
    let m4_0R ← Signal.reg (0#384); let m4_1R ← Signal.reg (0#384)
    let m5_0R ← Signal.reg (0#384); let m5_1R ← Signal.reg (0#384)
    let m6_0R ← Signal.reg (0#384); let m6_1R ← Signal.reg (0#384)
    let m7_0R ← Signal.reg (0#384); let m7_1R ← Signal.reg (0#384)
    let m8_0R ← Signal.reg (0#384); let m8_1R ← Signal.reg (0#384)
    let m9_0R ← Signal.reg (0#384); let m9_1R ← Signal.reg (0#384)
    let m10_0R ← Signal.reg (0#384); let m10_1R ← Signal.reg (0#384)
    let m11_0R ← Signal.reg (0#384); let m11_1R ← Signal.reg (0#384)
    let m12_0R ← Signal.reg (0#384); let m12_1R ← Signal.reg (0#384)
    let m13_0R ← Signal.reg (0#384); let m13_1R ← Signal.reg (0#384)
    let m14_0R ← Signal.reg (0#384); let m14_1R ← Signal.reg (0#384)
    let m15_0R ← Signal.reg (0#384); let m15_1R ← Signal.reg (0#384)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 5))
    let opDSig := (opDR : Signal dom Bool)
    let x1_0S := (ax1_0R : Signal dom (BitVec 384)); let x1_1S := (ax1_1R : Signal dom (BitVec 384))
    let y1_0S := (ay1_0R : Signal dom (BitVec 384)); let y1_1S := (ay1_1R : Signal dom (BitVec 384))
    let z1_0S := (az1_0R : Signal dom (BitVec 384)); let z1_1S := (az1_1R : Signal dom (BitVec 384))
    let x2_0S := (ax2_0R : Signal dom (BitVec 384)); let x2_1S := (ax2_1R : Signal dom (BitVec 384))
    let y2_0S := (ay2_0R : Signal dom (BitVec 384)); let y2_1S := (ay2_1R : Signal dom (BitVec 384))
    let z2_0S := (az2_0R : Signal dom (BitVec 384)); let z2_1S := (az2_1R : Signal dom (BitVec 384))
    let m0_0S := (m0_0R : Signal dom (BitVec 384)); let m0_1S := (m0_1R : Signal dom (BitVec 384))
    let m1_0S := (m1_0R : Signal dom (BitVec 384)); let m1_1S := (m1_1R : Signal dom (BitVec 384))
    let m2_0S := (m2_0R : Signal dom (BitVec 384)); let m2_1S := (m2_1R : Signal dom (BitVec 384))
    let m3_0S := (m3_0R : Signal dom (BitVec 384)); let m3_1S := (m3_1R : Signal dom (BitVec 384))
    let m4_0S := (m4_0R : Signal dom (BitVec 384)); let m4_1S := (m4_1R : Signal dom (BitVec 384))
    let m5_0S := (m5_0R : Signal dom (BitVec 384)); let m5_1S := (m5_1R : Signal dom (BitVec 384))
    let m6_0S := (m6_0R : Signal dom (BitVec 384)); let m6_1S := (m6_1R : Signal dom (BitVec 384))
    let m7_0S := (m7_0R : Signal dom (BitVec 384)); let m7_1S := (m7_1R : Signal dom (BitVec 384))
    let m8_0S := (m8_0R : Signal dom (BitVec 384)); let m8_1S := (m8_1R : Signal dom (BitVec 384))
    let m9_0S := (m9_0R : Signal dom (BitVec 384)); let m9_1S := (m9_1R : Signal dom (BitVec 384))
    let m10_0S := (m10_0R : Signal dom (BitVec 384)); let m10_1S := (m10_1R : Signal dom (BitVec 384))
    let m11_0S := (m11_0R : Signal dom (BitVec 384)); let m11_1S := (m11_1R : Signal dom (BitVec 384))
    let m12_0S := (m12_0R : Signal dom (BitVec 384)); let m12_1S := (m12_1R : Signal dom (BitVec 384))
    let m13_0S := (m13_0R : Signal dom (BitVec 384)); let m13_1S := (m13_1R : Signal dom (BitVec 384))
    let m14_0S := (m14_0R : Signal dom (BitVec 384)); let m14_1S := (m14_1R : Signal dom (BitVec 384))
    let m15_0S := (m15_0R : Signal dom (BitVec 384)); let m15_1S := (m15_1R : Signal dom (BitVec 384))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_5 := (Signal.pure 0#5 : Signal dom (BitVec 5))
    let p1_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))

    let isTrig := (stSig === p1_2 : Signal dom Bool)
    let isWait := (stSig === p2_2 : Signal dom Bool)

    -- ================= DOUBLE combinational intermediates (Fp2) =================
    -- Fp2 add/sub/×k are componentwise, so each is a pair of scalar
    -- Fp ops on the two components (0 / 1).
    -- m0=X*X m1=Y*Y m2=B*B(=m1*m1) m3=XB*XB m4=E*E m5=E*DmX3 m6=Y*Z
    let d_XB0 := fAddP x1_0S m1_0S; let d_XB1 := fAddP x1_1S m1_1S               -- X + B
    let d_AC0 := fAddP m0_0S m2_0S; let d_AC1 := fAddP m0_1S m2_1S              -- A + C
    let d_sub0 := fSubP m3_0S d_AC0; let d_sub1 := fSubP m3_1S d_AC1            -- (X+B)^2 - (A+C)
    let d_D0 := fx2 d_sub0; let d_D1 := fx2 d_sub1                             -- D = 2*(...)
    let d_E0 := fx3 m0_0S; let d_E1 := fx3 m0_1S                               -- E = 3A
    let d_2D0 := fx2 d_D0; let d_2D1 := fx2 d_D1                               -- 2D
    let d_X30 := fSubP m4_0S d_2D0; let d_X31 := fSubP m4_1S d_2D1             -- X3 = F - 2D
    let d_DmX30 := fSubP d_D0 d_X30; let d_DmX31 := fSubP d_D1 d_X31           -- D - X3
    let d_8C0 := fx8 m2_0S; let d_8C1 := fx8 m2_1S                             -- 8C
    let d_Y30 := fSubP m5_0S d_8C0; let d_Y31 := fSubP m5_1S d_8C1             -- Y3 = E(D-X3) - 8C
    let d_Z30 := fx2 m6_0S; let d_Z31 := fx2 m6_1S                             -- Z3 = 2*Y*Z

    -- ================= ADD combinational intermediates (Fp2) =================
    -- m0=Z1Z1 m1=Z2Z2 m2=U1 m3=U2 m4=Z2*Z2Z2 m5=S1 m6=Z1*Z1Z1 m7=S2
    -- m8=I m9=J m10=V m11=rr2 m12=rVX m13=S1J m14=sqZZ m15=Z3
    let a_H0 := fSubP m3_0S m2_0S; let a_H1 := fSubP m3_1S m2_1S               -- H = U2 - U1
    let a_twoH0 := fx2 a_H0; let a_twoH1 := fx2 a_H1                           -- 2H
    let a_S2mS1_0 := fSubP m7_0S m5_0S; let a_S2mS1_1 := fSubP m7_1S m5_1S     -- S2 - S1
    let a_rr0 := fx2 a_S2mS1_0; let a_rr1 := fx2 a_S2mS1_1                     -- rr = 2*(S2-S1)
    let a_r2mJ0 := fSubP m11_0S m9_0S; let a_r2mJ1 := fSubP m11_1S m9_1S       -- rr2 - J
    let a_2V0 := fx2 m10_0S; let a_2V1 := fx2 m10_1S                           -- 2V
    let a_X30 := fSubP a_r2mJ0 a_2V0; let a_X31 := fSubP a_r2mJ1 a_2V1         -- X3 = rr2 - J - 2V
    let a_VmX30 := fSubP m10_0S a_X30; let a_VmX31 := fSubP m10_1S a_X31       -- V - X3
    let a_2S1J0 := fx2 m13_0S; let a_2S1J1 := fx2 m13_1S                       -- 2*S1J
    let a_Y30 := fSubP m12_0S a_2S1J0; let a_Y31 := fSubP m12_1S a_2S1J1       -- Y3 = rVX - 2*S1J
    let a_ZZ0 := fAddP z1_0S z2_0S; let a_ZZ1 := fAddP z1_1S z2_1S             -- Z1 + Z2
    let a_ZZsum0 := fAddP m0_0S m1_0S; let a_ZZsum1 := fAddP m0_1S m1_1S       -- Z1Z1 + Z2Z2
    let a_z3t0 := fSubP m14_0S a_ZZsum0; let a_z3t1 := fSubP m14_1S a_ZZsum1   -- sqZZ - (Z1Z1+Z2Z2)

    -- ================= operand A/B selection per (opDouble, step) =================
    -- DOUBLE operand A (component 0 / 1), mirroring the secp256k1 routing.
    let dblA0 :=
      (Signal.mux (stepEqK stepSig 0) x1_0S
        (Signal.mux (stepEqK stepSig 1) y1_0S
          (Signal.mux (stepEqK stepSig 2) m1_0S
            (Signal.mux (stepEqK stepSig 3) d_XB0
              (Signal.mux (stepEqK stepSig 4) d_E0
                (Signal.mux (stepEqK stepSig 5) d_E0
                  (Signal.mux (stepEqK stepSig 6) y1_0S x1_0S)))))) : Signal dom (BitVec 384))
    let dblA1 :=
      (Signal.mux (stepEqK stepSig 0) x1_1S
        (Signal.mux (stepEqK stepSig 1) y1_1S
          (Signal.mux (stepEqK stepSig 2) m1_1S
            (Signal.mux (stepEqK stepSig 3) d_XB1
              (Signal.mux (stepEqK stepSig 4) d_E1
                (Signal.mux (stepEqK stepSig 5) d_E1
                  (Signal.mux (stepEqK stepSig 6) y1_1S x1_1S)))))) : Signal dom (BitVec 384))
    let dblB0 :=
      (Signal.mux (stepEqK stepSig 0) x1_0S
        (Signal.mux (stepEqK stepSig 1) y1_0S
          (Signal.mux (stepEqK stepSig 2) m1_0S
            (Signal.mux (stepEqK stepSig 3) d_XB0
              (Signal.mux (stepEqK stepSig 4) d_E0
                (Signal.mux (stepEqK stepSig 5) d_DmX30
                  (Signal.mux (stepEqK stepSig 6) z1_0S x1_0S)))))) : Signal dom (BitVec 384))
    let dblB1 :=
      (Signal.mux (stepEqK stepSig 0) x1_1S
        (Signal.mux (stepEqK stepSig 1) y1_1S
          (Signal.mux (stepEqK stepSig 2) m1_1S
            (Signal.mux (stepEqK stepSig 3) d_XB1
              (Signal.mux (stepEqK stepSig 4) d_E1
                (Signal.mux (stepEqK stepSig 5) d_DmX31
                  (Signal.mux (stepEqK stepSig 6) z1_1S x1_1S)))))) : Signal dom (BitVec 384))

    -- ADD operand A (component 0).
    let addA0 :=
      (Signal.mux (stepEqK stepSig 0) z1_0S
        (Signal.mux (stepEqK stepSig 1) z2_0S
          (Signal.mux (stepEqK stepSig 2) x1_0S
            (Signal.mux (stepEqK stepSig 3) x2_0S
              (Signal.mux (stepEqK stepSig 4) z2_0S
                (Signal.mux (stepEqK stepSig 5) y1_0S
                  (Signal.mux (stepEqK stepSig 6) z1_0S
                    (Signal.mux (stepEqK stepSig 7) y2_0S
                      (Signal.mux (stepEqK stepSig 8) a_twoH0
                        (Signal.mux (stepEqK stepSig 9) a_H0
                          (Signal.mux (stepEqK stepSig 10) m2_0S
                            (Signal.mux (stepEqK stepSig 11) a_rr0
                              (Signal.mux (stepEqK stepSig 12) a_rr0
                                (Signal.mux (stepEqK stepSig 13) m5_0S
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ0
                                    (Signal.mux (stepEqK stepSig 15) a_z3t0 z1_0S)))))))))))))))
        : Signal dom (BitVec 384))
    let addA1 :=
      (Signal.mux (stepEqK stepSig 0) z1_1S
        (Signal.mux (stepEqK stepSig 1) z2_1S
          (Signal.mux (stepEqK stepSig 2) x1_1S
            (Signal.mux (stepEqK stepSig 3) x2_1S
              (Signal.mux (stepEqK stepSig 4) z2_1S
                (Signal.mux (stepEqK stepSig 5) y1_1S
                  (Signal.mux (stepEqK stepSig 6) z1_1S
                    (Signal.mux (stepEqK stepSig 7) y2_1S
                      (Signal.mux (stepEqK stepSig 8) a_twoH1
                        (Signal.mux (stepEqK stepSig 9) a_H1
                          (Signal.mux (stepEqK stepSig 10) m2_1S
                            (Signal.mux (stepEqK stepSig 11) a_rr1
                              (Signal.mux (stepEqK stepSig 12) a_rr1
                                (Signal.mux (stepEqK stepSig 13) m5_1S
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ1
                                    (Signal.mux (stepEqK stepSig 15) a_z3t1 z1_1S)))))))))))))))
        : Signal dom (BitVec 384))
    -- ADD operand B (component 0).
    let addB0 :=
      (Signal.mux (stepEqK stepSig 0) z1_0S
        (Signal.mux (stepEqK stepSig 1) z2_0S
          (Signal.mux (stepEqK stepSig 2) m1_0S
            (Signal.mux (stepEqK stepSig 3) m0_0S
              (Signal.mux (stepEqK stepSig 4) m1_0S
                (Signal.mux (stepEqK stepSig 5) m4_0S
                  (Signal.mux (stepEqK stepSig 6) m0_0S
                    (Signal.mux (stepEqK stepSig 7) m6_0S
                      (Signal.mux (stepEqK stepSig 8) a_twoH0
                        (Signal.mux (stepEqK stepSig 9) m8_0S
                          (Signal.mux (stepEqK stepSig 10) m8_0S
                            (Signal.mux (stepEqK stepSig 11) a_rr0
                              (Signal.mux (stepEqK stepSig 12) a_VmX30
                                (Signal.mux (stepEqK stepSig 13) m9_0S
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ0
                                    (Signal.mux (stepEqK stepSig 15) a_H0 z1_0S)))))))))))))))
        : Signal dom (BitVec 384))
    let addB1 :=
      (Signal.mux (stepEqK stepSig 0) z1_1S
        (Signal.mux (stepEqK stepSig 1) z2_1S
          (Signal.mux (stepEqK stepSig 2) m1_1S
            (Signal.mux (stepEqK stepSig 3) m0_1S
              (Signal.mux (stepEqK stepSig 4) m1_1S
                (Signal.mux (stepEqK stepSig 5) m4_1S
                  (Signal.mux (stepEqK stepSig 6) m0_1S
                    (Signal.mux (stepEqK stepSig 7) m6_1S
                      (Signal.mux (stepEqK stepSig 8) a_twoH1
                        (Signal.mux (stepEqK stepSig 9) m8_1S
                          (Signal.mux (stepEqK stepSig 10) m8_1S
                            (Signal.mux (stepEqK stepSig 11) a_rr1
                              (Signal.mux (stepEqK stepSig 12) a_VmX31
                                (Signal.mux (stepEqK stepSig 13) m9_1S
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ1
                                    (Signal.mux (stepEqK stepSig 15) a_H1 z1_1S)))))))))))))))
        : Signal dom (BitVec 384))

    let engA0 := (Signal.mux opDSig dblA0 addA0 : Signal dom (BitVec 384))
    let engA1 := (Signal.mux opDSig dblA1 addA1 : Signal dom (BitVec 384))
    let engB0 := (Signal.mux opDSig dblB0 addB0 : Signal dom (BitVec 384))
    let engB1 := (Signal.mux opDSig dblB1 addB1 : Signal dom (BitVec 384))

    let engC0 := fp2C0
    let engC1 := fp2C1
    let engDone := fp2Done

    -- Last step: double = 6, add = 15.
    let lastStep := (Signal.mux opDSig (stepEqK stepSig 6) (stepEqK stepSig 15) : Signal dom Bool)
    let stepAck := (isWait &&& engDone : Signal dom Bool)
    let atLast := (stepAck &&& lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    -- Phase transitions.
    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    let stepInc := (stepSig + p1_5 : Signal dom (BitVec 5))
    stepR <~ Signal.mux start p0_5
              (Signal.mux advance stepInc stepSig)

    opDR <~ Signal.mux start opDouble opDSig

    -- Coordinate latches.
    ax1_0R <~ Signal.mux start x1_0 x1_0S; ax1_1R <~ Signal.mux start x1_1 x1_1S
    ay1_0R <~ Signal.mux start y1_0 y1_0S; ay1_1R <~ Signal.mux start y1_1 y1_1S
    az1_0R <~ Signal.mux start z1_0 z1_0S; az1_1R <~ Signal.mux start z1_1 z1_1S
    ax2_0R <~ Signal.mux start x2_0 x2_0S; ax2_1R <~ Signal.mux start x2_1 x2_1S
    ay2_0R <~ Signal.mux start y2_0 y2_0S; ay2_1R <~ Signal.mux start y2_1 y2_1S
    az2_0R <~ Signal.mux start z2_0 z2_0S; az2_1R <~ Signal.mux start z2_1 z2_1S

    -- Scratch latches (both components).
    m0_0R  <~ latchIntoK stepAck stepSig engC0 0 m0_0S;  m0_1R  <~ latchIntoK stepAck stepSig engC1 0 m0_1S
    m1_0R  <~ latchIntoK stepAck stepSig engC0 1 m1_0S;  m1_1R  <~ latchIntoK stepAck stepSig engC1 1 m1_1S
    m2_0R  <~ latchIntoK stepAck stepSig engC0 2 m2_0S;  m2_1R  <~ latchIntoK stepAck stepSig engC1 2 m2_1S
    m3_0R  <~ latchIntoK stepAck stepSig engC0 3 m3_0S;  m3_1R  <~ latchIntoK stepAck stepSig engC1 3 m3_1S
    m4_0R  <~ latchIntoK stepAck stepSig engC0 4 m4_0S;  m4_1R  <~ latchIntoK stepAck stepSig engC1 4 m4_1S
    m5_0R  <~ latchIntoK stepAck stepSig engC0 5 m5_0S;  m5_1R  <~ latchIntoK stepAck stepSig engC1 5 m5_1S
    m6_0R  <~ latchIntoK stepAck stepSig engC0 6 m6_0S;  m6_1R  <~ latchIntoK stepAck stepSig engC1 6 m6_1S
    m7_0R  <~ latchIntoK stepAck stepSig engC0 7 m7_0S;  m7_1R  <~ latchIntoK stepAck stepSig engC1 7 m7_1S
    m8_0R  <~ latchIntoK stepAck stepSig engC0 8 m8_0S;  m8_1R  <~ latchIntoK stepAck stepSig engC1 8 m8_1S
    m9_0R  <~ latchIntoK stepAck stepSig engC0 9 m9_0S;  m9_1R  <~ latchIntoK stepAck stepSig engC1 9 m9_1S
    m10_0R <~ latchIntoK stepAck stepSig engC0 10 m10_0S; m10_1R <~ latchIntoK stepAck stepSig engC1 10 m10_1S
    m11_0R <~ latchIntoK stepAck stepSig engC0 11 m11_0S; m11_1R <~ latchIntoK stepAck stepSig engC1 11 m11_1S
    m12_0R <~ latchIntoK stepAck stepSig engC0 12 m12_0S; m12_1R <~ latchIntoK stepAck stepSig engC1 12 m12_1S
    m13_0R <~ latchIntoK stepAck stepSig engC0 13 m13_0S; m13_1R <~ latchIntoK stepAck stepSig engC1 13 m13_1S
    m14_0R <~ latchIntoK stepAck stepSig engC0 14 m14_0S; m14_1R <~ latchIntoK stepAck stepSig engC1 14 m14_1S
    m15_0R <~ latchIntoK stepAck stepSig engC0 15 m15_0S; m15_1R <~ latchIntoK stepAck stepSig engC1 15 m15_1S

    doneR <~ atLast

    -- Outputs (Fp2 coords), selected by op at the done cycle.
    let x0Out := (Signal.mux opDSig d_X30 a_X30 : Signal dom (BitVec 384))
    let x1OutV := (Signal.mux opDSig d_X31 a_X31 : Signal dom (BitVec 384))
    let y0Out := (Signal.mux opDSig d_Y30 a_Y30 : Signal dom (BitVec 384))
    let y1OutV := (Signal.mux opDSig d_Y31 a_Y31 : Signal dom (BitVec 384))
    let z0Out := (Signal.mux opDSig d_Z30 m15_0S : Signal dom (BitVec 384))
    let z1OutV := (Signal.mux opDSig d_Z31 m15_1S : Signal dom (BitVec 384))

    return ({ x0Out := x0Out
            , x1Out := x1OutV
            , y0Out := y0Out
            , y1Out := y1OutV
            , z0Out := z0Out
            , z1Out := z1OutV
            , done := (doneR : Signal dom Bool)
            , fp2Start := isTrig
            , fp2A0 := engA0
            , fp2A1 := engA1
            , fp2B0 := engB0
            , fp2B1 := engB1
            } : G2PointOpOut dom)

end Sparkle.IP.Crypto.G2PointOpHW
