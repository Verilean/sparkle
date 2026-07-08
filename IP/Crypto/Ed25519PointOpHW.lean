/-
  IP.Crypto.Ed25519PointOpHW — one extended twisted-Edwards
  point operation (double OR unified-add) on Ed25519, as a
  `circuit do` FSM driving the bit-serial field multiplier
  `Ed25519FieldHW.mulHW` as a shared sub-engine over its
  start/done handshake.

  Op selected by `opDouble` (latched on `start`):
    * true  ⇒ DOUBLE (X,Y,Z,T)                 — 8 engine multiplies
    * false ⇒ ADD    (X1,Y1,Z1,T1)+(X2,Y2,Z2,T2) — 9 engine multiplies

  Only field *multiplies* use the engine; field add/sub and ×2
  are combinational (single conditional reduce mod p = 2²⁵⁵-19),
  folded into the per-step operand muxes.  Because Edwards
  addition is complete, no special-casing is needed.

  Formulas match `Ed25519PointExt` (a = -1):
    DOUBLE dbl-2008-hwcd:  A=X²,B=Y²,C=2Z²,D=-A,E=(X+Y)²-A-B,
                           G=D+B,F=G-C,H=D-B; X3=EF,Y3=GH,Z3=FG,T3=EH.
    ADD    add-2008-hwcd-3: A=(Y1-X1)(Y2-X2),B=(Y1+X1)(Y2+X2),
                           C=(2T1)(dT2),D=2Z1Z2,E=B-A,F=D-C,G=D+C,
                           H=B+A; X3=EF,Y3=GH,Z3=FG,T3=EH.

  The multiplier is NOT instantiated here — it is driven over an
  external start/done handshake (same composition style as
  `Secp256k1PointOpHW`).  A higher-level module (the scalar-mul
  controller) or a testbench wires an `Ed25519FieldHW.mulHW`
  instance to `mulStart`/`mulA`/`mulB` and routes `result`/`done`
  back into `mulResult`/`mulDone`.

  Interface:
    inputs  start (Bool pulse), opDouble (Bool, latched),
            x1,y1,z1,t1  (first point, BitVec 256),
            x2,y2,z2,t2  (second point, ADD only),
            mulResult, mulDone (field-mul handshake in)
    outputs xOut,yOut,zOut,tOut (result coords, valid at done),
            done (Bool pulse),
            mulStart, mulA, mulB (field-mul handshake out)
-/
import Sparkle
import IP.Crypto.Proof.Ed25519Field
import IP.Crypto.Proof.Ed25519Point
import IP.Crypto.Ed25519FieldHW

namespace Sparkle.IP.Crypto.Ed25519PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- p = 2²⁵⁵-19 as a 257-bit constant (headroom for a+b and
    a+p-b combinational reductions, both < 2p < 2²⁵⁷). -/
def pBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Ed25519Field.p

/-- The curve constant d = -121665/121666 mod p, as a literal
    256-bit constant (must be a literal — the `Ed25519Point.d`
    definition computes a field inverse, which the synth
    elaborator cannot unfold).  Value verified against
    `Ed25519Point.d`. -/
def dBv : BitVec 256 :=
  0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3#256

/-- Output record. -/
structure PointOpOut (dom : DomainConfig) where
  xOut : Signal dom (BitVec 256)
  yOut : Signal dom (BitVec 256)
  zOut : Signal dom (BitVec 256)
  tOut : Signal dom (BitVec 256)
  done : Signal dom Bool
  mulStart : Signal dom Bool
  mulA : Signal dom (BitVec 256)
  mulB : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PointOpOut dom) dom := ⟨⟩

/-- Field add mod p (combinational): widen to 257, add, single
    conditional subtract of p. -/
private def faddMod {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := (aw + bw : Signal dom (BitVec 257))
  let pP := (Signal.pure pBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - pP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Field sub mod p (combinational): a + p - b in 257 bits
    (in [0, 2p)), then one conditional subtract. -/
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

/-- Field negate mod p (combinational): 0 - a. -/
private def fnegMod {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  fsubMod (Signal.pure 0#256 : Signal dom (BitVec 256)) a

/-- `stepSig == k` as a Bool signal. -/
private def stepEqK {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 5)) (k : Nat) : Signal dom Bool :=
  (stepSig === (Signal.pure (BitVec.ofNat 5 k) : Signal dom (BitVec 5)))

/-- Next value for scratch register `k`. -/
private def latchIntoK {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 5))
    (engRes : Signal dom (BitVec 256)) (k : Nat)
    (cur : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  Signal.mux (stepAck &&& stepEqK stepSig k) engRes cur

/-- One extended-coords point op (double or add) FSM. -/
def pointOpHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (opDouble : Signal dom Bool)
    (x1 y1 z1 t1 : Signal dom (BitVec 256))
    (x2 y2 z2 t2 : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256))
    (mulDone : Signal dom Bool) :
    PointOpOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger, 2 wait, 3 complete.
    let stR ← Signal.reg (0#2)
    -- Step index 0..8.
    let stepR ← Signal.reg (0#5)
    let opDR ← Signal.reg false
    -- Latched inputs.
    let ax1R ← Signal.reg (0#256); let ay1R ← Signal.reg (0#256)
    let az1R ← Signal.reg (0#256); let at1R ← Signal.reg (0#256)
    let ax2R ← Signal.reg (0#256); let ay2R ← Signal.reg (0#256)
    let az2R ← Signal.reg (0#256); let at2R ← Signal.reg (0#256)
    -- Scratch registers m0..m8 for engine-multiply results.
    let m0R ← Signal.reg (0#256); let m1R ← Signal.reg (0#256)
    let m2R ← Signal.reg (0#256); let m3R ← Signal.reg (0#256)
    let m4R ← Signal.reg (0#256); let m5R ← Signal.reg (0#256)
    let m6R ← Signal.reg (0#256); let m7R ← Signal.reg (0#256)
    let m8R ← Signal.reg (0#256)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let stepSig := (stepR : Signal dom (BitVec 5))
    let opDSig := (opDR : Signal dom Bool)
    let x1S := (ax1R : Signal dom (BitVec 256)); let y1S := (ay1R : Signal dom (BitVec 256))
    let z1S := (az1R : Signal dom (BitVec 256)); let t1S := (at1R : Signal dom (BitVec 256))
    let x2S := (ax2R : Signal dom (BitVec 256)); let y2S := (ay2R : Signal dom (BitVec 256))
    let z2S := (az2R : Signal dom (BitVec 256)); let t2S := (at2R : Signal dom (BitVec 256))
    let m0S := (m0R : Signal dom (BitVec 256)); let m1S := (m1R : Signal dom (BitVec 256))
    let m2S := (m2R : Signal dom (BitVec 256)); let m3S := (m3R : Signal dom (BitVec 256))
    let m4S := (m4R : Signal dom (BitVec 256)); let m5S := (m5R : Signal dom (BitVec 256))
    let m6S := (m6R : Signal dom (BitVec 256)); let m7S := (m7R : Signal dom (BitVec 256))
    let m8S := (m8R : Signal dom (BitVec 256))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_5 := (Signal.pure 0#5 : Signal dom (BitVec 5))
    let p1_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let dConst := (Signal.pure dBv : Signal dom (BitVec 256))

    let isTrig := (stSig === p1_2 : Signal dom Bool)
    let isWait := (stSig === p2_2 : Signal dom Bool)

    -- ================= DOUBLE combinational intermediates =================
    -- muls: m0=X*X(A) m1=Y*Y(B) m2=Z*Z m3=XY2=(X+Y)^2
    --       m4=E*F(X3) m5=G*H(Y3) m6=F*G(Z3) m7=E*H(T3)
    let d_C    := fx2 m2S                          -- C = 2Z²
    let d_D    := fnegMod m0S                       -- D = -A
    let d_XY   := faddMod x1S y1S                   -- X+Y  (operand for m3)
    let d_E    := fsubMod (fsubMod m3S m0S) m1S     -- E = (X+Y)² - A - B
    let d_G    := faddMod d_D m1S                   -- G = D+B
    let d_F    := fsubMod d_G d_C                   -- F = G-C
    let d_H    := fsubMod d_D m1S                   -- H = D-B

    -- ================= ADD combinational intermediates =================
    -- muls: m0=(Y1-X1)(Y2-X2)(A) m1=(Y1+X1)(Y2+X2)(B) m2=d*T2 m3=(2T1)*m2(C)
    --       m4=Z1*Z2  m5=E*F(X3) m6=G*H(Y3) m7=F*G(Z3) m8=E*H(T3)
    let a_YmX1 := fsubMod y1S x1S                   -- Y1-X1  (m0 operand A)
    let a_YmX2 := fsubMod y2S x2S                   -- Y2-X2  (m0 operand B)
    let a_YpX1 := faddMod y1S x1S                   -- Y1+X1  (m1 operand A)
    let a_YpX2 := faddMod y2S x2S                   -- Y2+X2  (m1 operand B)
    let a_2T1  := fx2 t1S                           -- 2·T1   (m3 operand A)
    let a_D    := fx2 m4S                           -- D = 2·Z1·Z2
    let a_E    := fsubMod m1S m0S                   -- E = B-A
    let a_F    := fsubMod a_D m3S                   -- F = D-C
    let a_G    := faddMod a_D m3S                   -- G = D+C
    let a_H    := faddMod m1S m0S                   -- H = B+A

    -- ================= operand A/B selection =================
    let dblA :=
      (Signal.mux (stepEqK stepSig 0) x1S
        (Signal.mux (stepEqK stepSig 1) y1S
          (Signal.mux (stepEqK stepSig 2) z1S
            (Signal.mux (stepEqK stepSig 3) d_XY
              (Signal.mux (stepEqK stepSig 4) d_E
                (Signal.mux (stepEqK stepSig 5) d_G
                  (Signal.mux (stepEqK stepSig 6) d_F d_E))))))
        : Signal dom (BitVec 256))
    let dblB :=
      (Signal.mux (stepEqK stepSig 0) x1S
        (Signal.mux (stepEqK stepSig 1) y1S
          (Signal.mux (stepEqK stepSig 2) z1S
            (Signal.mux (stepEqK stepSig 3) d_XY
              (Signal.mux (stepEqK stepSig 4) d_F
                (Signal.mux (stepEqK stepSig 5) d_H
                  (Signal.mux (stepEqK stepSig 6) d_G d_H)))))) : Signal dom (BitVec 256))
    let addA :=
      (Signal.mux (stepEqK stepSig 0) a_YmX1
        (Signal.mux (stepEqK stepSig 1) a_YpX1
          (Signal.mux (stepEqK stepSig 2) dConst
            (Signal.mux (stepEqK stepSig 3) a_2T1
              (Signal.mux (stepEqK stepSig 4) z1S
                (Signal.mux (stepEqK stepSig 5) a_E
                  (Signal.mux (stepEqK stepSig 6) a_G
                    (Signal.mux (stepEqK stepSig 7) a_F a_E)))))))
        : Signal dom (BitVec 256))
    let addB :=
      (Signal.mux (stepEqK stepSig 0) a_YmX2
        (Signal.mux (stepEqK stepSig 1) a_YpX2
          (Signal.mux (stepEqK stepSig 2) t2S
            (Signal.mux (stepEqK stepSig 3) m2S
              (Signal.mux (stepEqK stepSig 4) z2S
                (Signal.mux (stepEqK stepSig 5) a_F
                  (Signal.mux (stepEqK stepSig 6) a_H
                    (Signal.mux (stepEqK stepSig 7) a_G a_H)))))))
        : Signal dom (BitVec 256))

    let engA := (Signal.mux opDSig dblA addA : Signal dom (BitVec 256))
    let engB := (Signal.mux opDSig dblB addB : Signal dom (BitVec 256))

    let engRes := mulResult
    let engDone := mulDone

    -- Last step: double = 7, add = 8.
    let lastStep := (Signal.mux opDSig (stepEqK stepSig 7) (stepEqK stepSig 8) : Signal dom Bool)
    let stepAck := (isWait &&& engDone : Signal dom Bool)
    let atLast := (stepAck &&& lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))
    let stepInc := (stepSig + p1_5 : Signal dom (BitVec 5))
    stepR <~ Signal.mux start p0_5
              (Signal.mux advance stepInc stepSig)
    opDR <~ Signal.mux start opDouble opDSig
    ax1R <~ Signal.mux start x1 x1S
    ay1R <~ Signal.mux start y1 y1S
    az1R <~ Signal.mux start z1 z1S
    at1R <~ Signal.mux start t1 t1S
    ax2R <~ Signal.mux start x2 x2S
    ay2R <~ Signal.mux start y2 y2S
    az2R <~ Signal.mux start z2 z2S
    at2R <~ Signal.mux start t2 t2S

    m0R <~ latchIntoK stepAck stepSig engRes 0 m0S
    m1R <~ latchIntoK stepAck stepSig engRes 1 m1S
    m2R <~ latchIntoK stepAck stepSig engRes 2 m2S
    m3R <~ latchIntoK stepAck stepSig engRes 3 m3S
    m4R <~ latchIntoK stepAck stepSig engRes 4 m4S
    m5R <~ latchIntoK stepAck stepSig engRes 5 m5S
    m6R <~ latchIntoK stepAck stepSig engRes 6 m6S
    m7R <~ latchIntoK stepAck stepSig engRes 7 m7S
    m8R <~ latchIntoK stepAck stepSig engRes 8 m8S

    doneR <~ atLast

    -- Outputs.  DOUBLE: X3=m4,Y3=m5,Z3=m6,T3=m7.  ADD: X3=m5,Y3=m6,Z3=m7,T3=m8.
    let xOut := (Signal.mux opDSig m4S m5S : Signal dom (BitVec 256))
    let yOut := (Signal.mux opDSig m5S m6S : Signal dom (BitVec 256))
    let zOut := (Signal.mux opDSig m6S m7S : Signal dom (BitVec 256))
    let tOut := (Signal.mux opDSig m7S m8S : Signal dom (BitVec 256))

    return ({ xOut := xOut, yOut := yOut, zOut := zOut, tOut := tOut
            , done := (doneR : Signal dom Bool)
            , mulStart := isTrig
            , mulA := engA
            , mulB := engB
            } : PointOpOut dom)

end Sparkle.IP.Crypto.Ed25519PointOpHW
