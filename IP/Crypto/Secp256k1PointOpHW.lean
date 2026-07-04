/-
  IP.Crypto.Secp256k1PointOpHW — one Jacobian point operation
  (double OR add) on secp256k1, as a `circuit do` FSM that drives
  the bit-serial field multiplier `Secp256k1FieldHW.mulHW` as a
  shared sub-engine via its start/done handshake.

  The point op is selected by `opDouble` (latched on `start`):
    * true  ⇒ DOUBLE (X,Y,Z)            — 7 engine multiplies
    * false ⇒ ADD    (X1,Y1,Z1)+(X2,Y2,Z2) — 16 engine multiplies

  Only field *multiplies* use the engine; field add/sub and
  multiply-by-small-constant (×2, ×3, ×8) are combinational
  (single conditional reduce mod p), folded into the per-step
  operand-selection muxes.

  Formulas (a = 0 short Weierstrass, matching Secp256k1PointJac):
    DOUBLE dbl-2009-l, ADD add-2007-bl (generic branch — the
    caller/ladder guarantees the two inputs are distinct, so the
    u₁=u₂ special-cases are not exercised here).

  The field multiplier is NOT instantiated inside this module —
  it is driven over an *external* start/done handshake (the same
  synthesizable composition style as `HKDFHW` / `AESGCMHW`, where
  the sub-engine is a plug-in wired at the next level up).  A
  higher-level module (the scalar-mul controller) or a testbench
  connects a `Secp256k1FieldHW.mulHW` instance to the exposed
  `mulStart`/`mulA`/`mulB` ports and routes its `result`/`done`
  back into `mulResult`/`mulDone`.

  Interface:
    inputs  start (Bool pulse) — latch operands, begin
            opDouble (Bool)    — op selector (latched)
            x1,y1,z1           — first point (BitVec 256)
            x2,y2,z2           — second point (ADD only)
            mulResult          — field-multiplier result in
            mulDone (Bool)     — field-multiplier done in
    outputs xOut,yOut,zOut     — result coords (valid at `done`)
            done (Bool pulse)  — result ready
            mulStart (Bool)    — pulse the field multiplier
            mulA,mulB          — operands for the field multiplier

  Timing: each engine multiply is 258 cycles + 2 handshake
  cycles (trigger + latch) ≈ 260 cycles/step.  DOUBLE ≈ 7 steps,
  ADD ≈ 16 steps.  `done` pulses one cycle after the last step's
  result is latched.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1Field
import IP.Crypto.Secp256k1FieldHW

namespace Sparkle.IP.Crypto.Secp256k1PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- secp256k1 prime as a 257-bit constant (headroom for a+b and
    a+p-b combinational reductions, both < 2p < 2^257). -/
def pBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Secp256k1Field.p

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

/-- Field add mod p (combinational): widen to 257, add, single
    conditional subtract of p. -/
private def faddMod {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := ((· + ·) <$> aw <*> bw : Signal dom (BitVec 257))
  let pP := (Signal.pure pBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> pP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Field sub mod p (combinational): compute a + p - b in 257
    bits (always in [0, 2p)), then one conditional subtract. -/
private def fsubMod {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let pP := (Signal.pure pBv257 : Signal dom (BitVec 257))
  let apb := ((· + ·) <$> aw <*> pP : Signal dom (BitVec 257))     -- a + p  (< 2^257)
  let s   := ((· - ·) <$> apb <*> bw : Signal dom (BitVec 257))    -- a + p - b  (in [0, 2p))
  let ge  := ((BitVec.ule · ·) <$> pP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> pP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Field ×2 (combinational). -/
private def fx2 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := faddMod a a

/-- Field ×3 (combinational). -/
private def fx3 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := faddMod a (fx2 a)

/-- Field ×8 (combinational). -/
private def fx8 {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) := fx2 (fx2 (fx2 a))

/-- `stepSig == k` as a Bool signal (step-index compare helper). -/
private def stepEqK {dom : DomainConfig}
    (stepSig : Signal dom (BitVec 6)) (k : Nat) : Signal dom Bool :=
  ((· == ·) <$> stepSig <*> (Signal.pure (BitVec.ofNat 6 k) : Signal dom (BitVec 6)))

/-- Next value for scratch register `k`: on a step-ack for step `k`
    take the engine result, else hold. -/
private def latchIntoK {dom : DomainConfig}
    (stepAck : Signal dom Bool) (stepSig : Signal dom (BitVec 6))
    (engRes : Signal dom (BitVec 256)) (k : Nat)
    (cur : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  Signal.mux ((· && ·) <$> stepAck <*> stepEqK stepSig k) engRes cur

/-- One Jacobian point op (double or add) FSM. -/
def pointOpHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (opDouble : Signal dom Bool)
    (x1 y1 z1 : Signal dom (BitVec 256))
    (x2 y2 z2 : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256))
    (mulDone : Signal dom Bool) :
    PointOpOut dom :=
  circuit do
    -- FSM phase: 0 = idle, 1 = trigger multiply, 2 = wait for done, 3 = complete.
    let stR ← Signal.reg (0#2)
    -- Step index 0..15 (which multiply of the schedule we are on).
    let stepR ← Signal.reg (0#6)
    -- Op selector, latched on start.
    let opDR ← Signal.reg false
    -- Latched input coordinates.
    let ax1R ← Signal.reg (0#256)
    let ay1R ← Signal.reg (0#256)
    let az1R ← Signal.reg (0#256)
    let ax2R ← Signal.reg (0#256)
    let ay2R ← Signal.reg (0#256)
    let az2R ← Signal.reg (0#256)
    -- Scratch registers for engine-multiply results (m0..m15).
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
    -- Sticky done flag.
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

    -- Phase constants.
    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let p0_6 := (Signal.pure 0#6 : Signal dom (BitVec 6))
    let p1_6 := (Signal.pure 1#6 : Signal dom (BitVec 6))

    let isTrig := ((· == ·) <$> stSig <*> p1_2 : Signal dom Bool)
    let isWait := ((· == ·) <$> stSig <*> p2_2 : Signal dom Bool)

    -- ================= DOUBLE combinational operand exprs =================
    -- m0=X*X m1=Y*Y m2=B*B(=m1*m1) m3=XB*XB m4=E*E m5=E*DmX3 m6=Y*Z
    -- comb intermediates on double path:
    let d_XB   := faddMod x1S m1S                       -- X + B
    let d_D    := fx2 (fsubMod m3S (faddMod m0S m2S))    -- 2*((X+B)^2 - (A+C))
    let d_E    := fx3 m0S                                -- 3*A
    let d_X3   := fsubMod m4S (fx2 d_D)                  -- F - 2D
    let d_DmX3 := fsubMod d_D d_X3                       -- D - X3
    let d_Y3   := fsubMod m5S (fx8 m2S)                  -- E(D-X3) - 8C
    let d_Z3   := fx2 m6S                                -- 2*Y*Z

    -- ================= ADD combinational operand exprs =================
    -- m0=Z1Z1 m1=Z2Z2 m2=U1 m3=U2 m4=Z2*Z2Z2 m5=S1 m6=Z1*Z1Z1 m7=S2
    -- m8=I(=twoH^2) m9=J(=H*I) m10=V(=U1*I) m11=rr2 m12=rVX m13=S1J
    -- m14=sqZZ m15=Z3(=z3t*H)
    let a_H    := fsubMod m3S m2S                        -- U2 - U1
    let a_twoH := fx2 a_H                                -- 2H
    let a_rr   := fx2 (fsubMod m7S m5S)                  -- 2*(S2 - S1)
    let a_X3   := fsubMod (fsubMod m11S m9S) (fx2 m10S)  -- rr2 - J - 2V
    let a_VmX3 := fsubMod m10S a_X3                      -- V - X3
    let a_Y3   := fsubMod m12S (fx2 m13S)                -- rVX - 2*S1J
    let a_ZZ   := faddMod z1S z2S                        -- Z1 + Z2
    let a_z3t  := fsubMod m14S (faddMod m0S m1S)         -- sqZZ - (Z1Z1+Z2Z2)

    -- ================= operand A/B selection per (opDouble, step) =================
    -- Build the two operands for the current engine multiply.
    -- DOUBLE operands:
    let dblA :=
      (Signal.mux (stepEqK stepSig 0) x1S
        (Signal.mux (stepEqK stepSig 1) y1S
          (Signal.mux (stepEqK stepSig 2) m1S
            (Signal.mux (stepEqK stepSig 3) d_XB
              (Signal.mux (stepEqK stepSig 4) d_E
                (Signal.mux (stepEqK stepSig 5) d_E
                  (Signal.mux (stepEqK stepSig 6) y1S x1S)))))) : Signal dom (BitVec 256))
    let dblB :=
      (Signal.mux (stepEqK stepSig 0) x1S
        (Signal.mux (stepEqK stepSig 1) y1S
          (Signal.mux (stepEqK stepSig 2) m1S
            (Signal.mux (stepEqK stepSig 3) d_XB
              (Signal.mux (stepEqK stepSig 4) d_E
                (Signal.mux (stepEqK stepSig 5) d_DmX3
                  (Signal.mux (stepEqK stepSig 6) z1S x1S)))))) : Signal dom (BitVec 256))
    -- ADD operands:
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
          (Signal.mux (stepEqK stepSig 2) m1S     -- U1 = X1 * Z2Z2
            (Signal.mux (stepEqK stepSig 3) m0S     -- U2 = X2 * Z1Z1
              (Signal.mux (stepEqK stepSig 4) m1S   -- t_z2c = Z2 * Z2Z2
                (Signal.mux (stepEqK stepSig 5) m4S -- S1 = Y1 * t_z2c
                  (Signal.mux (stepEqK stepSig 6) m0S   -- t_z1c = Z1 * Z1Z1
                    (Signal.mux (stepEqK stepSig 7) m6S -- S2 = Y2 * t_z1c
                      (Signal.mux (stepEqK stepSig 8) a_twoH   -- I = twoH^2
                        (Signal.mux (stepEqK stepSig 9) m8S    -- J = H * I
                          (Signal.mux (stepEqK stepSig 10) m8S -- V = U1 * I
                            (Signal.mux (stepEqK stepSig 11) a_rr    -- rr2 = rr*rr
                              (Signal.mux (stepEqK stepSig 12) a_VmX3 -- rVX = rr*(V-X3)
                                (Signal.mux (stepEqK stepSig 13) m9S  -- S1J = S1 * J
                                  (Signal.mux (stepEqK stepSig 14) a_ZZ    -- sqZZ = ZZ*ZZ
                                    (Signal.mux (stepEqK stepSig 15) a_H z1S))))))))))))))) -- Z3 = z3t*H
        : Signal dom (BitVec 256))

    let engA := (Signal.mux opDSig dblA addA : Signal dom (BitVec 256))
    let engB := (Signal.mux opDSig dblB addB : Signal dom (BitVec 256))

    -- The field multiplier is external: trigger on the trigger
    -- phase, and consume its result/done over the handshake ports.
    let engRes := mulResult
    let engDone := mulDone

    -- Last step index depends on the op (double = 6, add = 15).
    let lastStep := (Signal.mux opDSig (stepEqK stepSig 6) (stepEqK stepSig 15) : Signal dom Bool)
    -- Step completes when we are waiting and the engine reports done.
    let stepAck := ((· && ·) <$> isWait <*> engDone : Signal dom Bool)
    let atLast := ((· && ·) <$> stepAck <*> lastStep : Signal dom Bool)
    let advance := ((fun s l => s && !l) <$> stepAck <*> lastStep : Signal dom Bool)

    -- ================= register updates =================
    -- Phase transitions:
    --   start ⇒ trigger (1)
    --   trigger ⇒ wait (2)
    --   wait & ack & not-last ⇒ trigger (1)
    --   wait & ack & last ⇒ complete (3)
    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux stepAck
                  (Signal.mux lastStep p3_2 p1_2)
                  stSig))

    -- Step index: 0 on start, +1 on advance.
    let stepInc := ((· + ·) <$> stepSig <*> p1_6 : Signal dom (BitVec 6))
    stepR <~ Signal.mux start p0_6
              (Signal.mux advance stepInc stepSig)

    -- Op selector latched on start.
    opDR <~ Signal.mux start opDouble opDSig

    -- Coordinate latches on start.
    ax1R <~ Signal.mux start x1 x1S
    ay1R <~ Signal.mux start y1 y1S
    az1R <~ Signal.mux start z1 z1S
    ax2R <~ Signal.mux start x2 x2S
    ay2R <~ Signal.mux start y2 y2S
    az2R <~ Signal.mux start z2 z2S

    -- Scratch latches: on stepAck, write engRes into scratch[stepSig].
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

    -- Done pulse: one cycle when the last step is acked.
    doneR <~ atLast

    -- ================= outputs =================
    -- Selected at the done cycle from the final combinational exprs.
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

end Sparkle.IP.Crypto.Secp256k1PointOpHW
