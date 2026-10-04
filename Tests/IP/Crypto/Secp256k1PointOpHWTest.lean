/-
  Sim + synth test for IP.Crypto.Secp256k1PointOpHW.pointOpHW —
  the Jacobian point-op FSM (DOUBLE / ADD) that drives the
  bit-serial secp256k1 field multiplier as a sub-engine.

  Behavioural: the FSM sequences a fixed schedule of engine
  multiplies with combinational field add/sub/×k between them.
  This test re-executes that EXACT schedule as a pure-data model
  (`scheduleDouble` / `scheduleAdd` below — a faithful, line-by-
  line transcription of the operand routing encoded in
  `pointOpHW`) and cross-validates the resulting (X,Y,Z) against
  the independent Jacobian reference `Secp256k1PointJac.double`
  / `.add`.  This is what actually de-risks the module: the
  operand schedule is the part that is easy to get wrong, and it
  is checked here against a formula-level reference.

  (The cycle-accurate Signal circuit is validated to *synthesize*
  by the `#synthesizeVerilog` checks below.  Full closed-loop
  cycle co-sim — tying `pointOpHW`'s handshake to a real `mulHW`
  via `Signal.loop` — is left to the JIT-backed harness; the
  interpreted `.val` path over a nested feedback loop is the known
  multi-output-FSM slowdown documented for this repo.)

  Synth: `#synthesizeVerilog` on xOut, done, mulStart.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1Field
import IP.Crypto.Secp256k1FieldHW
import IP.Crypto.Proof.Secp256k1PointJac
import IP.Crypto.Secp256k1PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1PointOpHW

namespace Sparkle.Tests.IP.Crypto.Secp256k1PointOpHWTest

abbrev D := defaultDomain

-- Pure-data field ops matching the module's combinational helpers.
private abbrev fMul := Sparkle.IP.Crypto.Secp256k1Field.mul
private abbrev fAdd := Sparkle.IP.Crypto.Secp256k1Field.add
private abbrev fSub := Sparkle.IP.Crypto.Secp256k1Field.sub
private def fx2 (a : Nat) : Nat := fAdd a a
private def fx3 (a : Nat) : Nat := fAdd a (fx2 a)
private def fx8 (a : Nat) : Nat := fx2 (fx2 (fx2 a))

/-- The DOUBLE schedule EXACTLY as `pointOpHW` routes it:
    the 7 engine multiplies (m0..m6) and the combinational
    intermediates between them.  Returns (X3, Y3, Z3). -/
private def scheduleDouble (X Y Z : Nat) : Nat × Nat × Nat :=
  let m0 := fMul X X            -- A = X*X
  let m1 := fMul Y Y            -- B = Y*Y
  let m2 := fMul m1 m1          -- C = B*B
  let d_XB := fAdd X m1         -- X + B
  let m3 := fMul d_XB d_XB      -- (X+B)^2
  let d_D := fx2 (fSub m3 (fAdd m0 m2))   -- D = 2((X+B)^2 - (A+C))
  let d_E := fx3 m0            -- E = 3A
  let m4 := fMul d_E d_E        -- F = E*E
  let d_X3 := fSub m4 (fx2 d_D)            -- X3 = F - 2D
  let d_DmX3 := fSub d_D d_X3              -- D - X3
  let m5 := fMul d_E d_DmX3     -- E*(D-X3)
  let d_Y3 := fSub m5 (fx8 m2)             -- Y3 = E(D-X3) - 8C
  let m6 := fMul Y Z            -- Y*Z
  let d_Z3 := fx2 m6                        -- Z3 = 2*Y*Z
  (d_X3, d_Y3, d_Z3)

/-- The ADD schedule EXACTLY as `pointOpHW` routes it:
    the 16 engine multiplies (m0..m15) and combinational
    intermediates.  Returns (X3, Y3, Z3). -/
private def scheduleAdd (X1 Y1 Z1 X2 Y2 Z2 : Nat) : Nat × Nat × Nat :=
  let m0 := fMul Z1 Z1          -- Z1Z1
  let m1 := fMul Z2 Z2          -- Z2Z2
  let m2 := fMul X1 m1          -- U1 = X1*Z2Z2
  let m3 := fMul X2 m0          -- U2 = X2*Z1Z1
  let m4 := fMul Z2 m1          -- t_z2c = Z2*Z2Z2
  let m5 := fMul Y1 m4          -- S1 = Y1*t_z2c
  let m6 := fMul Z1 m0          -- t_z1c = Z1*Z1Z1
  let m7 := fMul Y2 m6          -- S2 = Y2*t_z1c
  let a_H := fSub m3 m2         -- H = U2 - U1
  let a_twoH := fx2 a_H         -- 2H
  let m8 := fMul a_twoH a_twoH  -- I = (2H)^2
  let m9 := fMul a_H m8         -- J = H*I
  let a_rr := fx2 (fSub m7 m5)  -- rr = 2*(S2-S1)
  let m10 := fMul m2 m8         -- V = U1*I
  let m11 := fMul a_rr a_rr     -- rr2 = rr*rr
  let a_X3 := fSub (fSub m11 m9) (fx2 m10)  -- X3 = rr2 - J - 2V
  let a_VmX3 := fSub m10 a_X3               -- V - X3
  let m12 := fMul a_rr a_VmX3   -- rr*(V-X3)
  let m13 := fMul m5 m9         -- S1*J
  let a_Y3 := fSub m12 (fx2 m13)            -- Y3 = rVX - 2*S1J
  let a_ZZ := fAdd Z1 Z2        -- Z1 + Z2
  let m14 := fMul a_ZZ a_ZZ     -- sqZZ
  let a_z3t := fSub m14 (fAdd m0 m1)        -- sqZZ - (Z1Z1+Z2Z2)
  let m15 := fMul a_z3t a_H     -- Z3 = z3t*H
  (a_X3, a_Y3, m15)

def main : IO Unit := do
  IO.println "=== secp256k1 Jacobian point-op FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Concrete non-trivial Jacobian points: 3·G and 5·G.
  let P := Sparkle.IP.Crypto.Secp256k1PointJac.mulScalar 3 Sparkle.IP.Crypto.Secp256k1PointJac.generator
  let Q := Sparkle.IP.Crypto.Secp256k1PointJac.mulScalar 5 Sparkle.IP.Crypto.Secp256k1PointJac.generator

  -- DOUBLE: schedule vs. formula reference.
  let dref := Sparkle.IP.Crypto.Secp256k1PointJac.double P
  let (dx, dy, dz) := scheduleDouble P.x P.y P.z
  if dx = dref.x ∧ dy = dref.y ∧ dz = dref.z then
    IO.println "  ✓ DOUBLE schedule matches Jacobian reference"
  else
    IO.println s!"  ✗ DOUBLE mismatch: sched=({dx},{dy},{dz}) ref=({dref.x},{dref.y},{dref.z})"
    ok := false

  -- ADD: schedule vs. formula reference.
  let aref := Sparkle.IP.Crypto.Secp256k1PointJac.add P Q
  let (ax, ay, az) := scheduleAdd P.x P.y P.z Q.x Q.y Q.z
  if ax = aref.x ∧ ay = aref.y ∧ az = aref.z then
    IO.println "  ✓ ADD schedule matches Jacobian reference"
  else
    IO.println s!"  ✗ ADD mismatch: sched=({ax},{ay},{az}) ref=({aref.x},{aref.y},{aref.z})"
    ok := false

  -- Second independent case: 7·G double, (7·G)+(11·G) add.
  let P2 := Sparkle.IP.Crypto.Secp256k1PointJac.mulScalar 7 Sparkle.IP.Crypto.Secp256k1PointJac.generator
  let Q2 := Sparkle.IP.Crypto.Secp256k1PointJac.mulScalar 11 Sparkle.IP.Crypto.Secp256k1PointJac.generator
  let d2 := Sparkle.IP.Crypto.Secp256k1PointJac.double P2
  let (dx2, dy2, dz2) := scheduleDouble P2.x P2.y P2.z
  let a2 := Sparkle.IP.Crypto.Secp256k1PointJac.add P2 Q2
  let (ax2, ay2, az2) := scheduleAdd P2.x P2.y P2.z Q2.x Q2.y Q2.z
  if dx2 = d2.x ∧ dy2 = d2.y ∧ dz2 = d2.z ∧ ax2 = a2.x ∧ ay2 = a2.y ∧ az2 = a2.z then
    IO.println "  ✓ second case (7·G, 7·G+11·G) matches"
  else
    IO.println "  ✗ second case mismatch"
    ok := false

  IO.println s!"  · cycle cost per op (real mulHW, 258 cyc/mul + handshake):"
  IO.println s!"      DOUBLE ≈ 7 muls  → ~{7 * 260} cycles"
  IO.println s!"      ADD    ≈ 16 muls → ~{16 * 260} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Secp256k1PointOpHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1PointOpHW

private def synth_secp256k1PointOpX
    (start : Signal defaultDomain Bool)
    (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 x2 y2 z2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone).xOut

#synthesizeVerilog synth_secp256k1PointOpX

private def synth_secp256k1PointOpDone
    (start : Signal defaultDomain Bool)
    (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 x2 y2 z2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone).done

#synthesizeVerilog synth_secp256k1PointOpDone

private def synth_secp256k1PointOpMulStart
    (start : Signal defaultDomain Bool)
    (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 x2 y2 z2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone).mulStart

#synthesizeVerilog synth_secp256k1PointOpMulStart

end SynthesisChecks
