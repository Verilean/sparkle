/-
  Sim + synth test for IP.Crypto.P256PointOpHW.pointOpHW — the
  P-256 (a = -3) Jacobian point-op FSM.

  Re-executes the EXACT multiply schedule the FSM routes (both the
  a = -3 DOUBLE and the add-2007-bl ADD) as a pure-data model and
  cross-validates (X,Y,Z) against the independent Jacobian
  reference `P256PointJac.double`/`.add`.  The operand schedule is
  the part easy to get wrong; it is checked here against a
  formula-level reference (itself already locked against the affine
  `P256Point` in `P256PointJacTest`).

  Synth: `#synthesizeVerilog` on xOut, done, mulStart.
-/
import Sparkle
import IP.Crypto.Proof.P256Field
import IP.Crypto.P256FieldHW
import IP.Crypto.Proof.P256PointJac
import IP.Crypto.P256PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256PointOpHW

namespace Sparkle.Tests.IP.Crypto.P256PointOpHWTest

abbrev D := defaultDomain

private abbrev fMul := Sparkle.IP.Crypto.P256Field.mul
private abbrev fAdd := Sparkle.IP.Crypto.P256Field.add
private abbrev fSub := Sparkle.IP.Crypto.P256Field.sub
private def fx2 (a : Nat) : Nat := fAdd a a
private def fx3 (a : Nat) : Nat := fAdd a (fx2 a)
private def fx4 (a : Nat) : Nat := fx2 (fx2 a)
private def fx8 (a : Nat) : Nat := fx2 (fx2 (fx2 a))

/-- The a = -3 DOUBLE schedule EXACTLY as `pointOpHW` routes it:
    8 engine multiplies (m0..m7) + combinational intermediates.
    Returns (X3, Y3, Z3). -/
private def scheduleDouble (X Y Z : Nat) : Nat × Nat × Nat :=
  let m0 := fMul Z Z                       -- δ = Z²
  let m1 := fMul Y Y                       -- γ = Y²
  let m2 := fMul X m1                       -- β = X·γ
  let d_XmD := fSub X m0                    -- X - δ
  let d_XpD := fAdd X m0                    -- X + δ
  let m3 := fMul d_XmD d_XpD                -- (X-δ)(X+δ)
  let d_alpha := fx3 m3                      -- α = 3·m3
  let m4 := fMul d_alpha d_alpha            -- α²
  let d_YpZ := fAdd Y Z                     -- Y + Z
  let m5 := fMul d_YpZ d_YpZ                -- (Y+Z)²
  let d_X3 := fSub m4 (fx8 m2)              -- X3 = α² - 8β
  let d_Z3 := fSub (fSub m5 m1) m0          -- Z3 = (Y+Z)² - γ - δ
  let d_4bmX3 := fSub (fx4 m2) d_X3         -- 4β - X3
  let m6 := fMul d_alpha d_4bmX3            -- α(4β-X3)
  let m7 := fMul m1 m1                       -- γ²
  let d_Y3 := fSub m6 (fx8 m7)              -- Y3 = α(4β-X3) - 8γ²
  (d_X3, d_Y3, d_Z3)

/-- The ADD schedule EXACTLY as `pointOpHW` routes it (add-2007-bl,
    curve-independent).  Returns (X3, Y3, Z3). -/
private def scheduleAdd (X1 Y1 Z1 X2 Y2 Z2 : Nat) : Nat × Nat × Nat :=
  let m0 := fMul Z1 Z1
  let m1 := fMul Z2 Z2
  let m2 := fMul X1 m1
  let m3 := fMul X2 m0
  let m4 := fMul Z2 m1
  let m5 := fMul Y1 m4
  let m6 := fMul Z1 m0
  let m7 := fMul Y2 m6
  let a_H := fSub m3 m2
  let a_twoH := fx2 a_H
  let m8 := fMul a_twoH a_twoH
  let m9 := fMul a_H m8
  let a_rr := fx2 (fSub m7 m5)
  let m10 := fMul m2 m8
  let m11 := fMul a_rr a_rr
  let a_X3 := fSub (fSub m11 m9) (fx2 m10)
  let a_VmX3 := fSub m10 a_X3
  let m12 := fMul a_rr a_VmX3
  let m13 := fMul m5 m9
  let a_Y3 := fSub m12 (fx2 m13)
  let a_ZZ := fAdd Z1 Z2
  let m14 := fMul a_ZZ a_ZZ
  let a_z3t := fSub m14 (fAdd m0 m1)
  let m15 := fMul a_z3t a_H
  (a_X3, a_Y3, m15)

def main : IO Unit := do
  IO.println "=== P-256 (a=-3) Jacobian point-op FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let P := Sparkle.IP.Crypto.P256PointJac.mulScalar 3 Sparkle.IP.Crypto.P256PointJac.generator
  let Q := Sparkle.IP.Crypto.P256PointJac.mulScalar 5 Sparkle.IP.Crypto.P256PointJac.generator

  let dref := Sparkle.IP.Crypto.P256PointJac.double P
  let (dx, dy, dz) := scheduleDouble P.x P.y P.z
  if dx = dref.x ∧ dy = dref.y ∧ dz = dref.z then
    IO.println "  ✓ DOUBLE (a=-3) schedule matches Jacobian reference"
  else
    IO.println s!"  ✗ DOUBLE mismatch: sched=({dx},{dy},{dz}) ref=({dref.x},{dref.y},{dref.z})"
    ok := false

  let aref := Sparkle.IP.Crypto.P256PointJac.add P Q
  let (ax, ay, az) := scheduleAdd P.x P.y P.z Q.x Q.y Q.z
  if ax = aref.x ∧ ay = aref.y ∧ az = aref.z then
    IO.println "  ✓ ADD schedule matches Jacobian reference"
  else
    IO.println s!"  ✗ ADD mismatch: sched=({ax},{ay},{az}) ref=({aref.x},{aref.y},{aref.z})"
    ok := false

  let P2 := Sparkle.IP.Crypto.P256PointJac.mulScalar 7 Sparkle.IP.Crypto.P256PointJac.generator
  let Q2 := Sparkle.IP.Crypto.P256PointJac.mulScalar 11 Sparkle.IP.Crypto.P256PointJac.generator
  let d2 := Sparkle.IP.Crypto.P256PointJac.double P2
  let (dx2, dy2, dz2) := scheduleDouble P2.x P2.y P2.z
  let a2 := Sparkle.IP.Crypto.P256PointJac.add P2 Q2
  let (ax2, ay2, az2) := scheduleAdd P2.x P2.y P2.z Q2.x Q2.y Q2.z
  if dx2 = d2.x ∧ dy2 = d2.y ∧ dz2 = d2.z ∧ ax2 = a2.x ∧ ay2 = a2.y ∧ az2 = a2.z then
    IO.println "  ✓ second case (7·G, 7·G+11·G) matches"
  else
    IO.println "  ✗ second case mismatch"
    ok := false

  IO.println s!"  · cycle cost (real mulHW, ~260 cyc/mul): DOUBLE ~{8*260}, ADD ~{16*260}"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.P256PointOpHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256PointOpHW

private def synth_p256PointOpX
    (start : Signal defaultDomain Bool)
    (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 x2 y2 z2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone).xOut

#synthesizeVerilog synth_p256PointOpX

private def synth_p256PointOpDone
    (start : Signal defaultDomain Bool)
    (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 x2 y2 z2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone).done

#synthesizeVerilog synth_p256PointOpDone

private def synth_p256PointOpMulStart
    (start : Signal defaultDomain Bool)
    (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 x2 y2 z2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone).mulStart

#synthesizeVerilog synth_p256PointOpMulStart

end SynthesisChecks
