/-
  Sim + synth test for IP.Crypto.Ed25519PointOpHW.pointOpHW —
  the extended twisted-Edwards point-op FSM (DOUBLE / ADD) that
  drives the bit-serial Ed25519 field multiplier as a sub-engine.

  Behavioural: `scheduleDouble` / `scheduleAdd` re-execute the
  EXACT operand routing encoded in `pointOpHW` (line-by-line) and
  cross-validate the resulting (X,Y,Z,T) against the independent
  reference `Ed25519PointExt.double` / `.add`.  This de-risks the
  operand schedule.  The cycle-accurate Signal circuit is proven
  to *synthesize* by the `#synthesizeVerilog` checks below (closed-
  loop cycle co-sim is left to the JIT harness, per the repo's
  documented `.val`-over-feedback-loop slowdown).

  Synth: `#synthesizeVerilog` on xOut, done.
-/
import Sparkle
import IP.Crypto.Ed25519Field
import IP.Crypto.Ed25519FieldHW
import IP.Crypto.Ed25519PointExt
import IP.Crypto.Ed25519PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519PointOpHW

namespace Sparkle.Tests.IP.Crypto.Ed25519PointOpHWTest

abbrev D := defaultDomain

private abbrev fMul := Sparkle.IP.Crypto.Ed25519Field.mul
private abbrev fAdd := Sparkle.IP.Crypto.Ed25519Field.add
private abbrev fSub := Sparkle.IP.Crypto.Ed25519Field.sub
private def fx2 (a : Nat) : Nat := fAdd a a
private def fneg (a : Nat) : Nat := fSub 0 a
private abbrev dConst := Sparkle.IP.Crypto.Ed25519Point.d

/-- DOUBLE schedule EXACTLY as `pointOpHW` routes it (8 muls). -/
private def scheduleDouble (X Y Z _T : Nat) : Nat × Nat × Nat × Nat :=
  let m0 := fMul X X            -- A
  let m1 := fMul Y Y            -- B
  let m2 := fMul Z Z            -- Z²
  let d_XY := fAdd X Y
  let m3 := fMul d_XY d_XY      -- (X+Y)²
  let d_C := fx2 m2             -- C = 2Z²
  let d_D := fneg m0            -- D = -A
  let d_E := fSub (fSub m3 m0) m1  -- E = (X+Y)²-A-B
  let d_G := fAdd d_D m1        -- G = D+B
  let d_F := fSub d_G d_C       -- F = G-C
  let d_H := fSub d_D m1        -- H = D-B
  let m4 := fMul d_E d_F        -- X3 = E*F
  let m5 := fMul d_G d_H        -- Y3 = G*H
  let m6 := fMul d_F d_G        -- Z3 = F*G
  let m7 := fMul d_E d_H        -- T3 = E*H
  (m4, m5, m6, m7)

/-- ADD schedule EXACTLY as `pointOpHW` routes it (9 muls). -/
private def scheduleAdd (X1 Y1 Z1 T1 X2 Y2 Z2 T2 : Nat) : Nat × Nat × Nat × Nat :=
  let m0 := fMul (fSub Y1 X1) (fSub Y2 X2)   -- A
  let m1 := fMul (fAdd Y1 X1) (fAdd Y2 X2)   -- B
  let m2 := fMul dConst T2                    -- d*T2
  let m3 := fMul (fx2 T1) m2                  -- C = (2T1)*(d*T2)
  let m4 := fMul Z1 Z2                         -- Z1*Z2
  let a_D := fx2 m4                            -- D = 2Z1Z2
  let a_E := fSub m1 m0                        -- E = B-A
  let a_F := fSub a_D m3                       -- F = D-C
  let a_G := fAdd a_D m3                       -- G = D+C
  let a_H := fAdd m1 m0                        -- H = B+A
  let m5 := fMul a_E a_F        -- X3
  let m6 := fMul a_G a_H        -- Y3
  let m7 := fMul a_F a_G        -- Z3
  let m8 := fMul a_E a_H        -- T3
  (m5, m6, m7, m8)

open Sparkle.IP.Crypto.Ed25519PointExt (Point mulScalar generator double add)

def main : IO Unit := do
  IO.println "=== Ed25519 extended-coords point-op FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let P := mulScalar 3 generator
  let Q := mulScalar 5 generator

  let dref := double P
  let (dx, dy, dz, dt) := scheduleDouble P.x P.y P.z P.t
  if dx = dref.x ∧ dy = dref.y ∧ dz = dref.z ∧ dt = dref.t then
    IO.println "  ✓ DOUBLE schedule matches Ed25519PointExt.double"
  else
    IO.println s!"  ✗ DOUBLE mismatch"; ok := false

  let aref := add P Q
  let (ax, ay, az, atc) := scheduleAdd P.x P.y P.z P.t Q.x Q.y Q.z Q.t
  if ax = aref.x ∧ ay = aref.y ∧ az = aref.z ∧ atc = aref.t then
    IO.println "  ✓ ADD schedule matches Ed25519PointExt.add"
  else
    IO.println s!"  ✗ ADD mismatch"; ok := false

  -- Second case: 7·G double, (7·G)+(11·G) add.
  let P2 := mulScalar 7 generator
  let Q2 := mulScalar 11 generator
  let d2 := double P2
  let (dx2, dy2, dz2, dt2) := scheduleDouble P2.x P2.y P2.z P2.t
  let a2 := add P2 Q2
  let (ax2, ay2, az2, at2c) := scheduleAdd P2.x P2.y P2.z P2.t Q2.x Q2.y Q2.z Q2.t
  if dx2 = d2.x ∧ dy2 = d2.y ∧ dz2 = d2.z ∧ dt2 = d2.t
     ∧ ax2 = a2.x ∧ ay2 = a2.y ∧ az2 = a2.z ∧ at2c = a2.t then
    IO.println "  ✓ second case (7·G, 7·G+11·G) matches"
  else
    IO.println "  ✗ second case mismatch"; ok := false

  IO.println s!"  · cycle cost per op (real mulHW, 258 cyc/mul + handshake):"
  IO.println s!"      DOUBLE ≈ 8 muls → ~{8 * 260} cycles"
  IO.println s!"      ADD    ≈ 9 muls → ~{9 * 260} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Ed25519PointOpHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519PointOpHW

private def synth_ed25519PointOpX
    (start : Signal defaultDomain Bool) (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 t1 x2 y2 z2 t2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256)) (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (pointOpHW start opDouble x1 y1 z1 t1 x2 y2 z2 t2 mulResult mulDone).xOut

#synthesizeVerilog synth_ed25519PointOpX

private def synth_ed25519PointOpDone
    (start : Signal defaultDomain Bool) (opDouble : Signal defaultDomain Bool)
    (x1 y1 z1 t1 x2 y2 z2 t2 : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256)) (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (pointOpHW start opDouble x1 y1 z1 t1 x2 y2 z2 t2 mulResult mulDone).done

#synthesizeVerilog synth_ed25519PointOpDone

end SynthesisChecks
