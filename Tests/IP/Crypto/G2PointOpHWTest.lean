/-
  Sim + synth test for IP.Crypto.G2PointOpHW.g2PointOpHW — the
  BLS12-381 G2 Jacobian point-op FSM (DOUBLE / ADD) that drives
  the Fp2 multiplier as a sub-engine.

  Behavioural: the FSM sequences a fixed schedule of Fp2
  multiplies with combinational Fp2 add/sub/×k between them (the
  same 7-mul / 16-mul a=0 schedule as secp256k1, over Fp2).  This
  test re-executes that EXACT schedule as a pure-data model
  (`scheduleDouble` / `scheduleAdd`, over `BLS12_381.Fp2`
  arithmetic) and cross-validates the resulting (X,Y,Z) against
  the independent reference `BLS12_381.G2.double` / `.add`.

  (Full closed-loop cycle co-sim is left to the JIT harness; the
  interpreted `.val` path over a nested feedback loop is the known
  multi-output-FSM slowdown documented for this repo.)

  SYNTH PUNTED.  The `g2PointOpHW` *module* elaborates to
  `Signal.loop` and builds clean (`lake build IP.Crypto.G2PointOpHW`
  succeeds in ~1s).  But `#synthesizeVerilog` on it does NOT
  complete within 9+ minutes even for a single output port — it
  hits the known super-linear "repeat-walk" translate wall (the
  same wall SHA512BlockHW / the 25-lane Keccak256HW FSM punt their
  synth on): this FSM has 32 scratch registers × 384 bits selected
  through 16-way `stepEqK` mux chains, which the current wire
  translator re-walks combinatorially.  Rather than fake a pass we
  omit the `#synthesizeVerilog` checks here and rely on (a) the
  module building (elaboration to Signal.loop), (b) this
  schedule-level cross-check against the Fp2 formula reference, and
  (c) the fully-synthesizing lower layer `Fp2MulHW`.  Unblocking the
  synth needs the compiler-perf translate-cache fix tracked in
  MEMORY as the known slowness root.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.Fp2MulHW
import IP.Crypto.G2PointOpHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.G2PointOpHW
open Sparkle.IP.Crypto.BLS12_381

namespace Sparkle.Tests.IP.Crypto.G2PointOpHWTest

abbrev D := defaultDomain
abbrev E2 := Fp2.El

private def f2mul (a b : E2) : E2 := Fp2.mul a b
private def f2add (a b : E2) : E2 := Fp2.add a b
private def f2sub (a b : E2) : E2 := Fp2.sub a b
private def f2x2 (a : E2) : E2 := Fp2.scaleFp a 2
private def f2x3 (a : E2) : E2 := Fp2.scaleFp a 3
private def f2x8 (a : E2) : E2 := Fp2.scaleFp a 8

/-- DOUBLE schedule EXACTLY as `g2PointOpHW` routes it (over Fp2).
    Returns (X3, Y3, Z3). -/
private def scheduleDouble (X Y Z : E2) : E2 × E2 × E2 :=
  let m0 := f2mul X X            -- A
  let m1 := f2mul Y Y            -- B
  let m2 := f2mul m1 m1          -- C
  let d_XB := f2add X m1
  let m3 := f2mul d_XB d_XB      -- (X+B)^2
  let d_D := f2x2 (f2sub m3 (f2add m0 m2))   -- D
  let d_E := f2x3 m0            -- E
  let m4 := f2mul d_E d_E        -- F
  let d_X3 := f2sub m4 (f2x2 d_D)
  let d_DmX3 := f2sub d_D d_X3
  let m5 := f2mul d_E d_DmX3
  let d_Y3 := f2sub m5 (f2x8 m2)
  let m6 := f2mul Y Z
  let d_Z3 := f2x2 m6
  (d_X3, d_Y3, d_Z3)

/-- ADD schedule EXACTLY as `g2PointOpHW` routes it (over Fp2).
    Returns (X3, Y3, Z3). -/
private def scheduleAdd (X1 Y1 Z1 X2 Y2 Z2 : E2) : E2 × E2 × E2 :=
  let m0 := f2mul Z1 Z1          -- Z1Z1
  let m1 := f2mul Z2 Z2          -- Z2Z2
  let m2 := f2mul X1 m1          -- U1
  let m3 := f2mul X2 m0          -- U2
  let m4 := f2mul Z2 m1          -- t_z2c
  let m5 := f2mul Y1 m4          -- S1
  let m6 := f2mul Z1 m0          -- t_z1c
  let m7 := f2mul Y2 m6          -- S2
  let a_H := f2sub m3 m2         -- H
  let a_twoH := f2x2 a_H
  let m8 := f2mul a_twoH a_twoH  -- I
  let m9 := f2mul a_H m8         -- J
  let a_rr := f2x2 (f2sub m7 m5) -- rr
  let m10 := f2mul m2 m8         -- V
  let m11 := f2mul a_rr a_rr     -- rr2
  let a_X3 := f2sub (f2sub m11 m9) (f2x2 m10)
  let a_VmX3 := f2sub m10 a_X3
  let m12 := f2mul a_rr a_VmX3
  let m13 := f2mul m5 m9         -- S1J
  let a_Y3 := f2sub m12 (f2x2 m13)
  let a_ZZ := f2add Z1 Z2
  let m14 := f2mul a_ZZ a_ZZ     -- sqZZ
  let a_z3t := f2sub m14 (f2add m0 m1)
  let m15 := f2mul a_z3t a_H     -- Z3
  (a_X3, a_Y3, m15)

def main : IO Unit := do
  IO.println "=== BLS12-381 G2 Jacobian point-op FSM schedule check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Non-trivial G2 points: 3·G2 and 5·G2.
  let P := G2.mulScalar 3 G2.generator
  let Q := G2.mulScalar 5 G2.generator

  let dref := G2.double P
  let (dx, dy, dz) := scheduleDouble P.x P.y P.z
  if dx = dref.x ∧ dy = dref.y ∧ dz = dref.z then
    IO.println "  ✓ DOUBLE schedule matches G2.double reference"
  else
    IO.println "  ✗ DOUBLE mismatch"
    ok := false

  let aref := G2.add P Q
  let (ax, ay, az) := scheduleAdd P.x P.y P.z Q.x Q.y Q.z
  if ax = aref.x ∧ ay = aref.y ∧ az = aref.z then
    IO.println "  ✓ ADD schedule matches G2.add reference"
  else
    IO.println "  ✗ ADD mismatch"
    ok := false

  -- Second independent case: 7·G2 double, (7·G2)+(11·G2) add.
  let P2 := G2.mulScalar 7 G2.generator
  let Q2 := G2.mulScalar 11 G2.generator
  let d2 := G2.double P2
  let (dx2, dy2, dz2) := scheduleDouble P2.x P2.y P2.z
  let a2 := G2.add P2 Q2
  let (ax2, ay2, az2) := scheduleAdd P2.x P2.y P2.z Q2.x Q2.y Q2.z
  if dx2 = d2.x ∧ dy2 = d2.y ∧ dz2 = d2.z ∧ ax2 = a2.x ∧ ay2 = a2.y ∧ az2 = a2.z then
    IO.println "  ✓ second case (7·G2, 7·G2+11·G2) matches"
  else
    IO.println "  ✗ second case mismatch"
    ok := false

  IO.println s!"  · cycle cost per op (Fp2-mul ~48 cyc):"
  IO.println s!"      DOUBLE ≈ 7 Fp2-muls  → ~{7 * 48} cycles"
  IO.println s!"      ADD    ≈ 16 Fp2-muls → ~{16 * 48} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.G2PointOpHWTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.G2PointOpHW

-- One representative output is synth-checked.  The former
-- super-linear synth-time wall is gone (fixed by the O(1) wire-name
-- collision check in Sparkle/IR/Builder.lean); a single G2 output now
-- translates in ~35 s.  We check ONE output rather than all nine to
-- keep the build time bounded — the wire-translation path is shared
-- across outputs, so one is a sufficient regression guard.
private def synth_g2PointOp_x0
    (start opDouble : Signal defaultDomain Bool)
    (x0 x1 y0 y1 z0 z1 bx0 bx1 by0 by1 bz0 bz1 fp2C0 fp2C1 : Signal defaultDomain (BitVec 384))
    (fp2Done : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 384) :=
  (g2PointOpHW start opDouble x0 x1 y0 y1 z0 z1 bx0 bx1 by0 by1 bz0 bz1 fp2C0 fp2C1 fp2Done).x0Out

#synthesizeVerilog synth_g2PointOp_x0

end SynthesisChecks
