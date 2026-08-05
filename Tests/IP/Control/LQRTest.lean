/-
  LQR state feedback — simulation + synthesis tests.

  The assertion that matters is `lyapunov_V_decreases`: it checks, cycle by
  cycle on the *actual fixed-point circuit's* trajectory, that the quadratic form
  `V(x) = xᵀPx` with the Riccati `P` from
  `proofs/SparkleProofs/Control/LQRDesign.lean` really does decrease.

  That is a concrete witness for the transported theorem: `LQRDesign.lean` proves
  the ℝ contraction and `Transport.lean` carries it to the quantized loop, but
  those live in the Mathlib sidecar.  This test verifies the *same* `P` works on
  the integers the hardware actually computes with — so if someone retunes the
  gain without redoing the certificate, this fails.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.LQRStateFeedback
import LSpec

set_option maxRecDepth 100000

namespace Sparkle.Tests.IP.Control.LQRTest

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.LQR
open LSpec

/-- Q15.16 → milliunits. -/
def milli (x : BitVec 32) : Int := x.toInt * 1000 / 65536

/-- `V` along the closed-loop trajectory, in milliunits. -/
def vTrace (n : Nat) : List Int :=
  (List.range n).map fun i =>
    milli (lyapunovV demoP11 demoP12 demoP22 (demoRun i))

/-- The `x₁` trajectory, in milliunits. -/
def x1Trace (n : Nat) : List Int :=
  (List.range n).map fun i => milli (demoRun i).x1

/-- The `x₂` trajectory, in milliunits. -/
def x2Trace (n : Nat) : List Int :=
  (List.range n).map fun i => milli (demoRun i).x2

/-- Is the list non-increasing? -/
def nonIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≥ b && nonIncreasing (b :: rest)

def suite : TestSeq :=
  group "LQR state feedback" <|
    -- The Lyapunov certificate transported to fixed point: V must not increase.
    test "V is non-increasing along the fixed-point trajectory"
      (nonIncreasing (vTrace 80)) $
    -- And it must actually make progress, not just sit still.
    test "V strictly decreases over the run"
      (((vTrace 80).head?.getD 0) > ((vTrace 80).getLast?.getD 0)) $
    -- The state converges toward the origin from x = (4.0, 0).
    test "x1 starts at 4.0"
      ((x1Trace 4).head?.getD 0 == 4000) $
    test "x1 decreases toward the origin"
      (((x1Trace 200).getLast?.getD 9999).natAbs < 500) $
    -- Boundedness is structural (the clamps), so it holds for the whole run.
    test "state stays inside the ±64.0 clamp"
      (((x1Trace 200 ++ x2Trace 200).map Int.natAbs).all (· ≤ 64000)) $
    -- The control effort respects the actuator limit by construction.
    test "control output respects the ±8.0 clamp"
      (((List.range 200).map fun i =>
         (milli (control demoGain demoULim (demoRun i))).natAbs).all (· ≤ 8000))

def main : IO UInt32 := do
  lspecIO (Std.HashMap.ofList [("all", [suite])]) []

/-- `IO Unit` wrapper for `Tests/AllTests.lean`.

    `AllTests` links every suite into one binary, and the repo convention there
    is an `IO Unit` main that aborts on failure (see
    `Tests/IP/Net/CRC32Test.lean`).  Returning the `lspecIO` code from inside
    `AllTests.main` instead leaves the per-suite `main` unreferenced by the
    aggregate's object file and the link fails on
    `lp_sparkle_..._main`. -/
def mainUnit : IO Unit := do
  let code ← main
  if code != 0 then IO.Process.exit 1

/-! ### Synthesis checks -/

section SynthesisChecks

set_option maxHeartbeats 80000000

/-- Closed loop (plant on-chip) as a synthesizable top. -/
def lqrLoopTop : Signal defaultDomain (BitVec 32) := demoLQR

/-- Controller only (plant off-chip), the shape a board would instantiate. -/
def lqrCtrlTop (x1 x2 : Signal defaultDomain (BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  lqrController demoULim x1 x2 (Signal.pure demoGain.k1) (Signal.pure demoGain.k2)

#synthesizeVerilog lqrLoopTop
#synthesizeVerilog lqrCtrlTop

end SynthesisChecks

end Sparkle.Tests.IP.Control.LQRTest
