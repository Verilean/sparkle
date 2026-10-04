/-
  PID with anti-windup — simulation + synthesis tests.

  Two things are checked that the Lyapunov argument does *not* cover, because
  they hold unconditionally by construction rather than by stability:

  * the integrator never leaves `[-iLim, iLim]` — that is anti-windup, and it is
    what makes the circuit overflow-free for *any* gains and *any* input;
  * the output never leaves `[-uLim, uLim]` — the actuator limit.

  Then the closed loop against the first-order plant is checked to actually
  converge to the setpoint, which is the part that does depend on the tuning.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.PID
import LSpec

set_option maxRecDepth 100000

namespace Sparkle.Tests.IP.Control.PIDTest

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.PID
open LSpec

/-- Q15.16 → milliunits. -/
def milli (x : BitVec 32) : Int := x.toInt * 1000 / 65536

/-- Setpoint 1.0. -/
def setpoint : BitVec 32 := q 1 1

/-- Closed-loop measurement trajectory, in milliunits. -/
def yTrace (n : Nat) : List Int :=
  (List.range n).map fun i => milli (closedLoop setpoint i).2

/-- Integrator trajectory, in milliunits. -/
def integTrace (n : Nat) : List Int :=
  (List.range n).map fun i => milli (closedLoop setpoint i).1.integ

/-- A deliberately hostile open-loop run: a large constant error, which is what
    drives an unprotected integrator to wind up without bound. -/
def windupInteg (n : Nat) : List Int :=
  let rec go : Nat → State → List Int
    | 0, _ => []
    | k + 1, st =>
      let (st', _) := step demoGains demoILim demoULim st (q 1000 1) (0#32)
      milli st'.integ :: go k st'
  go n ⟨0#32, 0#32⟩

def suite : TestSeq :=
  group "PID with anti-windup" <|
    -- Structural bounds: hold for any input, no stability assumption.
    test "integrator stays within ±16.0 under a huge sustained error"
      (((windupInteg 500).map Int.natAbs).all (· ≤ 16000)) $
    test "integrator actually saturates (the clamp is exercised)"
      (((windupInteg 500).map Int.natAbs).any (· ≥ 15000)) $
    test "closed-loop integrator stays within ±16.0"
      (((integTrace 300).map Int.natAbs).all (· ≤ 16000)) $
    test "control output stays within ±8.0"
      (((List.range 300).map fun i =>
         let st := (closedLoop setpoint i).1
         let y := (closedLoop setpoint i).2
         (milli (step demoGains demoILim demoULim st setpoint y).2).natAbs).all
        (· ≤ 8000)) $
    -- Tuning-dependent: the loop tracks the setpoint.
    test "closed loop starts at zero"
      ((yTrace 3).head?.getD 999 == 0) $
    test "closed loop converges to the 1.0 setpoint"
      (((yTrace 300).getLast?.getD 0 - 1000).natAbs < 50)

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

/-- The PID alone (setpoint and measurement as inputs). -/
def pidTop (r y : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  demoPID r y

/-- PID + plant, closed on-chip. -/
def pidLoopTop (r : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  closedLoopCircuit r

#synthesizeVerilog pidTop
#synthesizeVerilog pidLoopTop

end SynthesisChecks

end Sparkle.Tests.IP.Control.PIDTest
