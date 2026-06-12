import LSpec
import Sparkle.Analog

/-!
# Analog transient tests

Phase-1 exit criterion: the continuous-time solver reproduces the closed-form
behaviour of linear RC and RLC circuits.
-/

open LSpec Sparkle.Analog

namespace Tests.Analog

/-- Absolute-tolerance float comparison. -/
private def approx (a b tol : Float) : Bool := Float.abs (a - b) < tol

/-- RC low-pass driven by a 5 V step. `R = 1 kΩ`, `C = 1 µF`, so `τ = RC = 1 ms`.
Node `2` is the capacitor voltage. -/
private def rc : Circuit := circuit fun n1 n2 =>
  [ vsourceDC 5.0 |>.between n1 ground
  , resistor 1e3 |>.between n1 n2
  , capacitor 1e-6 |>.between n2 ground ]

/-- Series R-L-C driven by a 5 V step (`R = 100 Ω`, `L = 1 mH`, `C = 1 µF`;
overdamped). Node `3` is the capacitor voltage, which settles to 5 V. -/
private def rlc : Circuit := circuit fun n1 n2 n3 =>
  [ vsourceDC 5.0 |>.between n1 ground
  , resistor 100 |>.between n1 n2
  , inductor 1e-3 |>.between n2 n3
  , capacitor 1e-6 |>.between n3 ground ]

/-- The same RC network via the monadic builder; should equal `rc` as a value. -/
private def rcMonadic : Circuit := runCircuit do
  let n1 ← net
  let n2 ← net
  place (vsourceDC 5.0) n1 ground
  place (resistor 1e3) n1 n2
  place (capacitor 1e-6) n2 ground

private def topology (c : Circuit) : List (Nat × Nat) :=
  c.placements.map (fun p => (p.pos, p.neg))

/-- DC value of the analytic RC response at `t = τ` and `t = 5τ`. -/
private def vτ : Float := 5.0 * (1.0 - Float.exp (-1.0))
private def v5τ : Float := 5.0 * (1.0 - Float.exp (-5.0))

def tests : TestSeq :=
  -- Library invariant: the value-based and monadic builders agree.
  test "value-based and monadic builders produce the same circuit"
      (topology rc == topology rcMonadic && rc.netCount == rcMonadic.netCount) <|
  -- dt = τ/100; Backward Euler is within ~1% here.
  test "RC voltage at t=τ matches 5(1-1/e)"
      (approx ((rc.transient 1e-5 100).finalNet rc 2) vτ 0.05) <|
  test "RC voltage at t=5τ matches 5(1-e^-5)"
      (approx ((rc.transient 1e-5 500).finalNet rc 2) v5τ 0.05) <|
  test "RC starts uncharged (≈0 V at t=0)"
      (approx (((rc.transient 1e-5 100).sampleNet rc 2)[0]!.2) 0.0 1e-9) <|
  test "RLC capacitor settles to source voltage (5 V)"
      (approx ((rlc.transient 1e-6 3000).finalNet rlc 3) 5.0 0.05) <|
  test "RLC DC operating point is consistent (final current ≈ 0)"
      (approx (((rlc.transient 1e-6 3000).back?.map (·.2[5]!)).getD 0.0) 0.0 1e-3)

end Tests.Analog

def main : IO UInt32 :=
  lspecIO (Std.HashMap.ofList [("analog", [Tests.Analog.tests])]) []
