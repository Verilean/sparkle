/-
  Example: RC transient vs closed form

  Backward-Euler transient simulation of an RC step response, printed alongside
  the analytic solution `5(1 − e^{−t/τ})`.
-/

import Sparkle.Analog

open Sparkle.Analog

namespace Examples.Analog.RCTransient

/-- RC low-pass driven by a 5 V step. `R = 1 kΩ`, `C = 1 µF` ⇒ `τ = RC = 1 ms`.
Net 2 is the capacitor voltage. -/
def rc : Circuit := circuit fun n1 n2 =>
  [ vsourceDC 5.0 |>.between n1 ground
  , resistor 1e3  |>.between n1 n2
  , capacitor 1e-6 |>.between n2 ground ]

/-- Closed-form capacitor voltage for the 5 V step (τ = 1 ms). -/
def analytic (t : Float) : Float := 5.0 * (1.0 - Float.exp (-t / 1e-3))

def demo : IO Unit := do
  -- dt = τ/100, run to 5τ.
  let samples := (rc.transient 1e-5 500).sampleNet rc 2
  IO.println "RC step response vs closed form 5(1 - e^{-t/τ}):"
  IO.println "    t (ms)    V_sim       V_exact"
  for k in [0, 50, 100, 200, 500] do
    let (t, v) := samples[k]!
    IO.println s!"   {t * 1e3}      {v}      {analytic t}"
  IO.println ""

end Examples.Analog.RCTransient
