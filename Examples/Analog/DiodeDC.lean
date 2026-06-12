/-
  Example: nonlinear DC operating point

  A diode is just `i = Is·(exp(v/Vt) − 1)`. Newton's method solves the resulting
  nonlinear system; nothing else about the API changes versus a linear circuit.
-/

import Sparkle.Analog

open Sparkle.Analog

namespace Examples.Analog.DiodeDC

/-- 1 V source — 1 kΩ — diode — ground. The diode drops ≈0.6 V; the rest of the
1 V appears across the resistor, and the same current flows through both. -/
def diodeClamp : Circuit := circuit fun n1 n2 =>
  [ vsourceDC 1.0 |>.between n1 ground
  , resistor 1e3  |>.between n1 n2
  , diode 1e-14 0.025 |>.between n2 ground ]

def demo : IO Unit := do
  IO.println "Nonlinear DC operating point (1V — 1kΩ — diode — gnd):"
  match diodeClamp.solveDC with
  | some x => IO.println s!"  V(diode) = {x[1]!} V,  I = {x[4]!} A\n"
  | none => IO.println "  (failed to converge)\n"

end Examples.Analog.DiodeDC
