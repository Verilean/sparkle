/-
  Examples: analog (continuous-time) circuits

  Aggregates the `Examples/Analog/` subgroup and runs every demo. Each example
  file is self-contained and can be read on its own:
  - Analog/DiodeDC.lean      — nonlinear DC operating point (Newton)
  - Analog/RCTransient.lean  — transient simulation vs closed form
  - Analog/Ladder.lean       — a parametric N-stage ladder (metaprogramming)

  Run with:  lake exe analog-example
-/

import Examples.Analog.DiodeDC
import Examples.Analog.RCTransient
import Examples.Analog.Ladder

def main : IO Unit := do
  Examples.Analog.DiodeDC.demo
  Examples.Analog.RCTransient.demo
  Examples.Analog.Ladder.demo
