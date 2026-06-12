/-
  Examples: analog (continuous-time) circuits

  Aggregates the `Examples/Analog/` subgroup and runs every demo. Each example
  file is self-contained and can be read on its own:
  - Analog/DiodeDC.lean      — nonlinear DC operating point (Newton)
  - Analog/RCTransient.lean  — transient simulation vs closed form

  Run with:  lake exe analog-example
-/

import Examples.Analog.DiodeDC
import Examples.Analog.RCTransient

def main : IO Unit := do
  Examples.Analog.DiodeDC.demo
  Examples.Analog.RCTransient.demo
