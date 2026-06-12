import Sparkle.Analog.IR.Expr
import Sparkle.Analog.Num
import Sparkle.Analog.IR.Netlist
import Sparkle.Analog.DSL.Build

/-!
# Sparkle.Analog — continuous-time analog modelling

A standalone, simulation-first analog HDL embedded in Lean 4. Device models are
written as acausal equations (in the Functional Hybrid Modelling / Modelica
lineage) over a real-valued expression IR, and solved by Modified Nodal Analysis.

Deliberately import-isolated from the digital `Sparkle.IR` / `Sparkle.Core`
subsystem; the two share frontend patterns, not semantics.
-/
