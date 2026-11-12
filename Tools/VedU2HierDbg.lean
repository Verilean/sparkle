import Lean

/-!
# `ved_eprint_state`

The debug trace of the hierarchical checker's generated proof (`VED_HIER_TRACE`).  `trace_state` is a message,
which is dropped when the checker refuses (the command's messages are discarded with the exception); this
prints the goals to stderr instead, so a failing closer's goal can be read.
-/

open Lean Elab Tactic in
elab "ved_eprint_state" : tactic => do
  let gs ← getGoals
  IO.eprintln s!"VED-GOALS {gs.length}"
  for g in gs do
    IO.eprintln s!"{← Lean.Meta.ppGoal g}"
    IO.eprintln "VED-GOAL-END"
