import Lean

/-!
# `ved_eprint_state`

The debug trace of the hierarchical checker's generated proof (`VED_HIER_TRACE`).  `trace_state` is a message,
which is dropped when the checker refuses (the command's messages are discarded with the exception); this
prints the goals to stderr instead, so a failing closer's goal can be read.  With `VED_HIER_TRACE_FILE` set the same
text is appended to that file as it happens (a wrapper that buffers stderr until the process ends loses it when the
process is killed).
-/

open Lean Elab Tactic in
elab "ved_eprint_state" tag:(str)? : tactic => do
  let gs ← getGoals
  let t ← IO.monoMsNow
  let sink : String → IO Unit ← do
    match ← IO.getEnv "VED_HIER_TRACE_FILE" with
    | some f => pure fun s => do
        let h ← IO.FS.Handle.mk f .append
        h.putStr (s ++ "\n")
        h.flush
    | none => pure fun s => IO.eprintln s
  sink s!"VED-GOALS {gs.length} {tag.map (·.getString) |>.getD ""} t={t}"
  let full := (← IO.getEnv "VED_HIER_TRACE_BRIEF").isNone
  for g in gs do
    if full then sink s!"{← Lean.Meta.ppGoal g}" else sink s!"  goal size {(← instantiateMVars (← g.getType)).approxDepth}"
    sink "VED-GOAL-END"
  -- debugging only: `VED_HIER_STOP_AT=<tag prefix>` closes the goals with `sorry` at that print, so that a run does
  -- not go on into a closer that does not terminate
  if let some stop ← IO.getEnv "VED_HIER_STOP_AT" then
    if (tag.map (·.getString) |>.getD "").startsWith stop then
      for g in gs do g.admit
