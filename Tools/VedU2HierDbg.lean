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
  -- debugging only: `VED_HIER_STOP_AT=<tag prefix>` ABORTS the check (an error, so the run is refused) at that print,
  -- so that a run does not go on into a closer that does not terminate; it never closes a goal
  if let some stop ← IO.getEnv "VED_HIER_STOP_AT" then
    let tg := tag.map (·.getString) |>.getD ""
    if tg.startsWith stop then
      throwError "VED_HIER_STOP_AT: stopped at {tg} ({gs.length} goals open; debugging only)"

namespace Tools.VedU2HierDbg

/-- Peak and current resident memory of this process (kB; 0 if unavailable), from `/proc/self/status`. -/
def rssKb : IO (Nat × Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let get (k : String) : Nat := match (s.splitOn "\n").find? (·.startsWith k) with
      | some l => ((l.drop k.length).trimAscii.toString.takeWhile Char.isDigit).toNat!
      | none => 0
    return (get "VmHWM:", get "VmRSS:")
  catch _ => return (0, 0)

/-- Measurement only (`VED_HIER_PHASE_FILE=<file>`): append `<monotonic ms> <peak kB> <rss kB> <label>` to the file
and flush, AS IT HAPPENS (stderr of a killed run is buffered by a wrapper; this file is not).  Changes no goal. -/
def phaseLog (label : String) : IO Unit := do
  if let some f ← IO.getEnv "VED_HIER_PHASE_FILE" then
    let (hwm, rss) ← rssKb
    let h ← IO.FS.Handle.mk f .append
    h.putStr s!"{← IO.monoMsNow} {hwm} {rss} {label}\n"
    h.flush

end Tools.VedU2HierDbg

open Lean Elab Tactic in
/-- `ved_tick "label"`: measurement only (`VED_HIER_TICK`): prints the label and the monotonic ms to stderr (and, with
`VED_HIER_PHASE_FILE`, to that file, flushed); changes no goal. -/
elab "ved_tick " tag:str : tactic => do
  IO.eprintln s!"VED-TICK {tag.getString} t={← IO.monoMsNow}"
  Tools.VedU2HierDbg.phaseLog s!"tick {tag.getString}"
