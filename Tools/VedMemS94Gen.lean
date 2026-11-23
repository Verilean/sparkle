import Lean
import Tools.VedMemLoop

/-!
# The loop generalisation once, before the goal split (`ved.mem.s94GenOnce`)

Observed (sparkle-ved-mem-s94, thirteenth unit): `ved_loop_gen_mem s` (Tools/VedMemLoop.lean), run after stamp 100 on the 177 goals of R033,
generalises each of the 7 loops' states `(Signal.loop F).val s` goal by goal (revert, `rcases` of the state tuple) and splits every
`Bool` component by `cases`: 1 goal becomes 512, the scan for loops that no longer occur costs most of the time.  At the stamps 94/95
the goal is ONE goal in which the loops are shared (the case split is `refine ⟨_, _, _, ⟨rfl, rfl, rfl⟩, ?_⟩` and `And.intro`, later the peel).

`ved_loop_gen_once s` (on the one goal): every loop whose value `(loop).val s` occurs in the target or a hypothesis is generalised
(`generalizeDag`) and the state tuple is taken apart (`rcases`), as `ved_loop_gen_mem` does, but the `Bool` components are NOT split.
`ved_loop_gen_resid s` (where `ved_loop_gen_mem s` stood): one scan, shared over the goals by the types, of the targets and hypotheses of all goals for
`(loop).val s`; if none is left, nothing is done, otherwise the old `ved_loop_gen_mem s` runs (the fallback).
-/

namespace Tools.VedMemS94Gen

open Lean Meta Elab Tactic Tools.VedMemLoop Tools.VedU1WireShare Sparkle.Core.Signal

register_option ved.mem.s94GenOnce : Bool := {
  defValue := false
  descr := "ved memory loop: generalise the loop states once on the shared goal (stamp 95), without Bool case splits; the per-goal ved_loop_gen_mem is the fallback (default false)"
}

/-- test seams / counters (CloseCheck) -/
initialize genOnceHits : IO.Ref Nat ← IO.mkRef 0
initialize genOnceRefuse : IO.Ref Bool ← IO.mkRef false
initialize genOnceFailLate : IO.Ref Bool ← IO.mkRef false
/-- number of times the residual scan found nothing left (the old tactic skipped) / something left (the old tactic ran) -/
initialize genResidClean : IO.Ref Nat ← IO.mkRef 0
initialize genResidLeft : IO.Ref Nat ← IO.mkRef 0

/-- `ved_loop_gen_once s`: see the module comment.  Fails (the caller's `first` restores the state) unless there is exactly one goal and
at least one loop value is generalised. -/
elab "ved_loop_gen_once " s:ident : tactic => withMainContext do
  let gs ← getGoals
  unless gs.length == 1 do throwError "ved_loop_gen_once: {gs.length} goals"
  if (← genOnceRefuse.get) then throwError "ved_loop_gen_once: refused (test seam)"
  let sE ← elabTerm s.raw none
  let loops ← goalLoops (← getMainGoal)
  let mut done := 0
  for j in [0:loops.size] do
    let g ← getMainGoal
    unless (← hasValAt g loops[j]! sE) do continue
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_loop_gen_once: malformed Signal.loop"
    let bare := !(← whnfR α).isAppOf ``Prod
    let n := (← Tools.VedU1Loop.stateComps α).length
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let xs := (List.range (if bare then 1 else n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    let v ← g.withContext <| mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    generalizeDag v (if bare then Name.mkSimple s!"ved_x{j}_0" else X.getId)
    unless bare do evalTactic (← `(tactic| rcases $X:ident with ⟨$pats,*⟩))
    done := done + 1
  if done == 0 then throwError "ved_loop_gen_once: no loop value to generalise"
  if (← genOnceFailLate.get) then throwError "ved_loop_gen_once: late failure (test seam)"
  genOnceHits.modify (· + 1)
  dbgLog s!"gen_once: {done} of {loops.size} loops generalised"

/-- `ved_loop_gen_resid s`: `ved_loop_gen_mem s` unless no goal has a loop value `(loop).val s` left (one scan, each distinct type once) -/
elab "ved_loop_gen_resid " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let isV := fun (e : Expr) => e.isAppOfArity ``Signal.val 4 && (e.getArg! 2).isAppOfArity ``Signal.loop 4 && e.getArg! 3 == sE
  let seen ← IO.mkRef (({} : Std.HashSet Expr))
  let scan (e : Expr) : MetaM Bool := do
    let e ← instantiateMVars e
    if (← seen.get).contains e then return false
    seen.modify (·.insert e)
    return !(collectDag isV e).isEmpty
  let mut left := false
  for g in ← getGoals do
    if left then break
    left ← g.withContext do
      if (← scan (← g.getType)) then return true
      for d in ← getLCtx do
        unless d.isImplementationDetail do
          if (← scan d.type) then return true
      return false
  if left then
    genResidLeft.modify (· + 1)
    dbgLog "gen_resid: loop values left, ved_loop_gen_mem"
    evalTactic (← `(tactic| ved_loop_gen_mem $s))
  else
    genResidClean.modify (· + 1)
    dbgLog "gen_resid: no loop value left"

end Tools.VedMemS94Gen
