import Lean
import Tools.VedMemLoop

/-!
# The stage-94 simp without the `ite_congr` congruence theorem (`ved.mem.s94NoIteCongr`)

Observed (sparkle-ved-mem-s94, sixth unit): in the stage-94 simp of the new branch, the user congruence theorem `ite_congr` (`@[congr]`, used by
`Lean.Meta.Simp.trySimpCongrTheorem?` for every `ite` node) accounts for the allocating work between the `post` of one term and the `pre` of the
next: on the s150r conjunct #0 the same simp without it took 5.2 s / 72.8 M allocations instead of 9.1-9.3 s / 121 M, with the same number of steps,
the same used theorems and the same resulting expression (hash).  Simp falls back to its automatic congruence for `ite`.

`ved_s94_noitecongr (tacs)` runs `tacs` with the `ite` entry of the congruence-theorem extension of the environment without `ite_congr` and puts the
entry back afterwards (also when `tacs` fails; a failure is rethrown and the caller's `first | .. | ..` runs the old path).  It refuses (throws)
when the option is off or when `ite_congr` is not registered for `ite`.  Sound: the congruence theorem only changes how simp builds the proof of
its result; the proof is still checked by the kernel against the same statement.
-/

namespace Tools.VedMemS94Fix

open Lean Meta Elab Tactic

register_option ved.mem.s94NoIteCongr : Bool := {
  defValue := false
  descr := "the stage-94 simp of the new branch (`ved.mem.hstepNorm`) runs without the congruence theorem `ite_congr`; the old simp is the fallback"
}

/-- number of runs of the wrapper that completed (test counter) -/
initialize noIteCongrHits : IO.Ref Nat ← IO.mkRef 0

/-- test seam (never set by production code): the wrapper refuses, the old simp is the fallback -/
initialize noIteCongrRefuse : IO.Ref Bool ← IO.mkRef false

/-- test seam: the wrapper fails after its inner tactics have run (the congruence entry is put back) -/
initialize noIteCongrFailLate : IO.Ref Bool ← IO.mkRef false

def setIteCongr (l : List SimpCongrTheorem) : CoreM Unit :=
  modifyEnv fun env => congrExtension.modifyState env fun s => { s with lemmas := s.lemmas.insert ``ite l }

def noIteCongrCore (t : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Unit := do
  unless (← getOptions).getBool `ved.mem.s94NoIteCongr false do throwError "ved_s94_noitecongr: option ved.mem.s94NoIteCongr is off"
  if (← noIteCongrRefuse.get) then throwError "ved_s94_noitecongr: refused (test seam)"
  let some orig := (congrExtension.getState (← getEnv)).lemmas.find? ``ite | throwError "ved_s94_noitecongr: no congruence theorem for ite"
  let kept := orig.filter (·.theoremName != ``ite_congr)
  if kept.length == orig.length then throwError "ved_s94_noitecongr: ite_congr is not registered"
  let t0 ← IO.monoMsNow
  setIteCongr kept
  try evalTactic t finally setIteCongr orig
  if (← noIteCongrFailLate.get) then throwError "ved_s94_noitecongr: failed late (test seam)"
  noIteCongrHits.modify (· + 1)
  Tools.VedMemLoop.dbgLog s!"s94_noitecongr: inner ms={(← IO.monoMsNow) - t0}"

elab "ved_s94_noitecongr " "(" t:tacticSeq ")" : tactic => noIteCongrCore t

end Tools.VedMemS94Fix
