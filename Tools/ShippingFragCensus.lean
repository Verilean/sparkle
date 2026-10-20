import Lean.Elab.Command
import Tools.ShippingWalkStillMore
import Tools.ShippingMachineAuto

/-! # `#frag_census`: which reflected terms were inside the walk's first fragment — a MEASUREMENT

WRITTEN, NOT BUILT (par/a-41). It reads the environment of the file it is run
in and LOGS. It adds nothing, asserts nothing, expects nothing.

`Tools.ShippingWalkStill.walk_still` covered the ten constructors of `wfrag`;
`Tools.ShippingWalkStillMore.walk_still_all` covers every constructor
(`wfragAll` is the constant `true`). So the question "how much of the built
universe can the cache-coherence unit now reach" has two parts:

* for which declarations was `wfrag` FALSE — those are the ones the wider
  walk adds (every declaration with a reflected term is inside `wfragAll`);
* which declarations have a reflected term at all: a constant
  `f.gateTerm` (a gate child, `#gate_child`; measured by that term even when
  it carries `f.machineData` too) or `f.machineData` (the machine route,
  `#machine_endpoint`). A declaration with neither is outside the unit
  whatever the fragment.

## How a Boolean is obtained

NEVER by compiled evaluation of reflected data. For a term `t : Bool` the
command elaborates, in a saved-and-restored command state,

    example : t = true  := by first | decide | decide +kernel
    example : t = false := by first | decide | decide +kernel

and reports `T`, `F`, or `?` (neither went through: the kernel could not
reduce the term within the default heartbeats — not a verdict).

## The rows

    FRAGCENSUS START <f>
    FRAGCENSUS ROW <f>: <machine|gate>; wfrag=<T/F/?>; wfragAll=T (every term); calls=<none|some|?|->

`calls`: for a machine, whether its shape has call entries
(`shape.insts.isEmpty`); `-` for a gate child. `START` goes to standard
error, flushed, before each declaration.

* `#frag_row f` — one declaration;
* `#frag_census n` — every declaration of the environment with a reflected
  term that has no row yet, in name order, at most `n` of them and within a
  wall-clock budget (`budgetMs`); the ones left out are counted;
* `#frag_census_summary` — the counts and the declarations with
  `wfrag=F`.

What a row does NOT say: that `EntryOk` holds for the declaration. It says
only that the WALK's term condition is met (always, now) or was met before
(`wfrag`); `EntryOk` also needs the declaration's data facts and, for a
parent, its closing (`Tools/ShippingEntryOkCommand.lean`). -/
namespace Tools.ShippingFragCensus
open Lean Meta Elab Command

/-- Elaborate `example : t = <b> := by first | decide | decide +kernel` in a
scratch copy of the command state; `true` when it went through. -/
def decidesTo (t : Lean.Term) (b : Bool) : CommandElabM Bool := do
  let saved ← get
  modify fun s => { s with messages := {} }
  let stx ←
    if b then `(command| example : $t = true := by first | decide | decide +kernel)
    else `(command| example : $t = false := by first | decide | decide +kernel)
  let ok : Bool ←
    try
      elabCommand stx
      pure (!(← get).messages.hasErrors)
    catch _ => pure false
  set saved
  pure ok

/-- `T`, `F` or `?`. -/
def verdict (t : Lean.Term) : CommandElabM String := do
  if ← decidesTo t true then pure "T"
  else if ← decidesTo t false then pure "F"
  else pure "?"

/-- One measured declaration. -/
structure Row where
  decl : Name
  machine : Bool
  wfrag : String
  calls : String

initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]

/-- Wall-clock budget of one `#frag_census`, in milliseconds. -/
def budgetMs : Nat := 900000

/-- Measure one declaration (`machine`: by `f.machineData`, else by
`f.gateTerm`). -/
def measure (f : Name) (machine : Bool) : CommandElabM Unit := do
  IO.eprintln s!"FRAGCENSUS START {f}"
  (← IO.getStderr).flush
  let md : Ident := mkIdent (`_root_ ++ f ++ `machineData)
  let gt : Ident := mkIdent (`_root_ ++ f ++ `gateTerm)
  let w ←
    if machine then verdict (← `(Tools.ShippingWalkStill.wfrag ($md).packed))
    else verdict (← `(Tools.ShippingWalkStill.wfrag $gt))
  let calls ←
    if machine then do
      let v ← verdict (← `(List.isEmpty ($md).shape.insts))
      pure (if v == "T" then "none" else if v == "F" then "some" else "?")
    else pure "-"
  let kind : String := if machine then "machine" else "gate"
  logInfo m!"FRAGCENSUS ROW {f}: {kind}; wfrag={w}; wfragAll=T (every term); calls={calls}"
  rows.modify fun a => a.push { decl := f, machine := machine, wfrag := w, calls := calls }

/-- `#frag_row f`: one declaration. Logs when `f` has no reflected term. -/
elab "#frag_row " d:ident : command => do
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none => logInfo m!"FRAGCENSUS ROW {d.getId}: UNRESOLVED — not a constant of the imports"
  | some f =>
    let env ← getEnv
    -- a gate child may carry `machineData` too (its source definitions): the
    -- term its ENTRY walks is the gate term
    if env.contains (f ++ `gateTerm) then measure f false
    else if env.contains (f ++ `machineData) then measure f true
    else logInfo m!"FRAGCENSUS ROW {f}: NO REFLECTED TERM (neither {f}.machineData nor {f}.gateTerm)"

/-- `#frag_census n`: the declarations with a reflected term and no row yet,
in name order, at most `n`, within the time budget. -/
elab "#frag_census " n:num : command => do
  let cap := n.getNat
  let env ← getEnv
  let done := (← rows.get).map (·.decl)
  let found : Array (Name × Bool) := env.constants.fold (fun acc nm _ =>
    match nm with
    | .str p s =>
      if s == "gateTerm" then acc.push (p, false)
      else if s == "machineData" && !env.contains (p ++ `gateTerm) then acc.push (p, true)
      else acc
    | _ => acc) #[]
  let sorted := found.qsort (fun a b => decide (a.1.toString < b.1.toString))
  let todo := sorted.filter fun p => !done.contains p.1
  let t0 ← IO.monoMsNow
  let mut ran : Nat := 0
  let mut left : Nat := 0
  for (f, machine) in todo do
    let now ← IO.monoMsNow
    if ran ≥ cap || now - t0 > budgetMs then
      left := left + 1
    else
      measure f machine
      ran := ran + 1
  logInfo m!"FRAGCENSUS SCAN: {found.size} declarations with a reflected term in this environment ({(found.filter (·.2)).size} by machineData, {(found.filter (!·.2)).size} by gateTerm); {done.size} had a row already; measured now {ran}; left out {left} (cap {cap}, budget {budgetMs} ms)"

/-- `#frag_census_summary`: the counts of the rows of this file. -/
elab "#frag_census_summary" : command => do
  let rs ← rows.get
  let c (p : Row → Bool) : Nat := (rs.filter p).size
  let outside := (rs.filter fun r => r.wfrag == "F").toList.map fun r => toString r.decl
  let unknown := (rs.filter fun r => r.wfrag == "?").toList.map fun r => toString r.decl
  logInfo m!"FRAGCENSUS SUMMARY of {rs.size} rows: machine {c (·.machine)} (no call {c fun r => r.machine && r.calls == "none"}, with calls {c fun r => r.machine && r.calls == "some"}), gate {c (!·.machine)}; wfrag=T {c fun r => r.wfrag == "T"}, wfrag=F {c fun r => r.wfrag == "F"}, undecided {c fun r => r.wfrag == "?"}; wfragAll=T for all (every term). Outside the first fragment, reached by walk_still_all only: {outside}. Undecided: {unknown}. A MEASUREMENT of the walk's term condition; not a statement that EntryOk holds for any row."

end Tools.ShippingFragCensus
