import Lean.Elab.Command
import Tools.ShippingNoPortsMemKidCommand

/-! # `#machine_no_ports_memkid_sweep f`: the memory-machine-kid generator on one declaration, MEASURED and never an error (round par/e-1)

WRITTEN, NOT BUILT. In the style of the built leaf sweeps
(`Tools/ShippingLeafSweepCommand.lean`, `Tools/ShippingLeafSweepExpect.lean`).

`#machine_no_ports_memkid f` (`Tools/ShippingNoPortsMemKidCommand.lean`) is
an ERROR where the declaration is refused or a generated proof fails.
`#machine_no_ports_memkid_sweep f` runs the SAME functions (`scopeShape`,
`scopeArtifacts`, `generate`) and only LOGS:

    MEMKIDSWEEP START f                 -- first, also on stderr (it survives a hang or a kill)
    NOPORTS MEMKID f at depth 1: …      -- the generator's own line, when an endpoint was made
    MEMKIDSWEEP RESULT f: <class>; …; <ms> ms

The classes:

| class | meaning |
|---|---|
| `GENERATED` | `f.machine_design_noPortsNR1_closed` was added now; the statement check passed |
| `REBUILT` | it existed; the rebuilt statement is `isDefEq` (proof kept as `…_regen`); the statement check passed |
| `REFUSED` | the scope refuses the declaration (`scopeShape` / `scopeArtifacts`): the reason line |
| `FAILED` | the scope accepts it and a generated proof, the compare path or the statement check failed |
| `UNRESOLVED` | the identifier is not a constant of the imports |

On REFUSED / FAILED the environment and the message log are put back. The
command is an error in NO case.

`#machine_no_ports_memkid_summary` (once, at the end of a file) prints one
line per swept declaration and the counts by class, and is an ERROR only on
a mechanical inconsistency of what was just measured: a GENERATED / REBUILT
row whose statement check did not pass or whose closed endpoint is not in
the environment; a REFUSED / FAILED / UNRESOLVED row that left a closed
endpoint behind that was not there before; nothing swept. It asserts no
class and no count.

`#machine_no_ports_memkid_expect f "CLASS" ["reason"]` asserts the class of
the row `f` (the LAST sweep of `f` in this file): an ERROR when `f` was not
swept, when the class differs, for GENERATED / REBUILT when the statement
check did not pass or the closed endpoint is absent, and — with a reason —
when the row's note does not contain the written text.

WHAT A `GENERATED` LINE MEANS (binding for any report): for that ONE
declaration as an entry at depth 1, `f.machine_design_noPortsNR1_closed`
was added and kernel-checked — `DesignSV` over the child map of the run's
returned design (the module LIST, not the SV string, not `#sim`); data
conditions decided for that declaration and its callees (conditions, not
reductions); the run, the reflections of `f` and of its callees and the
runtime boundary `ChildBnd` stay premises. -/
namespace Tools.ShippingNoPortsMemKidSweep
open Lean Meta Elab Command
open Tools.ShippingNoPortsMemKidCommand

/-- One swept declaration. -/
structure Row where
  decl : String
  /-- `GENERATED`, `REBUILT`, `REFUSED`, `FAILED` or `UNRESOLVED` -/
  tag : String
  /-- the generator's line, or the refusal / failure reason -/
  note : String
  /-- the statement check passed (`false` when no endpoint was made) -/
  checkOk : Bool
  props : Nat
  antes : Nat
  bad : Nat
  /-- the closed endpoint was in the environment BEFORE the sweep -/
  before : Bool
  /-- the closed endpoint is in the environment afterwards -/
  left : Bool
  ms : Nat

/-- The rows of the file being elaborated (one process per file). -/
initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- The closed endpoint's name. -/
def closedOf (f : Name) : Name :=
  Tools.ShippingMachineClosesGen.closedName (f ++ `machine_design_noPortsNR1)

/-- `#machine_no_ports_memkid_sweep f`: see the file header. Never an error. -/
elab "#machine_no_ports_memkid_sweep " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"MEMKIDSWEEP START {shown}"
  logInfo m!"MEMKIDSWEEP START {shown}"
  let t0 ← IO.monoMsNow
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"MEMKIDSWEEP RESULT {shown}: UNRESOLVED — the identifier is not a constant of the imports (a wrong name in the sweep file, not a fact about a declaration)"
    rows.modify fun a => a.push
      { decl := shown, tag := "UNRESOLVED", note := "the identifier does not resolve",
        checkOk := false, props := 0, antes := 0, bad := 0, before := false, left := false,
        ms := 0 }
  | some f =>
    let closedN := closedOf f
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    let before : Bool := savedEnv.contains closedN
    -- the scope: a refusal is REFUSED
    let sc : Except String ScopeM ← try
        let s ← scopeShape f
        scopeArtifacts f s
        pure (Except.ok s)
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure (Except.error msg)
    match sc with
    | Except.error msg =>
      setEnv savedEnv
      modify fun st => { st with messages := savedMsgs }
      let left : Bool := (← getEnv).contains closedN
      let ms := (← IO.monoMsNow) - t0
      logInfo m!"MEMKIDSWEEP RESULT {f}: REFUSED — {clip msg 900}; {closedN} in the environment: {left}; {ms} ms"
      rows.modify fun a => a.push
        { decl := toString f, tag := "REFUSED", note := msg, checkOk := false, props := 0,
          antes := 0, bad := 0, before := before, left := left, ms := ms }
    | Except.ok s =>
      -- the generation: a failure is FAILED
      let res : Except String Made ← try
          let m ← generate f s
          pure (Except.ok m)
        catch ex =>
          let msg ← ex.toMessageData.toString
          pure (Except.error msg)
      match res with
      | Except.error msg =>
        setEnv savedEnv
        modify fun st => { st with messages := savedMsgs }
        let left : Bool := (← getEnv).contains closedN
        let ms := (← IO.monoMsNow) - t0
        logInfo m!"MEMKIDSWEEP RESULT {f}: FAILED (the scope accepts it; the environment put back) — {clip msg 1500}; callees {kindLines s}; {closedN} in the environment: {left}; {ms} ms"
        rows.modify fun a => a.push
          { decl := toString f, tag := "FAILED", note := msg, checkOk := false, props := 0,
            antes := 0, bad := 0, before := before, left := left, ms := ms }
      | Except.ok m =>
        let line := summaryLine f s m
        logInfo m!"{line}"
        let left : Bool := (← getEnv).contains closedN
        let ms := (← IO.monoMsNow) - t0
        let tag : String := if m.rebuilt then "REBUILT" else "GENERATED"
        logInfo m!"MEMKIDSWEEP RESULT {f}: {tag}; statement check passed: {m.check.ok} (proposition binders {m.check.props}, antecedents under the existentials {m.check.antes}, NOT ALLOWED {m.check.bad}); {closedN} in the environment: {left}; {ms} ms. SCOPE of this line: ONE declaration as an entry, depth 1; data conditions decided for it and its callees (conditions, not reductions); the run, the reflections and ChildBnd stay premises; DesignSV of the module list over the returned design's child map — not the SV string, not #sim"
        rows.modify fun a => a.push
          { decl := toString f, tag := tag, note := line, checkOk := m.check.ok,
            props := m.check.props, antes := m.check.antes, bad := m.check.bad,
            before := before, left := left, ms := ms }

/-- `#machine_no_ports_memkid_summary`: see the file header. An error only on
an inconsistency of what this file measured. -/
elab "#machine_no_ports_memkid_summary" : command => do
  let rs ← rows.get
  let mut lines : Array String := #[]
  let mut problems : Array String := #[]
  for r in rs do
    let made : Bool := r.tag == "GENERATED" || r.tag == "REBUILT"
    if made then
      lines := lines.push s!"MEMKIDSWEEP ROW {r.decl}: {r.tag}; proposition binders {r.props}, antecedents {r.antes}, NOT ALLOWED {r.bad}; {r.ms} ms"
      unless r.checkOk do
        problems := problems.push s!"{r.decl}: {r.tag} but its statement check did not pass"
      unless r.bad == 0 do
        problems := problems.push s!"{r.decl}: {r.tag} with {r.bad} NOT ALLOWED premises"
      unless r.left do
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_noPortsNR1_closed is not in the environment"
    else
      lines := lines.push s!"MEMKIDSWEEP ROW {r.decl}: {r.tag} — {clip r.note 300}; {r.ms} ms"
      if r.left && !r.before then
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_noPortsNR1_closed is in the environment and was not before the sweep"
  let count (t : String) : Nat := (rs.filter fun r => r.tag == t).size
  let namesOf (t : String) : List String := (rs.filter fun r => r.tag == t).toList.map (·.decl)
  logInfo m!"{String.intercalate "\n" lines.toList}"
  logInfo m!"MEMKIDSWEEP SUMMARY of {rs.size}: GENERATED {count "GENERATED"} {namesOf "GENERATED"}; REBUILT {count "REBUILT"} {namesOf "REBUILT"}; REFUSED {count "REFUSED"} {namesOf "REFUSED"}; FAILED {count "FAILED"} {namesOf "FAILED"}; UNRESOLVED {count "UNRESOLVED"} {namesOf "UNRESOLVED"}. Each GENERATED / REBUILT row: its statement check passed with 0 NOT ALLOWED (asserted below). No class and no count was expected by this command. A GENERATED row is about ONE declaration as an entry at depth 1 — DesignSV of the module list, with the run, the reflections and ChildBnd as premises; it is not a statement about the SV string, #sim, or any other declaration."
  if rs.isEmpty then
    throwError "MEMKIDSWEEP: nothing was swept in this file"
  unless problems.isEmpty do
    throwError "MEMKIDSWEEP: {problems.size} inconsistencies in what was measured:\n{String.intercalate "\n" problems.toList}"

/-- `#machine_no_ports_memkid_expect f "CLASS" ["reason"]`: see the file
header. Adds nothing to the environment; each is its own command. -/
elab "#machine_no_ports_memkid_expect " d:ident e:str r:(str)? : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let want : String := e.getString
  let rs ← rows.get
  let mine := (rs.filter fun x => x.decl == toString f).toList.reverse
  let row ← match mine with
    | x :: _ => pure x
    | [] => throwError "MEMKIDSWEEP EXPECT {f}: not swept in this file (no #machine_no_ports_memkid_sweep {f} before this line)"
  unless row.tag == want do
    throwError "MEMKIDSWEEP EXPECT {f}: expected {want}, now {row.tag} — {row.note}"
  if want == "GENERATED" || want == "REBUILT" then
    unless row.checkOk do
      throwError "MEMKIDSWEEP EXPECT {f}: {row.tag}, but its statement check did not pass"
    unless row.bad == 0 do
      throwError "MEMKIDSWEEP EXPECT {f}: {row.tag}, with {row.bad} NOT ALLOWED premises"
    unless (← getEnv).contains (closedOf f) do
      throwError "MEMKIDSWEEP EXPECT {f}: {row.tag}, but {closedOf f} is not in the environment"
  match r with
  | some s =>
    let sub : String := s.getString
    unless (row.note.splitOn sub).length > 1 do
      throwError "MEMKIDSWEEP EXPECT {f}: {row.tag}, but its reason does not contain \"{sub}\": {row.note}"
  | none => pure ()
  logInfo m!"MEMKIDSWEEP EXPECT {f}: {row.tag}, as expected"

end Tools.ShippingNoPortsMemKidSweep
