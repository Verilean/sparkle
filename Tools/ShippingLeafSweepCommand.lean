import Lean.Elab.Command
import Tools.ShippingLeafDesignCommand
import Tools.ShippingFinalGoalCommand

/-! # `#leaf_sweep f`: `#machine_leaf_design` on one declaration, MEASURED and never an error (round par/b-31)

WRITTEN, NOT BUILT.

`#machine_leaf_design_try f "CLASS"` (BUILT) is an error when the outcome's
class is not the one written in the file — it needs a prediction. A sweep
over declarations nobody ran the generator on has none that is more than a
reading. `#leaf_sweep f` runs the SAME generator
(`Tools.ShippingLeafDesignCommand.leafDesign`, which never throws and puts
the environment back on REFUSED / FAILED) and only LOGS:

    LEAFSWEEP START f                       -- first, also on stderr (it survives a hang or a kill)
    LEAFDESIGN DATA …                       -- the reader's data (the generator's own line)
    LEAFDESIGN PREMISE … ALLOWED | NOT ALLOWED …   -- the generator's listing, when a theorem was made
    LEAFDESIGN GENERATED | REBUILT | REFUSED | FAILED f: <note / reason>
    LEAFDESIGN AUDIT …                      -- `Tools.ShippingLeafDesignCommand.audit`, when a theorem was made
    GOALGAP …                               -- the parents' gap tool on f.machine_design_leaf0, when made
    LEAFSWEEP RESULT f: <class>; …; <ms> ms

`#leaf_sweep` is an error in NO case: an identifier that does not resolve is
`UNRESOLVED`, an exception of any step is caught and logged.

`#leaf_sweep_summary` (once, at the end of a file) prints one line per
declaration swept in this file and the counts by class, and is an ERROR only
on a mechanical inconsistency of what was just measured:

* a declaration whose class is GENERATED / REBUILT but whose audit did not
  pass (the audit re-reads the added statement: exactly the run and
  `MachineDefines f` as proposition binders, one antecedent `ChildBnd`, 0 NOT
  ALLOWED by `Tools.ShippingFinalGoalCommand.allowed`, no check / guard /
  checker constant, conclusion `DesignSV` over `childMap`; standard axioms);
* a REFUSED / FAILED / UNRESOLVED declaration that left
  `f.machine_design_leaf0` behind;
* nothing was swept.

It asserts NO expected class and NO expected count: predictions belong in
`docs/parallel/B-leaf-sweep.md`.

The classifier is the existing one: `Tools.ShippingFinalGoalCommand.allowed`,
through the generator's `checkStatement` and its `audit` (the function
`Tests.Compiler.NoPortsTest.premiseLines` calls too). The gap tool is the
existing `Tools.ShippingFinalGoalCommand.gapOf` (what `#machine_goal_gap_of`
runs); its failure is logged, not an error.

WHAT A `GENERATED` LINE MEANS (binding for any report): for that ONE
declaration as an entry, depth 0, no call, `f.machine_design_leaf0` was added
and kernel-checked — `DesignSV` over the child map of the run's returned
design (the module LIST, not the SV string, not `#sim`); data conditions
decided for that declaration (conditions, not reductions); the run, the
reflection `MachineDefines f` and the runtime boundary `ChildBnd` stay
premises; a compiler with the two guards of `Sparkle/IR/RefineCheck.lean`.

Names: a sweep GENERATES `f.machine_design_leaf0`, `…_gap`, and — where they
are not in the imports — `f.machine_leafKid` and `f.machine_closes`. A sweep
file must not be imported together with another file that generates the same
names for the same declaration. -/
namespace Tools.ShippingLeafSweepCommand
open Lean Meta Elab Command

/-- One swept declaration. -/
structure Row where
  decl : String
  /-- `GENERATED`, `REBUILT`, `REFUSED`, `FAILED` or `UNRESOLVED` -/
  tag : String
  /-- `OK`, `FAILED: …`, or `-` when no theorem was made -/
  audit : String
  /-- the gap hypotheses of the gap theorem, or why there is none -/
  gap : String
  /-- NOT ALLOWED lines in the generator's premise listing (measured) -/
  bad : Nat
  /-- lines of the generator's premise listing, without the conclusion -/
  listed : Nat
  /-- `f.machine_design_leaf0` in the environment afterwards -/
  left : Bool
  ms : Nat
  note : String

/-- The rows of the file being elaborated (one process per file). -/
initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- `#leaf_sweep f`: see the file header. Never an error. -/
elab "#leaf_sweep " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"LEAFSWEEP START {shown}"
  logInfo m!"LEAFSWEEP START {shown}"
  let t0 ← IO.monoMsNow
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"LEAFSWEEP RESULT {shown}: UNRESOLVED — the identifier is not a constant of the imports (a wrong name in the sweep file, not a fact about a declaration)"
    rows.modify fun a => a.push
      { decl := shown, tag := "UNRESOLVED", audit := "-", gap := "-", bad := 0, listed := 0,
        left := false, ms := 0, note := "the identifier does not resolve" }
  | some f =>
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    let o : Tools.ShippingLeafEntryCommand.Outcome ← try
        Tools.ShippingLeafDesignCommand.leafDesign f
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv savedEnv
        modify fun st => { st with messages := savedMsgs }
        pure { tag := "FAILED", data := s!"{f}: the generator threw outside its own handler",
               note := msg, lines := #[] }
    logInfo m!"LEAFDESIGN DATA {o.data}"
    for l in o.lines do logInfo m!"{l}"
    logInfo m!"LEAFDESIGN {o.tag} {f}: {o.note}"
    let made : Bool := o.tag == "GENERATED" || o.tag == "REBUILT"
    let leaf := f ++ `machine_design_leaf0
    let prem := o.lines.filter fun l => has l " PREMISE "
    let bad := (prem.filter fun l => has l "NOT ALLOWED").size
    -- the generator's audit: logs its listing, then asserts
    let envA ← getEnv
    let audit : String ← try
        if made then
          liftTermElabM (Tools.ShippingLeafDesignCommand.audit f)
          pure "OK"
        else
          pure "-"
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv envA
        pure s!"FAILED: {msg}"
    -- the parents' gap tool
    let gapName : Name := f ++ `machine_design_leaf0_gap
    let envG ← getEnv
    let msgsG := (← get).messages
    let gap : String ← try
        if !made then
          pure "-"
        else if envG.contains gapName then
          pure "not run: the gap theorem exists already"
        else
          let report ← liftTermElabM (Tools.ShippingFinalGoalCommand.gapOf leaf gapName)
          logInfo m!"GOALGAP {gapName} from {leaf}\n{String.intercalate "\n" report.toList}"
          let hyps ← liftTermElabM do
            let ci ← getConstInfo gapName
            forallTelescope ci.type fun xs _ => do
              let mut out : List String := []
              for x in xs do
                let nm := (← x.fvarId!.getUserName).toString
                if nm.startsWith "gap_" then out := out ++ [nm]
              return out
          pure s!"gap hypotheses {hyps}"
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv envG
        modify fun st => { st with messages := msgsG }
        pure s!"gap tool FAILED: {msg}"
    let left : Bool := (← getEnv).contains leaf
    let ms := (← IO.monoMsNow) - t0
    let auditS : String := clip audit 400
    let gapS : String := clip gap 400
    if made then
      logInfo m!"LEAFSWEEP RESULT {f}: {o.tag}; premise lines listed by the generator {prem.size}, NOT ALLOWED {bad}; audit {auditS}; {gapS}; {leaf} in the environment: {left}; {ms} ms. SCOPE of this line: ONE declaration as an entry, depth 0, no call; data conditions decided for it (conditions, not reductions); the run, MachineDefines {f} and ChildBnd stay premises; DesignSV of the module list over the returned design's child map — not the SV string, not #sim"
    else
      logInfo m!"LEAFSWEEP RESULT {f}: {o.tag} — {clip o.note 600}; {leaf} in the environment: {left}; {ms} ms"
    rows.modify fun a => a.push
      { decl := toString f, tag := o.tag, audit := audit, gap := gap, bad := bad,
        listed := prem.size, left := left, ms := ms, note := o.note }

/-- `#leaf_sweep_summary`: see the file header. An error only on an
inconsistency of what this file measured. -/
elab "#leaf_sweep_summary" : command => do
  let rs ← rows.get
  let mut lines : Array String := #[]
  let mut problems : Array String := #[]
  for r in rs do
    let made : Bool := r.tag == "GENERATED" || r.tag == "REBUILT"
    if made then
      lines := lines.push s!"LEAFSWEEP ROW {r.decl}: {r.tag}; listed {r.listed}, NOT ALLOWED {r.bad}; audit {clip r.audit 160}; {clip r.gap 160}; {r.ms} ms"
      unless r.audit == "OK" do
        problems := problems.push s!"{r.decl}: {r.tag} but its audit did not pass ({clip r.audit 300})"
      unless r.bad == 0 do
        problems := problems.push s!"{r.decl}: {r.tag} with {r.bad} NOT ALLOWED lines in the generator's listing"
      unless r.left do
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_leaf0 is not in the environment"
    else
      lines := lines.push s!"LEAFSWEEP ROW {r.decl}: {r.tag} — {clip r.note 240}; {r.ms} ms"
      if r.left then
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_leaf0 is in the environment"
  let count (t : String) : Nat := (rs.filter fun r => r.tag == t).size
  let namesOf (t : String) : List String := (rs.filter fun r => r.tag == t).toList.map (·.decl)
  logInfo m!"{String.intercalate "\n" lines.toList}"
  logInfo m!"LEAFSWEEP SUMMARY of {rs.size}: GENERATED {count "GENERATED"} {namesOf "GENERATED"}; REBUILT {count "REBUILT"} {namesOf "REBUILT"}; REFUSED {count "REFUSED"} {namesOf "REFUSED"}; FAILED {count "FAILED"} {namesOf "FAILED"}; UNRESOLVED {count "UNRESOLVED"} {namesOf "UNRESOLVED"}. Each GENERATED / REBUILT row: its audit passed and its listing has 0 NOT ALLOWED (asserted below). No class and no count was expected by this file. A GENERATED row is about ONE declaration as an entry at depth 0 — DesignSV of the module list, with the run, the reflection and ChildBnd as premises; it is not a statement about the SV string, #sim, or any other declaration."
  if rs.isEmpty then
    throwError "LEAFSWEEP: nothing was swept in this file"
  unless problems.isEmpty do
    throwError "LEAFSWEEP: {problems.size} inconsistencies in what was measured:\n{String.intercalate "\n" problems.toList}"

end Tools.ShippingLeafSweepCommand
