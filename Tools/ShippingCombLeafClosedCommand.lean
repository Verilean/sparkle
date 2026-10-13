import Lean.Elab.Command
import Tools.ShippingCombLeafShape
import Tools.ShippingCombLeafCommand

/-! # `#machine_comb_design0 f` and `#comb_closed_sweep f`: a SLOTLESS leaf as an entry at the design level, CLOSED (round par/b-33)

WRITTEN, NOT BUILT. `#machine_comb_design` and the OPEN endpoint
`f.machine_design_comb0_open` (BUILT at 4103e86f) are NOT changed.

## What is generated

For a machine-route declaration `f` without calls and without a register
slot, with the one output `out`, whose `f.machine_ships_comb` exists:

    f.machine_combKid : CombKid ``f f.machineData          -- as before (reused when present)
    f.machine_combPos : ∀ o ∈ f.machineData.shape.layout.outs, 0 < o.width     -- decided
    f.machine_design_comb0 :
      ∀ {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) … (b, design) w')
        (entry : MachineDefines … f f.machineData.shape),
        ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          (ChildBnd mref cref w →
           … DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) … )

    := fun hr entry =>
         Tools.ShippingCombLeafShape.comb_entry_design0_of_ships
           (f.machine_ships_comb hr entry (f.machine_closes mctx mref cctx cref))
           f.machine_combKid f.machine_combPos hr entry (f.machine_closes mctx mref cctx cref)

The term is the register leaves' (`Tools.ShippingLeafDesignCommand.endpointTerm`)
with `machine_ships_comb` in place of `machine_ships_wired`: the ship-level
endpoint is used as a HYPOTHESIS of the bridge, never opened. A TRANSPORTED
endpoint (`f.machine_ships_comb` under `Eq.mpr`: the sign-normalised
declarations the open generator refused) therefore needs no special
treatment here — as for the register leaves `outer` / `siblings`.

The statement check is the register leaves' own
(`Tools.ShippingLeafDesignCommand.checkStatementWith`): exactly two
proposition binders (the run, `MachineDefines f`), one existential, exactly
ONE antecedent under it and it is `ChildBnd`, 0 NOT ALLOWED by
`Tools.ShippingFinalGoalCommand.allowed`; none of `simpleBody`, `seqCheck`,
`seqNames`, `MachineCloses`, `InvW`, `printOk`, `isAssign` nor a parents'
checker constant; the conclusion about `DesignSV` over `childMap`. A
statement that fails is not added.

## What the kernel evaluates per declaration

NOT the module. (S1) / (S2) are theorems about every run
(`Tools.ShippingCombLeafShape.comb_entry_shape`); nothing about the run's
module is decided. Per declaration: the eleven data conditions of
`f.machine_combKid` (BUILT for 26 declarations: `decide` on
`f.machineData`'s shape and layout — the call check, the late binders, the
output widths / names / scalar types) and one more, `f.machine_combPos` (a
`decide` over the ONE output field's width). No `native_decide`.

## Scope and refusals

The scan of `#machine_comb_design` (`Tools.ShippingCombLeafCommand.scan`):
not a machine / calls / a register slot / no machine endpoint / no
`f.machine_ships_comb` / output names other than `["out"]`; then
`f.machine_closes` not derivable. The open generator's refusal "not
machine_ships_comb on 11 arguments" does NOT exist here.

`#comb_closed_sweep f` is an error in no case; `#comb_closed_sweep_summary`
only on an inconsistency of what the file measured.

SCOPE of a generated `f.machine_design_comb0` (binding for any report): ONE
declaration as an entry, depth 0, no call, no register, one output `out`;
data conditions decided for that declaration (conditions, not reductions);
the run, the reflection `MachineDefines f` and the runtime boundary
`ChildBnd` stay premises; `DesignSV` of the module LIST over the returned
design's child map — not the SV string, not `#sim`; the seeding is `seedR`
(`rst` low). -/
namespace Tools.ShippingCombLeafClosedCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- **`c.machine_combPos`, generated**: the output fields of `c` are not
empty (returned unchanged when it exists). -/
def combPosTheorem (c : Name) : CommandElabM Name := do
  let name := c ++ `machine_combPos
  if (← getEnv).contains name then return name
  let data : Ident := mkIdent (`_root_ ++ c ++ `machineData)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) :
        ∀ o ∈ ($data).shape.layout.outs, 0 < o.width := by
      first | decide | decide +kernel))
  checkMade name before
  return name

/-- The statement and the proof of `f.machine_design_comb0` (file header).
Nothing is added to the environment. -/
def endpointTerm (f cl kid pos : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let comb := f ++ `machine_ships_comb
  let cInfo ← getConstInfo comb
  unless cInfo.levelParams.isEmpty do throwError "{comb}: universe parameters"
  let value ← forallTelescopeReducing cInfo.type fun xs _ => do
    -- mctx mref cctx cref w w' b design hr entry closes
    unless xs.size == 11 do
      throwError "{comb}: {xs.size} binders, expected 11 (the four contexts, two worlds, the module, the design, the run, MachineDefines, MachineCloses)"
    let tRun ← instantiateMVars (← inferType xs[8]!)
    let tDef ← instantiateMVars (← inferType xs[9]!)
    let tCl ← instantiateMVars (← inferType xs[10]!)
    unless tRun.isAppOf ``Tools.ShippingEntrySoundness.RunsTo do
      throwError "{comb}: binder 9 is not the run: {tRun}"
    unless tDef.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 do
      throwError "{comb}: binder 10 is not MachineDefines: {tDef}"
    unless tCl.isAppOfArity ``Tools.ShippingMachineEntry.MachineCloses 6 do
      throwError "{comb}: binder 11 is not MachineCloses: {tCl}"
    let hr := xs[8]!
    let entry := xs[9]!
    let closes := mkAppN (mkConst cl) #[xs[0]!, xs[1]!, xs[2]!, xs[3]!]
    let closesT ← inferType closes
    unless ← isDefEq closesT tCl do
      throwError "{cl}: its statement at the contexts is not the MachineCloses binder of {comb}:{indentExpr closesT}\nagainst{indentExpr tCl}"
    let ships := mkAppN (mkConst comb) ((xs.extract 0 10).push closes)
    let body ← mkAppM ``Tools.ShippingCombLeafShape.comb_entry_design0_of_ships
      #[ships, mkConst kid, mkConst pos, hr, entry, closes]
    mkLambdaFVars ((xs.extract 0 8) ++ #[hr, entry]) body
  let value ← instantiateMVars value
  if value.hasMVar then
    throwError "{f}: the proof term of machine_design_comb0 has an unassigned metavariable"
  let type ← instantiateMVars (← inferType value)
  if type.hasMVar then
    throwError "{f}: the statement of machine_design_comb0 has an unassigned metavariable"
  return (type, value)

/-- The outcome of the generator on one declaration. -/
structure Outcome where
  /-- `GENERATED`, `REBUILT`, `REFUSED` or `FAILED` -/
  tag : String
  data : String
  note : String
  lines : Array String

/-- After the scan: the closing, `CombKid`, the output-width condition, the
endpoint (added, or rebuilt and compared). -/
def combDesign0Core (f : Name) : CommandElabM (Bool × String × Array String) := do
  let name := f ++ `machine_design_comb0
  let was : Bool := (← getEnv).contains name
  let cl ← liftTermElabM do
    let some n ← Tools.ShippingMachineClosesGen.closesTheorem? f
      | throwError "{f}: MachineCloses is not derived from the data (closesTheorem?): {f}.machine_closes is neither there nor generated"
    pure n
  let kid ← noAsync (Tools.ShippingCombLeafCommand.combKidTheorem f)
  let pos ← noAsync (combPosTheorem f)
  let res ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ← endpointTerm f cl kid pos
      let lines ← Tools.ShippingLeafDesignCommand.checkStatementWith "COMBDESIGN0" f name type
      let (made, line) ← Tools.ShippingNoPortsKidsCommand.addOrCompare name type value
      for n in [made, kid, pos, cl] do
        for ax in ← Lean.collectAxioms n do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "{n} uses a non-standard axiom: {ax}"
      pure (line, lines)
  let note : String :=
    s!"{res.1}. From {f}.machine_ships_comb by Tools.ShippingCombLeafShape.comb_entry_design0_of_ships: its three check antecedents discharged from the run and ChildBnd (the module is of the simple shape and has a cast statement — comb_entry_shape; its own text — comb_entry_text_out), its MachineShipsComb conclusion carried to DesignSV (childMap design.modules) 0 (checkedOptimize b) with 'every closed run shows the source'; data conditions {kid}, {pos}; closing {cl}. Premises: the run, MachineDefines {f} (binders), ChildBnd (the one antecedent under ∃ raw) — nothing else"
  return (was, note, res.2)

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def combDesign0 (f : Name) : CommandElabM Outcome := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let (data, refusal) ← Tools.ShippingCombLeafCommand.scan f
  match refusal with
  | some reason => return { tag := "REFUSED", data, note := reason, lines := #[] }
  | none =>
    try
      let (existed, note, lines) ← combDesign0Core f
      let tag : String := if existed then "REBUILT" else "GENERATED"
      return { tag, data, note, lines }
    catch ex =>
      let msg ← ex.toMessageData.toString
      let newMsgs := (← get).messages.toList.drop savedMsgs.toList.length
      let errs ← (newMsgs.filter (·.severity == .error)).mapM fun m => m.data.toString
      setEnv savedEnv
      modify fun st => { st with messages := savedMsgs }
      let refused : Bool := has msg "MachineCloses is not derived from the data"
      let tag : String := if refused then "REFUSED" else "FAILED"
      return { tag, data,
               note := s!"{msg} — errors logged by the generated theorems: {errs.take 2}",
               lines := #[] }

/-- `#machine_comb_design0 f`: an error where it is refused or fails. -/
elab "#machine_comb_design0 " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← combDesign0 f
  logInfo m!"COMBDESIGN0 DATA {o.data}"
  for l in o.lines do logInfo m!"{l}"
  if o.tag == "REFUSED" || o.tag == "FAILED" then
    throwError "COMBDESIGN0 {o.tag} {f}: {o.note}"
  else
    logInfo m!"COMBDESIGN0 {o.tag} {f}: {o.note}"

/-- The audit of an existing `f.machine_design_comb0` (throws on a
violation): the statement check again, on the STORED statement; that the
base `f.machine_ships_comb` mentions the three check constants and asks
`MachineCloses`; standard axioms of the endpoint, the data theorems, the
closing and the general theorems. Returns the premise lines. -/
def audit (f : Name) : MetaM (Array String) := do
  let leaf := f ++ `machine_design_comb0
  let base := f ++ `machine_ships_comb
  let info ← getConstInfo leaf
  let binfo ← getConstInfo base
  let mentions (t : Lean.Expr) (n : Name) : Bool := (t.find? (·.isConstOf n)).isSome
  let inBase : List Name := Tools.ShippingLeafEntryCommand.checkConsts.filter (mentions binfo.type)
  let baseCloses : Bool := mentions binfo.type ``Tools.ShippingMachineEntry.MachineCloses
  logInfo m!"COMBDESIGN0 AUDIT {f}: of {Tools.ShippingLeafEntryCommand.checkConsts} — in {base}: {inBase} (MachineCloses there: {baseCloses}); in {leaf}: {Tools.ShippingLeafDesignCommand.forbiddenAll.filter (mentions info.type)}"
  unless inBase.length == 3 do
    throwError "{base}: expected to mention the three check constants, mentions {inBase}"
  unless baseCloses do
    throwError "{base}: expected to ask MachineCloses"
  let lines ← Tools.ShippingLeafDesignCommand.checkStatementWith "COMBDESIGN0 AUDIT" f leaf info.type
  for n in [leaf, f ++ `machine_combKid, f ++ `machine_combPos, f ++ `machine_closes,
      ``Tools.ShippingCombLeafShape.comb_entry_design0_of_ships,
      ``Tools.ShippingCombLeafShape.comb_entry_shape,
      ``Tools.ShippingCombLeafShape.transition_simple_of_run,
      ``Tools.ShippingCastMerge.mergeDuplicates_hasCast,
      ``Tools.ShippingCombLeafDesign.comb_entry_text_out,
      ``Tools.ShippingCombLeafDesign.comb_design_of_ships] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  return lines

/-- One swept declaration. -/
structure Row where
  decl : String
  tag : String
  note : String
  audit : String
  gap : String
  listed : Nat
  bad : Nat
  left : Bool
  ms : Nat

/-- The rows of the file being elaborated. -/
initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]

/-- `#comb_closed_sweep f`: the closed generator, its audit and the gap tool;
LOGGED, never an error. -/
elab "#comb_closed_sweep " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"COMBCLOSED START {shown}"
  logInfo m!"COMBCLOSED START {shown}"
  let t0 ← IO.monoMsNow
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"COMBCLOSED RESULT {shown}: UNRESOLVED — the identifier is not a constant of the imports"
    rows.modify fun a => a.push
      { decl := shown, tag := "UNRESOLVED", note := "the identifier does not resolve", audit := "-",
        gap := "-", listed := 0, bad := 0, left := false, ms := 0 }
  | some f =>
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    let o : Outcome ← try
        combDesign0 f
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv savedEnv
        modify fun st => { st with messages := savedMsgs }
        pure { tag := "FAILED", data := s!"{f}: the generator threw outside its own handler",
               note := msg, lines := #[] }
    logInfo m!"COMBDESIGN0 DATA {o.data}"
    for l in o.lines do logInfo m!"{l}"
    logInfo m!"COMBDESIGN0 {o.tag} {f}: {o.note}"
    let made : Bool := o.tag == "GENERATED" || o.tag == "REBUILT"
    let leaf := f ++ `machine_design_comb0
    let prem := o.lines.filter fun l => has l " PREMISE "
    let bad := (prem.filter fun l => has l "NOT ALLOWED").size
    let envA ← getEnv
    let auditS : String ← try
        if made then
          let ls ← liftTermElabM (audit f)
          for l in ls do logInfo m!"{l}"
          pure "OK"
        else
          pure "-"
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv envA
        pure s!"FAILED: {msg}"
    let gapName : Name := f ++ `machine_design_comb0_gap
    let envG ← getEnv
    let msgsG := (← get).messages
    let gapS : String ← try
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
    if made then
      logInfo m!"COMBCLOSED RESULT {f}: {o.tag}; premise lines listed by the generator {prem.size}, NOT ALLOWED {bad}; audit {clip auditS 400}; {clip gapS 400}; {leaf} in the environment: {left}; {ms} ms. SCOPE of this line: ONE declaration as an entry, depth 0, no call, no register, one output `out`; data conditions decided for it (conditions, not reductions); the run, MachineDefines {f} and ChildBnd stay premises; DesignSV of the module list over the returned design's child map — not the SV string, not #sim"
    else
      logInfo m!"COMBCLOSED RESULT {f}: {o.tag} — {clip o.note 600}; {leaf} in the environment: {left}; {ms} ms"
    rows.modify fun a => a.push
      { decl := toString f, tag := o.tag, note := o.note, audit := auditS, gap := gapS,
        listed := prem.size, bad, left, ms }

/-- `#comb_closed_sweep_summary`: the rows and the counts; an error only on
an inconsistency of what this file measured. -/
elab "#comb_closed_sweep_summary" : command => do
  let rs ← rows.get
  let mut lines : Array String := #[]
  let mut problems : Array String := #[]
  for r in rs do
    let made : Bool := r.tag == "GENERATED" || r.tag == "REBUILT"
    if made then
      lines := lines.push s!"COMBCLOSED ROW {r.decl}: {r.tag}; listed {r.listed}, NOT ALLOWED {r.bad}; audit {clip r.audit 160}; {clip r.gap 160}; {r.ms} ms"
      unless r.audit == "OK" do
        problems := problems.push s!"{r.decl}: {r.tag} but its audit did not pass ({clip r.audit 300})"
      unless r.bad == 0 do
        problems := problems.push s!"{r.decl}: {r.tag} with {r.bad} NOT ALLOWED lines in the generator's listing"
      unless r.left do
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_comb0 is not in the environment"
    else
      lines := lines.push s!"COMBCLOSED ROW {r.decl}: {r.tag} — {clip r.note 240}; {r.ms} ms"
      if r.left then
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_comb0 is in the environment"
  let count (t : String) : Nat := (rs.filter fun r => r.tag == t).size
  let namesOf (t : String) : List String := (rs.filter fun r => r.tag == t).toList.map (·.decl)
  logInfo m!"{String.intercalate "\n" lines.toList}"
  logInfo m!"COMBCLOSED SUMMARY of {rs.size}: GENERATED {count "GENERATED"} {namesOf "GENERATED"}; REBUILT {count "REBUILT"} {namesOf "REBUILT"}; REFUSED {count "REFUSED"} {namesOf "REFUSED"}; FAILED {count "FAILED"} {namesOf "FAILED"}; UNRESOLVED {count "UNRESOLVED"} {namesOf "UNRESOLVED"}. Each GENERATED / REBUILT row: its audit passed and its listing has 0 NOT ALLOWED (asserted below). No class and no count was expected by this file. A GENERATED row is about ONE declaration as an entry at depth 0 — DesignSV of the module list, with the run, the reflection and ChildBnd as premises; not the SV string, not #sim, not any other declaration."
  if rs.isEmpty then
    throwError "COMBCLOSED: nothing was swept in this file"
  unless problems.isEmpty do
    throwError "COMBCLOSED: {problems.size} inconsistencies in what was measured:\n{String.intercalate "\n" problems.toList}"

end Tools.ShippingCombLeafClosedCommand
