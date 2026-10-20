import Lean.Elab.Command
import Tools.ShippingLeafEntryCommand
import Tools.ShippingLeafDesign

/-! # `#machine_leaf_design f`: a leaf register machine AS AN ENTRY, at the design level (round par/b-27)

`#machine_leaf_entry f` (`Tools/ShippingLeafEntryCommand.lean`) gives
`f.machine_ships_leafC`: ONE module (`MachineShips` at the emitter's own
width map). This command gives the design-level endpoint of the same
declaration, in the shape of the parents' depth-0 endpoints
(`f.machine_design_noPortsR0_closed`):

    f.machine_design_leaf0 :
      ∀ {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref f f.machineData.shape),
        ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          (ChildBnd mref cref w →
            ∃ ids, … ∃ cache regs, … ∀ i bools bits T ins st0 mems kids, (use conditions) →
              (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                  ⟨st0, mems, kids⟩ envsO ∧ envsO.length = T ∧ (the source on the outputs))
              ∧ ∀ envs', DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                  ⟨st0, mems, kids⟩ envs' → envs'.length = T ∧ (the source on the outputs))

    := fun hr entry =>
         Tools.ShippingLeafDesign.leaf_entry_design0_of_wired
           (f.machine_ships_wired hr entry (f.machine_closes mctx mref cctx cref))
           (f.machine_leafKid entry) hr

The statement is the inferred type of the term (`dom`, `src` are those of
`f.machine_ships_wired`). The use conditions and every difference from a
parent's endpoint are in the header of `Tools/ShippingLeafDesign.lean`.

## The name

The parents' depth-0 design-level names are `f.machine_design_sv0`,
`f.machine_design_svR0`, `f.machine_design_noPortsR0` and
`f.machine_design_noPortsR0_closed`: `machine_design_` (the conclusion is
`DesignSV`), a stage of the parents' head (`sv`, `noPorts`, `R`), the depth,
and `_closed` when `MachineClosesAt` is discharged. A leaf has none of the
head's stages (no head: `Tools/ShippingLeafDesign.lean`, "The route") and no
open form (its closing `f.machine_closes` is discharged inside the term), so:
`machine_design_` + `leaf` (the scope: an entry without calls) + `0` (the
depth) — `f.machine_design_leaf0`. No `_closed` suffix: there is no
`machine_design_leaf0` with a `MachineCloses` binder to distinguish it from.
No other file uses the name (`grep`).

## What is reused, and what is new

REUSED (BUILT, by import): the scope scan and its refusal lines
(`Tools.ShippingLeafEntryCommand.scan` — not a machine, memory, has calls,
slotless, no endpoint, no `machine_ships_wired`), the outcome record
(`Outcome`), `forbidden`, `checkConsts`; `closesTheorem?`;
`leafKidTheorem` (which returns an existing `f.machine_leafKid` unchanged: a
hypothesis-free data theorem whose statement is fixed by `f`);
`Tools.ShippingNoPortsKidsCommand.addOrCompare` — the COMPARE path: if
`f.machine_design_leaf0` EXISTS it is rebuilt all the same, added as
`f.machine_design_leaf0_regen` (kernel-checked) and its statement must be
`isDefEq` the existing one, an error otherwise. Never a silent return.

The command does NOT need `f.machine_ships_leafC`: it starts, like
`#machine_leaf_entry`, from `f.machine_ships_wired`.

NEW: `endpointTerm` (the term above) and `checkStatement` — before adding,
the produced statement must have exactly TWO proposition binders (one
`RunsTo`, one `MachineDefines` about `f`), both ALLOWED by
`Tools.ShippingFinalGoalCommand.allowed`; the shape `∃ raw, P ∧ (A → C)` with
exactly ONE antecedent `A`, which is `ChildBnd` (ALLOWED); no occurrence of
`simpleBody`, `seqCheck`, `seqNames`, `MachineCloses`, `InvW`, `printOk`,
`isAssign` (`forbidden`) nor of the parents' seven checker constants
(`checkers`: `portsMatchB`, `kidsPass`, `designCheck`, `shipsHierCheck`,
`outsCheck`, `kidsMaskedN`, `hierCheck`); `C` mentions `DesignSV` and
`childMap`. A statement that fails is not added (FAILED).

`#machine_leaf_design_try f "GENERATED|REBUILT|REFUSED|FAILED"` logs the
outcome and is an error when its class is not the expected one; on REFUSED /
FAILED the environment and the message log are put back. Every outcome is
preceded by a `LEAFDESIGN DATA` line with the reader's data.

The shape `∃ raw, P ∧ (A → C)` is the one `#machine_goal_gap_of` and the
parents' premise listing (`Tests.Compiler.NoPortsTest.premiseLines`) read:
the leaf endpoint is audited by the SAME tools as the parents'
(`Tests/Compiler/LeafDesignCntTest.lean`).

SCOPE of a generated theorem (binding for any report): ONE declaration as an
entry, depth 0, no call; `DesignSV` over the child map of the run's returned
design — the module LIST, not the SV string, not `#sim`; data conditions
decided per declaration (conditions, not reductions); the run, the reflection
and the runtime boundary `ChildBnd` stay premises; a compiler WITH the two
guards of `Sparkle/IR/RefineCheck.lean` (each falling back to its input
module).

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingLeafDesignCommand
open Lean Meta Elab Command

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- The parents' seven checker constants (the list of
`Tests.Compiler.NoPortsTest.checkers`). -/
def checkers : List Name :=
  [``Tools.ShippingDesignSV.portsMatchB,
   ``Tools.ShippingDesignSV.kidsPass,
   ``Tools.ShippingDesignSV.designCheck,
   ``Tools.ShippingHierPremisesBase.shipsHierCheck,
   ``Tools.ShippingDesignSVBack.outsCheck,
   ``Tools.ShippingMachineShipsDepth.kidsMaskedN,
   ``Tools.ShippingHierPremisesBase.hierCheck]

/-- What a design-level leaf statement must not mention: the check, guard
and closing constants of the leaf-entry command, and the parents' checkers. -/
def forbiddenAll : List Name :=
  Tools.ShippingLeafEntryCommand.forbidden ++ checkers

/-- One antecedent under the existentials: printed, whether it is allowed,
whether it is `ChildBnd`. -/
structure AnteLine where
  text : String
  ok : Bool
  isBnd : Bool

/-- What is under the binders of an endpoint `∃ w…, P ∧ (A₁ → … → C)`. -/
structure Inner where
  /-- the number of existentials -/
  nEx : Nat
  /-- the antecedents `Aᵢ` -/
  antes : Array AnteLine
  /-- `C`, printed -/
  concl : String
  /-- `C` mentions `DesignSV` -/
  hasDesign : Bool
  /-- `C` mentions `childMap` -/
  hasChildMap : Bool

/-- Reads the body of an endpoint. Throws when it is not of the shape. -/
partial def inner (ty : Lean.Expr) (nEx : Nat) : MetaM Inner := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm : Name := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun x => inner (mkApp p x).headBeta (nEx + 1)
  else if ty.isAppOfArity ``And 2 then
    let mut R : Lean.Expr := ty.getArg! 1
    let mut antes : Array AnteLine := #[]
    while (← Tools.ShippingFinalGoalCommand.isPropArrow R) do
      let A := R.bindingDomain!
      let ppA ← ppExpr A
      antes := antes.push
        { text := toString ppA,
          ok := Tools.ShippingFinalGoalCommand.allowed A,
          isBnd := A.isAppOf ``Tools.ShippingChildInv.ChildBnd }
      R := R.bindingBody!
    let ppR ← ppExpr R
    let hasD : Bool := (R.find? (·.isConstOf ``Tools.ShippingDesignSV.DesignSV)).isSome
    let hasC : Bool := (R.find? (·.isConstOf ``Tools.ShippingMachineLinked.childMap)).isSome
    return { nEx := nEx, antes := antes, concl := toString ppR, hasDesign := hasD,
             hasChildMap := hasC }
  else
    throwError "expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- The statement checks of a design-level leaf endpoint; the log lines (one
per proposition binder, one per antecedent under the existential, then the
conclusion). Throws on a violation. `tag` prefixes the lines. -/
def checkStatementWith (tag : String) (f leaf : Name) (type : Lean.Expr) :
    MetaM (Array String) := do
  for c in forbiddenAll do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{leaf}: the statement mentions {c}"
  let report ← forallTelescope type fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Nat := 0
    let mut runs : Nat := 0
    let mut defs : Nat := 0
    let mut props : Nat := 0
    for x in xs do
      let t0 ← inferType x
      let t ← instantiateMVars t0
      let isP ← isProp t
      if isP then
        props := props + 1
        let pp ← ppExpr t
        let nm ← x.fvarId!.getUserName
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then runs := runs + 1
        if t.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
          let same ← isDefEq (t.getArg! 4) (toExpr f)
          if same then defs := defs + 1
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"{tag} PREMISE {leaf}: ALLOWED     binder {nm} : {pp}"
        else
          bad := bad + 1
          lines := lines.push s!"{tag} PREMISE {leaf}: NOT ALLOWED binder {nm} : {pp}"
    let inn ← inner body 0
    let mut bndA : Nat := 0
    for a in inn.antes do
      if a.isBnd then bndA := bndA + 1
      if a.ok then
        lines := lines.push
          s!"{tag} PREMISE {leaf}: ALLOWED     antecedent under the existential : {a.text}"
      else
        bad := bad + 1
        lines := lines.push
          s!"{tag} PREMISE {leaf}: NOT ALLOWED antecedent under the existential : {a.text}"
    lines := lines.push s!"{tag} CONCLUSION {leaf}: {inn.concl}"
    let counts : List Nat := [bad, runs, defs, props, inn.antes.size, bndA, inn.nEx]
    return (lines, counts, inn.hasDesign && inn.hasChildMap)
  let lines : Array String := report.1
  let counts : List Nat := report.2.1
  let concl : Bool := report.2.2
  let bad : Nat := counts.getD 0 0
  let runs : Nat := counts.getD 1 0
  let defs : Nat := counts.getD 2 0
  let props : Nat := counts.getD 3 0
  let nAnte : Nat := counts.getD 4 0
  let bndA : Nat := counts.getD 5 0
  let nEx : Nat := counts.getD 6 0
  unless bad == 0 do
    throwError "{leaf}: {bad} NOT ALLOWED premises, expected 0: {lines}"
  unless props == 2 && runs == 1 && defs == 1 do
    throwError "{leaf}: {props} proposition binders (RunsTo {runs}, MachineDefines {f} {defs}), expected exactly one of each and no other"
  unless nEx == 1 do
    throwError "{leaf}: {nEx} existentials in front of the conjunction, expected 1 (raw)"
  unless nAnte == 1 && bndA == 1 do
    throwError "{leaf}: {nAnte} antecedents under the existential ({bndA} ChildBnd), expected exactly one, ChildBnd"
  unless concl do
    throwError "{leaf}: the conclusion does not mention DesignSV over childMap"
  return lines

/-- `checkStatementWith` with the generator's prefix. -/
def checkStatement (f leaf : Name) (type : Lean.Expr) : MetaM (Array String) :=
  checkStatementWith "LEAFDESIGN" f leaf type

/-- The statement and the proof of `f.machine_design_leaf0` (file header).
Nothing is added to the environment. `cl` is `f.machine_closes`, `kid` is
`f.machine_leafKid`. -/
def endpointTerm (f cl kid : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let wired := f ++ `machine_ships_wired
  let wInfo ← getConstInfo wired
  unless wInfo.levelParams.isEmpty do throwError "{wired}: universe parameters"
  let value ← forallTelescopeReducing wInfo.type fun xs _ => do
    -- mctx mref cctx cref w w' b design hr entry closes
    unless xs.size == 11 do
      throwError "{wired}: {xs.size} binders, expected 11 (the four contexts, two worlds, the module, the design, the run, MachineDefines, MachineCloses)"
    let tRun ← instantiateMVars (← inferType xs[8]!)
    let tDef ← instantiateMVars (← inferType xs[9]!)
    let tCl ← instantiateMVars (← inferType xs[10]!)
    unless tRun.isAppOf ``Tools.ShippingEntrySoundness.RunsTo do
      throwError "{wired}: binder 9 is not the run: {tRun}"
    unless tDef.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 do
      throwError "{wired}: binder 10 is not MachineDefines: {tDef}"
    unless tCl.isAppOfArity ``Tools.ShippingMachineEntry.MachineCloses 6 do
      throwError "{wired}: binder 11 is not MachineCloses: {tCl}"
    let hr := xs[8]!
    let entry := xs[9]!
    let closes := mkAppN (mkConst cl) #[xs[0]!, xs[1]!, xs[2]!, xs[3]!]
    let closesT ← inferType closes
    unless ← isDefEq closesT tCl do
      throwError "{cl}: its statement at the contexts is not the MachineCloses binder of {wired}:{indentExpr closesT}\nagainst{indentExpr tCl}"
    let ships := mkAppN (mkConst wired) ((xs.extract 0 10).push closes)
    let kidP ← mkAppM kid #[entry]
    let body ← mkAppM ``Tools.ShippingLeafDesign.leaf_entry_design0_of_wired #[ships, kidP, hr]
    mkLambdaFVars ((xs.extract 0 8) ++ #[hr, entry]) body
  let value ← instantiateMVars value
  if value.hasMVar then
    throwError "{f}: the proof term of machine_design_leaf0 has an unassigned metavariable"
  let type ← instantiateMVars (← inferType value)
  if type.hasMVar then
    throwError "{f}: the statement of machine_design_leaf0 has an unassigned metavariable"
  return (type, value)

/-- After the scope scan: the closing and `LeafKid` when absent, then the
endpoint (added, or rebuilt and compared). -/
def leafDesignCore (f : Name) : CommandElabM (Bool × String × Array String) := do
  let name := f ++ `machine_design_leaf0
  let kidName := f ++ `machine_leafKid
  let closesName := f ++ `machine_closes
  let envBefore ← getEnv
  let closesWas : Bool := envBefore.contains closesName
  let kidWas : Bool := envBefore.contains kidName
  let leafWas : Bool := envBefore.contains name
  let cl ← liftTermElabM do
    let some n ← Tools.ShippingMachineClosesGen.closesTheorem? f
      | throwError "{f}: MachineCloses is not derived from the data (closesTheorem?: MachineData.letsOk is false — a `let` that is the variable of a `let` with a driven field — or {f}.machine_ok / machine_body are missing): {closesName} is neither there nor generated, and LeafKid.closes asks it in every context"
    pure n
  let kid ← noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem f)
  let res ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ← endpointTerm f cl kid
      let lines ← checkStatement f name type
      let (made, line) ← Tools.ShippingNoPortsKidsCommand.addOrCompare name type value
      for n in [made, kid, cl] do
        for ax in ← Lean.collectAxioms n do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "{n} uses a non-standard axiom: {ax}"
      pure (line, lines)
  let word (existed : Bool) : String :=
    if existed then "EXISTING before this command (not regenerated)" else "GENERATED here"
  let wClose : String := word closesWas
  let wKid : String := word kidWas
  let note : String :=
    s!"{res.1}. From {f}.machine_ships_wired by Tools.ShippingLeafDesign.leaf_entry_design0_of_wired: its three check antecedents discharged at wof = wofOf (checkedOptimize b) (leaf_entry_textChecks_closed), its MachineShips conclusion carried to DesignSV (childMap design.modules) 0 (checkedOptimize b) with 'every closed run shows the source' (designSV0_of_leaf, designSV0_leaf_unique), its MachineCloses binder by {cl} — {wClose}; LeafKid by {kid} — {wKid}. Premises: the run, MachineDefines {f} (binders), ChildBnd (the one antecedent under ∃ raw) — nothing else"
  return (leafWas, note, res.2)

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. The scope and its refusal lines are those
of `#machine_leaf_entry` (`Tools.ShippingLeafEntryCommand.scan`). -/
def leafDesign (f : Name) : CommandElabM Tools.ShippingLeafEntryCommand.Outcome := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let s ← Tools.ShippingLeafEntryCommand.scan f
  let there : Bool := savedEnv.contains (f ++ `machine_design_leaf0)
  let data : String := s!"{s.data}. {f}.machine_design_leaf0 in the environment: {there}"
  match s.refusal with
  | some reason =>
    return { tag := "REFUSED", data := data, note := reason, lines := #[] }
  | none =>
    try
      let (existed, note, lines) ← leafDesignCore f
      let tag : String := if existed then "REBUILT" else "GENERATED"
      return { tag := tag, data := data, note := note, lines := lines }
    catch ex =>
      let msg ← ex.toMessageData.toString
      -- the errors a generated theorem logged, before they are dropped
      let newMsgs := (← get).messages.toList.drop savedMsgs.toList.length
      let errs ← (newMsgs.filter (·.severity == .error)).mapM fun m => m.data.toString
      setEnv savedEnv
      modify fun st => { st with messages := savedMsgs }
      -- a missing closing is a matter of scope, not of a failed proof
      let refused : Bool := (msg.splitOn "MachineCloses is not derived from the data").length > 1
      let tag : String := if refused then "REFUSED" else "FAILED"
      return { tag := tag, data := data,
               note := s!"{msg} — errors logged by the generated theorems: {errs.take 2}",
               lines := #[] }

/-- The log of an outcome. -/
def logOutcome (o : Tools.ShippingLeafEntryCommand.Outcome) (f : Name) : CommandElabM Unit := do
  logInfo m!"LEAFDESIGN DATA {o.data}"
  for l in o.lines do logInfo m!"{l}"
  logInfo m!"LEAFDESIGN {o.tag} {f}: {o.note}"

/-- `#machine_leaf_design f`: an error where it is refused or fails. -/
elab "#machine_leaf_design " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← leafDesign f
  if o.tag == "REFUSED" || o.tag == "FAILED" then
    logInfo m!"LEAFDESIGN DATA {o.data}"
    throwError "LEAFDESIGN {o.tag} {f}: {o.note}"
  else
    logOutcome o f

/-- `#machine_leaf_design_try f "EXPECTED"`: the outcome is LOGGED
(`LEAFDESIGN DATA …`, then `LEAFDESIGN GENERATED | REBUILT | REFUSED |
FAILED f: …`), and it is an error when its class is not the expected one. -/
elab "#machine_leaf_design_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← leafDesign f
  logOutcome o f
  unless o.tag == e.getString do
    throwError "LEAFDESIGN {f}: expected {e.getString}, found {o.tag}"

/-- The audit of a generated `f.machine_design_leaf0`: the base endpoint
`f.machine_ships_wired` mentions the three check constants and asks
`MachineCloses`; the design-level endpoint mentions none of `forbiddenAll`
(the leaf-entry command's constants and the parents' seven checkers), has
exactly two proposition binders (the run, `MachineDefines f`) and exactly
one antecedent under `∃ raw` (`ChildBnd`), 0 NOT ALLOWED, concludes in
`DesignSV` over `childMap`; standard axioms. The listing is LOGGED before the
assertions (`checkStatementWith` builds it, then asserts). -/
def audit (f : Name) : MetaM Unit := do
  let leaf := f ++ `machine_design_leaf0
  let base := f ++ `machine_ships_wired
  let info ← getConstInfo leaf
  let binfo ← getConstInfo base
  let mentions (t : Lean.Expr) (n : Name) : Bool := (t.find? (·.isConstOf n)).isSome
  let inBase : List Name := Tools.ShippingLeafEntryCommand.checkConsts.filter (mentions binfo.type)
  let inLeaf : List Name := forbiddenAll.filter (mentions info.type)
  let baseCloses : Bool := mentions binfo.type ``Tools.ShippingMachineEntry.MachineCloses
  let shipsInLeaf : Bool := mentions info.type ``Tools.ShippingMachineShipping.MachineShips
  logInfo m!"LEAFDESIGN AUDIT {f}: of {Tools.ShippingLeafEntryCommand.checkConsts} — in {base}: {inBase} (MachineCloses there: {baseCloses}); of {forbiddenAll} — in {leaf}: {inLeaf}; MachineShips in {leaf}: {shipsInLeaf}"
  -- the listing first: built without the assertions
  let listing ← forallTelescope info.type fun xs body => do
    let mut lines : Array String := #[]
    for x in xs do
      let t0 ← inferType x
      let t ← instantiateMVars t0
      let isP ← isProp t
      if isP then
        let pp ← ppExpr t
        let nm ← x.fvarId!.getUserName
        let word : String :=
          if Tools.ShippingFinalGoalCommand.allowed t then "ALLOWED    " else "NOT ALLOWED"
        lines := lines.push s!"LEAFDESIGN AUDIT PREMISE {leaf}: {word} binder {nm} : {pp}"
    let inn ← inner body 0
    for a in inn.antes do
      let word : String := if a.ok then "ALLOWED    " else "NOT ALLOWED"
      lines := lines.push
        s!"LEAFDESIGN AUDIT PREMISE {leaf}: {word} antecedent under the existential : {a.text}"
    lines := lines.push s!"LEAFDESIGN AUDIT CONCLUSION {leaf}: {inn.concl}"
    return lines
  for l in listing do logInfo m!"{l}"
  unless inBase.length == 3 do
    throwError "{base}: expected to mention the three check constants, mentions {inBase}"
  unless baseCloses do
    throwError "{base}: expected to ask MachineCloses"
  discard <| checkStatementWith "LEAFDESIGN AUDIT CHECK" f leaf info.type
  for n in [leaf, f ++ `machine_leafKid, f ++ `machine_closes,
      ``Tools.ShippingLeafDesign.leaf_entry_design0_of_wired,
      ``Tools.ShippingLeafDesign.leaf_design0_of_checks,
      ``Tools.ShippingLeafDesign.leaf_design_of_ships,
      ``Tools.ShippingLeafDesign.designSV0_leaf_unique,
      ``Tools.ShippingGuardsLeaf.leaf_entry_textChecks_closed,
      ``Tools.ShippingGuardsLeaf.leaf_entry_shipped_seq_closed,
      ``Tools.ShippingLeafEntry.designSV0_of_leaf] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"LEAFDESIGN AUDIT OK {leaf}: exactly two proposition binders (the run, MachineDefines {f}) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none of {forbiddenAll}; conclusion DesignSV (childMap design.modules) 0 (checkedOptimize b) — a closed run showing the source exists, and every closed run shows it; standard axioms (also {f}.machine_leafKid, {f}.machine_closes, leaf_entry_design0_of_wired, leaf_design0_of_checks, leaf_design_of_ships, designSV0_leaf_unique, leaf_entry_textChecks_closed, leaf_entry_shipped_seq_closed, designSV0_of_leaf). SCOPE: one declaration as an entry, depth 0, no call; data conditions decided for {f}; the run, the reflection and ChildBnd stay premises; a compiler with the two guards of Sparkle/IR/RefineCheck.lean; DesignSV of the module list over the returned design's child map — not the SV string, not #sim"

/-- The command over a list of names: one `LEAFDESIGN DATA` and one outcome
line per name, then one `LEAFDESIGN SWEEP` line with the classes. Nothing is
asserted. (Not run by any test of this round.) -/
def sweep (names : List Name) : CommandElabM Unit := do
  let mut genL : List Name := []
  let mut rebL : List Name := []
  let mut refused : List Name := []
  let mut failed : List Name := []
  for f in names do
    let o ← leafDesign f
    logInfo m!"LEAFDESIGN DATA {o.data}"
    logInfo m!"LEAFDESIGN {o.tag} {f}: {o.note}"
    if o.tag == "GENERATED" then genL := genL ++ [f]
    else if o.tag == "REBUILT" then rebL := rebL ++ [f]
    else if o.tag == "REFUSED" then refused := refused ++ [f]
    else failed := failed ++ [f]
  logInfo m!"LEAFDESIGN SWEEP of {names.length}: GENERATED {genL.length} {genL}; REBUILT {rebL.length} {rebL}; REFUSED {refused.length} {refused}; FAILED {failed.length} {failed}"

end Tools.ShippingLeafDesignCommand
