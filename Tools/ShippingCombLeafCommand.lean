import Lean.Elab.Command
import Tools.ShippingCombLeafDesign
import Tools.ShippingLeafDesignCommand
import Tools.ShippingControlOptSoundness

/-! # `#machine_comb_design f` and `#comb_sweep f`: a SLOTLESS leaf as an entry at the design level — the OPEN endpoint, and the measurement of what keeps it open (round par/b-32)

WRITTEN, NOT BUILT. The register leaves' command `#machine_leaf_design` and
what it generates are NOT changed.

## What is generated

For a machine-route declaration `f` without calls and WITHOUT a register
slot, with the one output `out`, whose `f.machine_ships_comb` exists
(untransported):

    f.machine_combKid : Tools.ShippingCombLeafDesign.CombKid ``f f.machineData
        -- the decided data conditions (no reflection, no closing inside)
    f.machine_design_comb0_open :
      ∀ {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) … (b, design) w')
        (entry : MachineDefines … f f.machineData.shape),
        ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          (ChildBnd mref cref w →
           simpleBody b = true →                                          -- (S1) OPEN
           (checkedOptimize b = b ∨ printOk (checkedOptimize b) = true) →  -- (S2) OPEN
           … DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) … )

    := fun hr entry =>
         Tools.ShippingCombLeafDesign.comb_entry_design0_out f.machineData soundL
           f.machine_combKid hr entry (f.machine_closes mctx mref cctx cref)

`soundL` is the wired trace term inside `f.machine_ships_comb`'s proof (its
seventh argument), reused as it is.

The name says what it is: `_open`. It is NOT `f.machine_design_leaf0`: two
antecedents under the existential are NOT ALLOWED by the goal's classifier
(`Tools.ShippingFinalGoalCommand.allowed`), and the generator's own check
ASSERTS that there are exactly those two — a statement with any other
premise is not added.

## What is measured (`#comb_sweep`)

(S1) and (S2) are Boolean facts about the module a run returns. For a
declaration the sweep runs the REAL entry (`synthesizeCombinational f`, by
the compiler, in this process) and logs, on the module `b` it returned and
on `checkedOptimize b`:

    simpleBody b            -- (S1)
    checkedOptimize b == b  -- the first disjunct of (S2)
    printOk (checkedOptimize b)   -- the second
    printOk b, PrintCheck.moduleCheck b
    a slice / concatenation / NOT assignment in b (`isCastExpr`),
    a comparison assignment (`isControlExpr`)    -- when one of them and (S1):
                                                 -- `checkedOptimize b = b` is a BUILT theorem
    the statements' kinds, the output names, the number of design modules

That is an EVALUATION on one run — evidence about which missing theorem a
declaration needs, not a proof of (S1) / (S2) for every run.

## Refusals (the scan of `#machine_leaf_design`, then this command's own)

| condition | reason |
|---|---|
| the machine reader refuses `f` | not a machine declaration (a gate-route / legacy declaration has other endpoints) |
| call entries | memory / has calls — a parent |
| a register slot | a register leaf: `#machine_leaf_design` |
| no `f.machineData / machine_ok / machine_body` | no machine endpoint |
| no `f.machine_ships_comb` | the head of `f.machine_sound` is not `machine_trace_of_comb`, or its generation failed |
| output names other than `["out"]` | (S3): the text of the merged module is derived only for the one output `out` |
| `f.machine_ships_comb` not `machine_ships_comb` on 11 arguments | a transported endpoint (under `Eq.mpr`): not handled |
| `f.machine_closes` not derivable | `MachineCloses` is not derived from the data |

`#comb_sweep f` is an error in no case. `#comb_sweep_summary` is an error
only on an inconsistency of what the file measured (a GENERATED row whose
theorem is absent or whose statement check did not count exactly the two
open obligations; another row that left the theorem behind; nothing swept). -/
namespace Tools.ShippingCombLeafCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- **`c.machine_combKid`, generated**: the decided data conditions of the
slotless leaf `c` (returned unchanged when it exists). -/
def combKidTheorem (c : Name) : CommandElabM Name := do
  let name := c ++ `machine_combKid
  if (← getEnv).contains name then return name
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := nm c "machineData"
  let cq : Term := quote c
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) :
        Tools.ShippingCombLeafDesign.CombKid $cq $data :=
      { ok := $(nm c "machine_ok")
        body := $(nm c "machine_body")
        calls := by decide
        dom := by decide
        leaf := by first | rfl | decide
        slots := by first | rfl | decide
        ss := by decide
        outTy := by decide
        one := by decide
        outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
              Sparkle.IR.NameHints.charOk c = true from by
            first | decide | decide +kernel) o ho)
        outScalar := by decide }))
  checkMade name before
  return name

/-- What the statement of an open endpoint must not mention: the parents'
checker constants, the two text checks of `machine_ships_comb`, the closing,
and the world invariant. (`simpleBody` and `printOk` ARE mentioned: they are
the two open obligations.) -/
def forbiddenOpen : List Name :=
  Tools.ShippingLeafDesignCommand.checkers ++
    [``Tools.SVParser.EmitSem.seqCheck, ``Tools.ShippingSeqSVSoundness.seqNames,
     ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildInv.InvW]

/-- The statement checks of `f.machine_design_comb0_open`; the premise lines
and the number of NOT ALLOWED ones. Throws unless: no forbidden constant;
exactly two proposition binders (the run, `MachineDefines f`), both allowed;
one existential in front; exactly THREE antecedents under it — `ChildBnd`
(allowed), one mentioning `simpleBody` and one mentioning `printOk` (the two
open obligations, NOT ALLOWED); the conclusion about `DesignSV` over
`childMap`. -/
def checkOpen (f name : Name) (type : Lean.Expr) : MetaM (Array String × Nat) := do
  for c in forbiddenOpen do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: the statement mentions {c}"
  forallTelescope type fun xs body => do
    let mut lines : Array String := #[]
    let mut badB : Nat := 0
    let mut runs : Nat := 0
    let mut defs : Nat := 0
    let mut props : Nat := 0
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        props := props + 1
        let pp ← ppExpr t
        let xn ← x.fvarId!.getUserName
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then runs := runs + 1
        if t.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
          if ← isDefEq (t.getArg! 4) (toExpr f) then defs := defs + 1
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"COMBDESIGN PREMISE {name}: ALLOWED     binder {xn} : {pp}"
        else
          badB := badB + 1
          lines := lines.push s!"COMBDESIGN PREMISE {name}: NOT ALLOWED binder {xn} : {pp}"
    let inn ← Tools.ShippingLeafDesignCommand.inner body 0
    let mut bnd : Nat := 0
    let mut s1 : Nat := 0
    let mut s2 : Nat := 0
    let mut other : Nat := 0
    for a in inn.antes do
      if a.ok then
        lines := lines.push
          s!"COMBDESIGN PREMISE {name}: ALLOWED     antecedent under the existential : {a.text}"
        if a.isBnd then bnd := bnd + 1 else other := other + 1
      else
        let which : String :=
          if has a.text "simpleBody" then "(S1) " else if has a.text "printOk" then "(S2) " else ""
        lines := lines.push
          s!"COMBDESIGN PREMISE {name}: NOT ALLOWED (OPEN) {which}antecedent under the existential : {a.text}"
        if has a.text "simpleBody" then s1 := s1 + 1
        else if has a.text "printOk" then s2 := s2 + 1
        else other := other + 1
    lines := lines.push s!"COMBDESIGN CONCLUSION {name}: {inn.concl}"
    unless badB == 0 && props == 2 && runs == 1 && defs == 1 do
      throwError "{name}: {props} proposition binders (RunsTo {runs}, MachineDefines {f} {defs}, NOT ALLOWED {badB}), expected exactly the run and MachineDefines {f}"
    unless inn.nEx == 1 do
      throwError "{name}: {inn.nEx} existentials in front of the conjunction, expected 1 (raw)"
    unless bnd == 1 && s1 == 1 && s2 == 1 && other == 0 do
      throwError "{name}: antecedents under the existential: ChildBnd {bnd}, (S1) simpleBody {s1}, (S2) printOk {s2}, other {other} — expected 1, 1, 1, 0: {lines}"
    unless inn.hasDesign && inn.hasChildMap do
      throwError "{name}: the conclusion does not mention DesignSV over childMap"
    return (lines, s1 + s2)

/-- The statement and the proof of `f.machine_design_comb0_open` (file
header). Nothing is added to the environment. -/
def endpointTerm (f cl kid : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let comb := f ++ `machine_ships_comb
  let some (.thmInfo ti) := (← getEnv).find? comb
    | throwError "{comb}: not a theorem"
  let v := ti.value
  unless v.isAppOfArity ``Tools.ShippingMachineShipsComb.machine_ships_comb 11 do
    throwError "{comb}: not machine_ships_comb on 11 arguments (a transported endpoint — under Eq.mpr — or another construction): not handled"
  let a := v.getAppArgs
  let d := a[1]!
  let soundL := a[6]!
  let value ← forallTelescopeReducing ti.type fun xs _ => do
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
    let closes := mkAppN (mkConst cl) #[xs[0]!, xs[1]!, xs[2]!, xs[3]!]
    let closesT ← inferType closes
    unless ← isDefEq closesT tCl do
      throwError "{cl}: its statement at the contexts is not the MachineCloses binder of {comb}:{indentExpr closesT}\nagainst{indentExpr tCl}"
    let body ← mkAppM ``Tools.ShippingCombLeafDesign.comb_entry_design0_out
      #[d, soundL, mkConst kid, xs[8]!, xs[9]!, closes]
    mkLambdaFVars ((xs.extract 0 8) ++ #[xs[8]!, xs[9]!]) body
  let value ← instantiateMVars value
  if value.hasMVar then
    throwError "{f}: the proof term of machine_design_comb0_open has an unassigned metavariable"
  let type ← instantiateMVars (← inferType value)
  if type.hasMVar then
    throwError "{f}: the statement of machine_design_comb0_open has an unassigned metavariable"
  return (type, value)

/-- The outcome of the generator on one declaration. -/
structure Outcome where
  /-- `GENERATED`, `REBUILT`, `REFUSED` or `FAILED` -/
  tag : String
  data : String
  note : String
  lines : Array String
  /-- the NOT ALLOWED (open) antecedents counted in the added statement -/
  nOpen : Nat

/-- The scope scan: the reader's data line and, outside the scope, the
reason. Adds nothing, never throws. -/
def scan (f : Name) : CommandElabM (String × Option String) := do
  let s ← Tools.ShippingLeafEntryCommand.scan f
  let env ← getEnv
  match s.refusal with
  | none =>
    return (s.data, some "a register leaf (a slot, no call, f.machine_ships_wired): in the scope of #machine_leaf_design, not of this command")
  | some r =>
    unless r.startsWith "slotless" do return (s.data, some r)
    for x in [`machineData, `machine_ok, `machine_body] do
      unless env.contains (f ++ x) do
        return (s.data, some s!"no machine endpoint: {f ++ x} is not in the environment (#machine_endpoint was not run on {f}, or its file is not imported)")
    unless env.contains (f ++ `machine_ships_comb) do
      return (s.data, some s!"no {f}.machine_ships_comb (the head of {f}.machine_sound is not machine_trace_of_comb, or the generation of the combinational ship-level endpoint failed): nothing to carry to the design level")
    let outs? : Option (List String) ← try
        let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
        pure (some (r.shape.layout.outs.map (·.name)))
      catch _ => pure none
    match outs? with
    | some outs =>
      unless outs == ["out"] do
        return (s.data, some s!"(S3) the output names are {outs}, not [out]: the text of the merged module is derived only for the one output `out` (Tools.ShippingCombKidText.mergeChecked_text_out; docs/parallel/A-comb-kids.md 2.3 for several outputs)")
    | none => return (s.data, some "the machine reader refuses it")
    return (s.data, none)

/-- After the scan: the closing, `CombKid`, the open endpoint (added, or
rebuilt and compared). -/
def combDesignCore (f : Name) : CommandElabM (Bool × String × Array String × Nat) := do
  let name := f ++ `machine_design_comb0_open
  let was : Bool := (← getEnv).contains name
  let cl ← liftTermElabM do
    let some n ← Tools.ShippingMachineClosesGen.closesTheorem? f
      | throwError "{f}: MachineCloses is not derived from the data (closesTheorem?): {f}.machine_closes is neither there nor generated"
    pure n
  let kid ← noAsync (combKidTheorem f)
  let res ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ← endpointTerm f cl kid
      let (lines, nOpen) ← checkOpen f name type
      let (made, line) ← Tools.ShippingNoPortsKidsCommand.addOrCompare name type value
      for n in [made, kid, cl] do
        for ax in ← Lean.collectAxioms n do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "{n} uses a non-standard axiom: {ax}"
      pure (line, lines, nOpen)
  let note : String :=
    s!"{res.1}. From {f}.machine_ships_comb's wired trace by Tools.ShippingCombLeafDesign.comb_entry_design0_out; data conditions {kid}; closing {cl}. Premises: the run, MachineDefines {f} (binders), ChildBnd (allowed antecedent) — and {res.2.2} OPEN obligations under the existential, NOT ALLOWED: (S1) simpleBody b = true, (S2) checkedOptimize b = b ∨ printOk (checkedOptimize b) = true. This is an OPEN endpoint, not a design-level endpoint of the final goal's form"
  return (was, note, res.2.1, res.2.2)

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def combDesign (f : Name) : CommandElabM Outcome := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let (data, refusal) ← scan f
  match refusal with
  | some reason => return { tag := "REFUSED", data, note := reason, lines := #[], nOpen := 0 }
  | none =>
    try
      let (existed, note, lines, nOpen) ← combDesignCore f
      let tag : String := if existed then "REBUILT" else "GENERATED"
      return { tag, data, note, lines, nOpen }
    catch ex =>
      let msg ← ex.toMessageData.toString
      let newMsgs := (← get).messages.toList.drop savedMsgs.toList.length
      let errs ← (newMsgs.filter (·.severity == .error)).mapM fun m => m.data.toString
      setEnv savedEnv
      modify fun st => { st with messages := savedMsgs }
      let refused : Bool := has msg "MachineCloses is not derived from the data" ||
        has msg "not machine_ships_comb on 11 arguments"
      let tag : String := if refused then "REFUSED" else "FAILED"
      return { tag, data,
               note := s!"{msg} — errors logged by the generated theorems: {errs.take 2}",
               lines := #[], nOpen := 0 }

/-- `#machine_comb_design f`: an error where it is refused or fails. -/
elab "#machine_comb_design " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← combDesign f
  logInfo m!"COMBDESIGN DATA {o.data}"
  for l in o.lines do logInfo m!"{l}"
  if o.tag == "REFUSED" || o.tag == "FAILED" then
    throwError "COMBDESIGN {o.tag} {f}: {o.note}"
  else
    logInfo m!"COMBDESIGN {o.tag} {f}: {o.note}"

/-! ## The measurement on the real module -/

/-- What one run of the real entry returned, as far as (S1) / (S2) go. -/
structure Measure where
  ran : Bool
  /-- (S1) -/
  simple : Bool
  /-- `checkedOptimize b == b` -/
  same : Bool
  /-- `printOk (checkedOptimize b)` -/
  printO : Bool
  /-- a slice / concatenation / NOT assignment in `b` -/
  cast : Bool
  /-- a comparison assignment in `b` -/
  control : Bool
  text : String

/-- Run the real entry on `f` and evaluate. Never throws. -/
def measure (f : Name) : CommandElabM Measure := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    let (b, design) ← liftTermElabM <| (Sparkle.Compiler.Elab.synthesizeCombinational f : MetaM _)
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let simple : Bool := Sparkle.IR.OptCheck.simpleBody b
    let same : Bool := o == b
    let printO : Bool := Sparkle.IR.PrintGuard.printOk o
    let printB : Bool := Sparkle.IR.PrintGuard.printOk b
    let uniform : Bool := Sparkle.IR.PrintCheck.moduleCheck b
    let assigns : Bool := b.body.all Sparkle.IR.RegDedup.isAssign
    let cast : Bool := b.body.any fun st => match st with
      | Sparkle.IR.AST.Stmt.assign _ e => Tools.ShippingControlOptSoundness.isCastExpr e
      | _ => false
    let control : Bool := b.body.any fun st => match st with
      | Sparkle.IR.AST.Stmt.assign _ e => Tools.ShippingControlOptSoundness.isControlExpr e
      | _ => false
    let notSimple : Nat := (b.body.filter fun st => match st with
      | Sparkle.IR.AST.Stmt.assign _ e => !Sparkle.IR.OptCheck.simpleRhs e
      | _ => true).length
    let s2 : Bool := same || printO
    let byThm : Bool := simple && (cast || control)
    let text : String :=
      s!"statements {b.body.length} (assignments only: {assigns}; not of the simple shape: {notSimple}), inputs {b.inputs.map (·.name)}, outputs {b.outputs.map (·.name)}, design modules {design.modules.length}; (S1) simpleBody b = {simple}; (S2) checkedOptimize b == b: {same}, printOk (checkedOptimize b): {printO} — (S2) holds on this run: {s2}; printOk b: {printB}; PrintCheck.moduleCheck b (the uniform-width fragment): {uniform}; a slice / concatenation / NOT assignment in b: {cast}; a comparison assignment in b: {control}; with (S1), `checkedOptimize b = b` by the BUILT checkedOptimize_cast / _control: {byThm}"
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    return { ran := true, simple, same, printO, cast, control, text }
  catch ex =>
    let msg ← ex.toMessageData.toString
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    return { ran := false, simple := false, same := false, printO := false, cast := false,
             control := false, text := s!"the real entry threw: {msg}" }

/-- One swept declaration. -/
structure Row where
  decl : String
  tag : String
  note : String
  nOpen : Nat
  left : Bool
  ran : Bool
  simple : Bool
  s2 : Bool
  byThm : Bool
  ms : Nat

/-- The rows of the file being elaborated. -/
initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]

/-- `#comb_sweep f`: the measurement, then the generator; LOGGED, never an
error. -/
elab "#comb_sweep " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"COMBSWEEP START {shown}"
  logInfo m!"COMBSWEEP START {shown}"
  let t0 ← IO.monoMsNow
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"COMBSWEEP RESULT {shown}: UNRESOLVED — the identifier is not a constant of the imports"
    rows.modify fun a => a.push
      { decl := shown, tag := "UNRESOLVED", note := "the identifier does not resolve", nOpen := 0,
        left := false, ran := false, simple := false, s2 := false, byThm := false, ms := 0 }
  | some f =>
    let m ← measure f
    logInfo m!"COMBSWEEP MODULE {f}: {m.text}"
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    let o : Outcome ← try
        combDesign f
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv savedEnv
        modify fun st => { st with messages := savedMsgs }
        pure { tag := "FAILED", data := s!"{f}: the generator threw outside its own handler",
               note := msg, lines := #[], nOpen := 0 }
    logInfo m!"COMBDESIGN DATA {o.data}"
    for l in o.lines do logInfo m!"{l}"
    logInfo m!"COMBDESIGN {o.tag} {f}: {o.note}"
    let leaf := f ++ `machine_design_comb0_open
    let left : Bool := (← getEnv).contains leaf
    let ms := (← IO.monoMsNow) - t0
    let s2 : Bool := m.same || m.printO
    let byThm : Bool := m.simple && (m.cast || m.control)
    let made : Bool := o.tag == "GENERATED" || o.tag == "REBUILT"
    if made then
      logInfo m!"COMBSWEEP RESULT {f}: {o.tag} — the OPEN endpoint {leaf} ({o.nOpen} open obligations, NOT ALLOWED: (S1), (S2)); on the measured run (S1) = {m.simple}, (S2) = {s2}; {ms} ms. SCOPE: ONE declaration as an entry, depth 0, no call, no register, one output `out`; data conditions decided for it; the run, MachineDefines {f}, ChildBnd premises; (S1), (S2) OPEN — this is not an endpoint of the final goal's form; DesignSV of the module list, not the SV string, not #sim; the measurement is one run, not a proof"
    else
      logInfo m!"COMBSWEEP RESULT {f}: {o.tag} — {clip o.note 600}; measured run: (S1) = {m.simple}, (S2) = {s2}; {leaf} in the environment: {left}; {ms} ms"
    rows.modify fun a => a.push
      { decl := toString f, tag := o.tag, note := o.note, nOpen := o.nOpen, left, ran := m.ran,
        simple := m.simple, s2, byThm, ms }

/-- `#comb_sweep_summary`: the rows and the counts; an error only on an
inconsistency of what this file measured. -/
elab "#comb_sweep_summary" : command => do
  let rs ← rows.get
  let mut lines : Array String := #[]
  let mut problems : Array String := #[]
  for r in rs do
    let made : Bool := r.tag == "GENERATED" || r.tag == "REBUILT"
    let tail : String := if made then "" else " — " ++ clip r.note 200
    lines := lines.push s!"COMBSWEEP ROW {r.decl}: {r.tag}; open obligations in the statement {r.nOpen}; real entry ran: {r.ran}; (S1) simpleBody = {r.simple}; (S2) = {r.s2}; (S2) by a built theorem given (S1): {r.byThm}; {r.ms} ms{tail}"
    if made then
      unless r.left do
        problems := problems.push s!"{r.decl}: {r.tag} but machine_design_comb0_open is not in the environment"
      unless r.nOpen == 2 do
        problems := problems.push s!"{r.decl}: {r.tag} with {r.nOpen} open obligations counted, expected 2"
    else if r.left then
      problems := problems.push s!"{r.decl}: {r.tag} but machine_design_comb0_open is in the environment"
  let count (t : String) : Nat := (rs.filter fun r => r.tag == t).size
  let namesOf (p : Row → Bool) : List String := (rs.filter p).toList.map (·.decl)
  logInfo m!"{String.intercalate "\n" lines.toList}"
  logInfo m!"COMBSWEEP SUMMARY of {rs.size}: GENERATED (the OPEN endpoint) {count "GENERATED"}; REBUILT {count "REBUILT"}; REFUSED {count "REFUSED"} {namesOf (fun r => r.tag == "REFUSED")}; FAILED {count "FAILED"} {namesOf (fun r => r.tag == "FAILED")}; UNRESOLVED {count "UNRESOLVED"}. MEASURED on one run of the real entry each: (S1) simpleBody FALSE for {namesOf (fun r => r.ran && !r.simple)}; (S1) true and (S2) FALSE for {namesOf (fun r => r.ran && r.simple && !r.s2)}; (S1) true and (S2) not given by a built theorem for {namesOf (fun r => r.ran && r.simple && !r.byThm)}; the real entry did not run for {namesOf (fun r => !r.ran)}. No class and no count was expected by this file. A GENERATED row is an OPEN endpoint with two NOT ALLOWED obligations: NO design-level endpoint of the final goal's form exists for any of these declarations."
  if rs.isEmpty then
    throwError "COMBSWEEP: nothing was swept in this file"
  unless problems.isEmpty do
    throwError "COMBSWEEP: {problems.size} inconsistencies in what was measured:\n{String.intercalate "\n" problems.toList}"

end Tools.ShippingCombLeafCommand
