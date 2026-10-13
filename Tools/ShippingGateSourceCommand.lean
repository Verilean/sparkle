import Lean.Elab.Command
import Tools.ShippingGateSource
import Tools.ShippingGateDesignCommand

/-! # `#gate_design0S f` and `#gate_source_sweep f`: a gate-route entry at the design level with the source on Signals (round par/b-36)

WRITTEN, NOT BUILT. `#gate_design0` and `f.gate_design0` (BUILT at
0a0a4f71) are NOT changed.

## What is generated

For a declaration `f` in the scope of `#gate_child` (its gate data is
generated when missing):

    f.gate_pointwise :
      ∀ i bools bits (t : Nat),
        (f.machineSource i bools bits).map (fun g => g t) =
          [(pack f.gateSort (eval (fun j => (bools (f.gateBpos.getD j 0)).val t)
                                  (fun j w => (bits (f.gateVpos.getD j 0) w).val t)
                                  f.gateTerm)).toNat]
      := fun i bools bits t => Eq.refl _            -- checked by the KERNEL

"the source's one observation at time `t` is the reflected term's value on
the inputs' values at time `t`". The statement is elaborated from syntax
(the binder types come from `f.machineSource`'s own type); the proof is
`Eq.refl` of the left side under the binders, added with `addDecl` — the
kernel decides it, the elaborator's `isDefEq` is not asked (the way
`Tools.ShippingMachineCommand.reflProof` proves `f.machine_result`, the
same equation in the machine route's vocabulary). It is about the source
function and the reflected term only: no module, no run, no check.

    f.gate_design0S :
      ∀ {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) … (b, design) w')
        (entry : EntryDefines mctx mref cctx cref f f.gateValue),
        ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          ∃ ids, ids.Nodup ∧ ids.length = f.gateBinders.length ∧ ∃ cache,
            ∀ i bools bits T ins st0 mems kids,
              (∀ t st, t < T → SourceInputs f f.gateBinders ids cache
                 (fun j => (bools j).val (T-1-t)) (fun j n => (bits j n).val (T-1-t))
                 (seedR b ins t st)) →
              (inputs within the declared widths) → (… the emitted widths) → Bounded … st0 →
              (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) T
                  ⟨st0, mems, kids⟩ envsO ∧ envsO.length = T ∧
                ∀ j hj k f', (f.machineSource i bools bits)[k]? = some f' → envsO[j] "out" = f' j)
              ∧ ∀ envs', DesignSV … envs' → (the same about envs')

    := fun hr entry => Tools.ShippingGateSource.gate_entry_design0S hr entry
         f.gate_old f.gate_peel f.gate_wf
         (bool_positions (by decide)) (bits_positions (by decide)) f.gate_pointwise

The statement is NOT written here a second time: the proof term is
elaborated and the theorem's statement is the term's inferred type. It is
then checked (`Tools.ShippingGateDesignCommand.checkStatement`: exactly the
run and `EntryDefines f f.gateValue` as proposition binders, one
existential in front of the conjunction, no antecedent that is not
ALLOWED — there is none —, `DesignSV` over `childMap`, none of
`forbiddenAll` nor `forwardCheck`) and, in addition, must mention
`SourceInputs` and `f.machineSource` and must NOT mention `childValue` or
`InRange` (the value-level form's constants).

## Sweep

`#gate_source_sweep f` (START line on stderr and in the log; generator;
audit on the stored statement; gap tool; RESULT line; never an error),
`#gate_source_sweep_summary` (error only on an inconsistency of what the
file measured), `#gate_source_sweep_expect f "CLASS" ["reason"]`.

Classes: `GENERATED`, `EXISTS`, `REFUSED` (outside the gate's scope:
`#gate_child`'s reason), `FAILED` (with the step: `gate_pointwise` — the
kernel refuses the `rfl`; or the endpoint), `UNRESOLVED`.

SCOPE of a GENERATED row: ONE gate-route declaration as an entry, depth 0,
no call, no register, one output `out`; the run and `EntryDefines f
f.gateValue` are premises; the source on Signals under `SourceInputs`;
`DesignSV` of the module list over the returned design's child map — not
the SV string, not `#sim`; seeding `seedR` (`rst` low). -/
namespace Tools.ShippingGateSourceCommand
open Lean Meta Elab Command

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

private def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- **`f.gate_pointwise`, generated** (file header; returned unchanged when
it exists). The statement from syntax, the proof `Eq.refl` of the left side,
checked by the kernel. -/
def pointwiseTheorem (f : Name) : CommandElabM Name := do
  let name := f ++ `gate_pointwise
  if (← getEnv).contains name then return name
  let n (s : String) : Ident := mkIdent (`_root_ ++ f ++ Name.mkSimple s)
  let stx ← `(∀ i bools bits (t : Nat),
    List.map (fun g => g t) ($(n "machineSource") i bools bits) =
      [Tools.ShippingUnifiedMeaning.Value.toNat
        (Tools.ShippingUnifiedMeaning.pack $(n "gateSort")
          (Tools.ShippingUnifiedSource.eval
            (fun j => Sparkle.Core.Signal.Signal.val (bools (List.getD $(n "gateBpos") j 0)) t)
            (fun j w => Sparkle.Core.Signal.Signal.val (bits (List.getD $(n "gateVpos") j 0) w) t)
            $(n "gateTerm")))])
  liftTermElabM <| withOptions (fun o => Lean.Elab.async.set o false) do
    let ty ← Term.elabType stx
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    if ty.hasMVar then
      throwError "{name}: the statement has an unassigned metavariable:{indentExpr ty}"
    let proof ← Tools.ShippingMachineCommand.reflProof ty true
    try
      addDecl (.thmDecl { name, levelParams := [], type := ty, value := proof })
    catch ex =>
      throwError "{name}: gate_pointwise is not checked by the kernel (the source's observation at time t is not, by reduction, the term's value on the inputs' values at t): {ex.toMessageData}"
    stdAxioms name
  return name

/-- The statement and the proof of `f.gate_design0S` (file header). Nothing
is added to the environment. -/
def endpointTerm (f : Name) : TermElabM (Lean.Expr × Lean.Expr) := do
  let n (s : String) : Ident := mkIdent (`_root_ ++ f ++ Name.mkSimple s)
  let cq : Lean.Term := Lean.Quote.quote f
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational $cq) mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
        $(n "gateValue")) =>
    Tools.ShippingGateSource.gate_entry_design0S hr entry
      $(n "gate_old") $(n "gate_peel") $(n "gate_wf")
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide))
      $(n "gate_pointwise"))
  let v ← Term.elabTermAndSynthesize stx none
  let value ← instantiateMVars v
  if value.hasMVar then
    throwError "{f}: the proof term of gate_design0S has an unassigned metavariable"
  let type ← instantiateMVars (← inferType value)
  if type.hasMVar then
    throwError "{f}: the statement of gate_design0S has an unassigned metavariable"
  return (type, value)

/-- The checks of the statement of `f.gate_design0S`: the gate design
endpoint's, and the Signal-level source form. Returns the premise lines. -/
def checkStatementS (tag : String) (f leaf : Name) (type : Lean.Expr) :
    MetaM (Array String) := do
  let lines ← Tools.ShippingGateDesignCommand.checkStatement tag f leaf type
  let mentions (c : Name) : Bool := (type.find? (·.isConstOf c)).isSome
  for c in [``Tools.ShippingMixedSourceBridge.SourceInputs, f ++ `machineSource] do
    unless mentions c do
      throwError "{leaf}: the statement does not mention {c}"
  for c in [``Tools.ShippingMachineChild.childValue, ``Tools.ShippingMachineChild.InRange] do
    if mentions c then
      throwError "{leaf}: the statement mentions {c} (the value-level form)"
  return lines

/-- `f.gate_design0S`, added. Throws when the data is not derivable, a
generated proof fails or a statement check fails. Returns the premise
lines. -/
def gateDesign0SCore (f : Name) : CommandElabM (Array String) := do
  let name := f ++ `gate_design0S
  unless (← getEnv).contains (f ++ `gate_child) do
    discard <| Tools.ShippingGateChildCommand.generateGateChild f
  for s in Tools.ShippingGateDesignCommand.dataNames ++ ["gateSort", "gateTerm", "gateBpos", "gateVpos"] do
    let d := f ++ Name.mkSimple s
    unless (← getEnv).contains d do
      throwError "{f}: {d} is not in the environment after #gate_child"
  discard <| pointwiseTheorem f
  liftTermElabM <| withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 100000) do
    let (type, value) ← endpointTerm f
    let lines ← checkStatementS "GATEDESIGN0S" f name type
    Tools.ShippingMachineLinkedCommand.addTheorem name type value
    return lines

/-- The outcome of the generator on one declaration. -/
structure Outcome where
  /-- `GENERATED`, `EXISTS`, `REFUSED` or `FAILED` -/
  tag : String
  note : String
  lines : Array String

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def gateDesign0S (f : Name) : CommandElabM Outcome := do
  let name := f ++ `gate_design0S
  if (← getEnv).contains name then
    return { tag := "EXISTS",
             note := s!"{name} is in the environment already: audited, not rebuilt",
             lines := #[] }
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    let lines ← gateDesign0SCore f
    return { tag := "GENERATED",
             note := s!"GENERATED {name}. Tools.ShippingGateSource.gate_entry_design0S at {f}'s gate data ({f}.gate_old, {f}.gate_peel, {f}.gate_wf; two decide on the binder positions) and {f}.gate_pointwise (the source's observation at time t is the term's value on the inputs' values at t: Eq.refl, checked by the kernel). Premises: the run and EntryDefines {f} {f}.gateValue (binders) — no antecedent under ∃ raw, no ChildBnd, no check constant; the source on Signals under SourceInputs, on the port out",
             lines }
  catch ex =>
    let msg ← ex.toMessageData.toString
    let newMsgs := (← get).messages.toList.drop savedMsgs.toList.length
    let errs ← (newMsgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    let refused : Bool := Tools.ShippingGateDesignCommand.scopeReasons.any fun r => has msg r
    let tag : String := if refused then "REFUSED" else "FAILED"
    return { tag,
             note := s!"{msg} — errors logged by the generated theorems: {errs.take 2}",
             lines := #[] }

/-- `#gate_design0S f`: an error where it is refused or fails. -/
elab "#gate_design0S " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← gateDesign0S f
  for l in o.lines do logInfo m!"{l}"
  if o.tag == "REFUSED" || o.tag == "FAILED" then
    throwError "GATEDESIGN0S {o.tag} {f}: {o.note}"
  else
    logInfo m!"GATEDESIGN0S {o.tag} {f}: {o.note}"

/-- The general theorems under a Signal-level gate design endpoint. -/
def generalTheorems : List Name :=
  [``Tools.ShippingGateSource.gate_entry_design0S,
   ``Tools.ShippingGateSource.text_run_of_steps,
   ``Tools.ShippingGateSource.post_eval,
   ``Tools.ShippingGateDesign.gate_entry_text,
   ``Tools.ShippingGateDesign.runModule_assigns_total,
   ``Tools.ShippingGateChild.gate_core_facts]

/-- The audit of an existing `f.gate_design0S` (throws on a violation): the
statement checks on the STORED statement; `f.gate_pointwise` is a theorem
whose statement mentions `f.machineSource` and `f.gateTerm`; standard
axioms. Returns the premise lines. -/
def audit (f : Name) : MetaM (Array String) := do
  let leaf := f ++ `gate_design0S
  let info ← getConstInfo leaf
  let lines ← checkStatementS "GATEDESIGN0S AUDIT" f leaf info.type
  let pw ← getConstInfo (f ++ `gate_pointwise)
  for c in [f ++ `machineSource, f ++ `gateTerm] do
    unless (pw.type.find? (·.isConstOf c)).isSome do
      throwError "{f ++ `gate_pointwise}: its statement does not mention {c}"
  for n in [leaf, f ++ `gate_pointwise, f ++ `gate_old, f ++ `gate_peel, f ++ `gate_wf]
      ++ generalTheorems do
    stdAxioms n
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

/-- `#gate_source_sweep f`: the generator, its audit and the gap tool;
LOGGED, never an error. -/
elab "#gate_source_sweep " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"GATESOURCE START {shown}"
  logInfo m!"GATESOURCE START {shown}"
  let t0 ← IO.monoMsNow
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"GATESOURCE RESULT {shown}: UNRESOLVED — the identifier is not a constant of the imports"
    rows.modify fun a => a.push
      { decl := shown, tag := "UNRESOLVED", note := "the identifier does not resolve", audit := "-",
        gap := "-", listed := 0, bad := 0, left := false, ms := 0 }
  | some f =>
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    let o : Outcome ← try
        gateDesign0S f
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv savedEnv
        modify fun st => { st with messages := savedMsgs }
        pure { tag := "FAILED", note := s!"the generator threw outside its own handler: {msg}",
               lines := #[] }
    for l in o.lines do logInfo m!"{l}"
    logInfo m!"GATEDESIGN0S {o.tag} {f}: {o.note}"
    let made : Bool := o.tag == "GENERATED" || o.tag == "EXISTS"
    let leaf := f ++ `gate_design0S
    let envA ← getEnv
    let auditR : String × Array String ← try
        if made then
          let ls ← liftTermElabM (audit f)
          for l in ls do logInfo m!"{l}"
          pure ("OK", ls)
        else
          pure ("-", #[])
      catch ex =>
        let msg ← ex.toMessageData.toString
        setEnv envA
        pure (s!"FAILED: {msg}", #[])
    let auditS : String := auditR.1
    let prem := auditR.2.filter fun l => has l " PREMISE "
    let bad := (prem.filter fun l => has l "NOT ALLOWED").size
    let gapName : Name := f ++ `gate_design0S_gap
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
      logInfo m!"GATESOURCE RESULT {f}: {o.tag}; premise lines listed by the audit {prem.size}, NOT ALLOWED {bad}; audit {clip auditS 400}; {clip gapS 400}; {leaf} in the environment: {left}; {ms} ms. SCOPE of this line: ONE gate-route declaration as an entry, depth 0, no call, no register, one output out; the run and EntryDefines {f} {f}.gateValue stay premises; the source on Signals ({f}.machineSource under SourceInputs); DesignSV of the module list over the returned design's child map — not the SV string, not #sim"
    else
      logInfo m!"GATESOURCE RESULT {f}: {o.tag} — {clip o.note 600}; {leaf} in the environment: {left}; {ms} ms"
    rows.modify fun a => a.push
      { decl := toString f, tag := o.tag, note := o.note, audit := auditS, gap := gapS,
        listed := prem.size, bad, left, ms }

/-- `#gate_source_sweep_summary`: the rows and the counts; an error only on
an inconsistency of what this file measured. -/
elab "#gate_source_sweep_summary" : command => do
  let rs ← rows.get
  let mut lines : Array String := #[]
  let mut problems : Array String := #[]
  for r in rs do
    let made : Bool := r.tag == "GENERATED" || r.tag == "EXISTS"
    if made then
      lines := lines.push s!"GATESOURCE ROW {r.decl}: {r.tag}; listed {r.listed}, NOT ALLOWED {r.bad}; audit {clip r.audit 160}; {clip r.gap 160}; {r.ms} ms"
      unless r.audit == "OK" do
        problems := problems.push s!"{r.decl}: {r.tag} but its audit did not pass ({clip r.audit 300})"
      unless r.bad == 0 do
        problems := problems.push s!"{r.decl}: {r.tag} with {r.bad} NOT ALLOWED lines in the audit's listing"
      unless r.left do
        problems := problems.push s!"{r.decl}: {r.tag} but gate_design0S is not in the environment"
    else
      lines := lines.push s!"GATESOURCE ROW {r.decl}: {r.tag} — {clip r.note 240}; {r.ms} ms"
      if r.left then
        problems := problems.push s!"{r.decl}: {r.tag} but gate_design0S is in the environment"
  let count (t : String) : Nat := (rs.filter fun r => r.tag == t).size
  let namesOf (t : String) : List String := (rs.filter fun r => r.tag == t).toList.map (·.decl)
  logInfo m!"{String.intercalate "\n" lines.toList}"
  logInfo m!"GATESOURCE SUMMARY of {rs.size}: GENERATED {count "GENERATED"} {namesOf "GENERATED"}; EXISTS {count "EXISTS"} {namesOf "EXISTS"}; REFUSED {count "REFUSED"} {namesOf "REFUSED"}; FAILED {count "FAILED"} {namesOf "FAILED"}; UNRESOLVED {count "UNRESOLVED"} {namesOf "UNRESOLVED"}. Each GENERATED / EXISTS row: its audit passed and its listing has 0 NOT ALLOWED (asserted below). No class and no count was expected by this command. A GENERATED row is about ONE gate-route declaration as an entry at depth 0 — DesignSV of the module list, with the run and the reflection as premises, the source on Signals; not the SV string, not #sim, not any other declaration."
  if rs.isEmpty then
    throwError "GATESOURCE: nothing was swept in this file"
  unless problems.isEmpty do
    throwError "GATESOURCE: {problems.size} inconsistencies in what was measured:\n{String.intercalate "\n" problems.toList}"

/-- `#gate_source_sweep_expect f "CLASS" ["reason"]`: the class of `f` in
this file is `CLASS` (and its note contains the reason, when given). -/
elab "#gate_source_sweep_expect " d:ident e:str r:(str)? : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let want : String := e.getString
  let rs ← rows.get
  let mine := (rs.filter fun x => x.decl == toString f).toList.reverse
  let row ← match mine with
    | x :: _ => pure x
    | [] => throwError "GATESOURCE EXPECT {f}: not swept in this file (no #gate_source_sweep {f} before this line)"
  unless row.tag == want do
    throwError "GATESOURCE EXPECT {f}: expected {want}, now {row.tag} — {row.note}"
  if want == "GENERATED" || want == "EXISTS" then
    unless row.audit == "OK" do
      throwError "GATESOURCE EXPECT {f}: {row.tag}, but its audit did not pass: {row.audit}"
    unless row.bad == 0 do
      throwError "GATESOURCE EXPECT {f}: {row.tag}, with {row.bad} NOT ALLOWED lines"
    unless (← getEnv).contains (f ++ `gate_design0S) do
      throwError "GATESOURCE EXPECT {f}: {row.tag}, but {f ++ `gate_design0S} is not in the environment"
  match r with
  | some s =>
    let sub : String := s.getString
    unless (row.note.splitOn sub).length > 1 do
      throwError "GATESOURCE EXPECT {f}: {row.tag}, but its reason does not contain \"{sub}\": {row.note}"
  | none => pure ()
  logInfo m!"GATESOURCE EXPECT {f}: {row.tag}, as expected"

end Tools.ShippingGateSourceCommand
