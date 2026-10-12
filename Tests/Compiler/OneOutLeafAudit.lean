import Tests.Compiler.OneOutCallerFullTest
import Tools.ShippingOneOutFullCommand
import Tools.ShippingFinalGoalCommand

/-! # The audit of a one-output endpoint whose callees are gate children and / or slotless leaf machine children (G1, round par/a-11)

Meta code only (no theorem). `audit` is the `run_cmd` body of
`Tests/Compiler/OneOutCallerLTest.lean` (BUILT) with the declaration, its
callees and the lemma names as arguments, so that the hand instances of
`callerLN` and `hftByte` and the family test of `#machine_oneout_any` run the
SAME checks:

(a) the endpoint and its closed form exist; they, `f.machine_closes_at`, the
    six per-declaration lemmas and every name in `stdNames` use the standard
    axioms only;
(b) none of the eight checker constants is written in the two statements or
    hidden in a premise's definition (`refuse`, `mentioned`, `hidden`), the
    trivially true residual is not an antecedent, and no premise of a lemma
    mentions or hides a checker;
(c) the inventory: `f.machine_design_svHR` does ask the four check premises;
(d) the COMPLETE premise lists of `f.machine_closes_at`, the open and the
    closed form are logged; class `other` must be: none (`machine_closes_at`),
    exactly the closing premise (open form), none (closed form) — throws
    otherwise;
(e) per machine callee the closed form has a `MachineDefines` binder of its
    data, per gate callee an `EntryDefines` binder; with no gate callee no
    `EntryDefines` at all;
(e') `existing := true` (the endpoint was there before the generator ran):
    the generator's own proof `f.machine_design_svH_full_gen` exists, on
    standard axioms, with a statement `isDefEq` the endpoint's, recorded as
    built from the generated lemmas;
(f) the goal gap of the closed form: generated when its theorem does not
    exist yet (throws on a premise NOT ALLOWED), else reported as existing.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutLeafAudit
open Lean Meta Elab Command

/-- Standard axioms only. -/
def std (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The audit (see the header). `tag` starts the summary line; `lemmas`: the
six per-declaration lemmas (facts, outs, portsRaw, portsShipped, hierTyped,
designFull); `scope`: the scope sentence printed with the summary. -/
def audit (tag : String) (f : Name) (machKids gateKids : List Name) (lemmas stdNames : List Name)
    (existing : Bool) (scope : String) : MetaM Unit := do
  let full := f ++ `machine_design_svH_full
  let closed := Tools.ShippingMachineClosesGen.closedName full
  let cl := f ++ `machine_closes_at
  let old := f ++ `machine_design_svHR
  unless (← getEnv).contains full do throwError "{full} was not generated"
  unless (← getEnv).contains closed do throwError "{closed} was not generated"
  -- (a) standard axioms
  for n in [full, closed, cl] ++ lemmas ++ stdNames do
    unless (← getEnv).contains n do throwError "{n}: not in the environment"
    std n
  -- (b) the eight checker constants: written, or hidden in a premise's definition
  let checkers := Tools.ShippingOneOutCommand.forbidden ++ Tools.ShippingOneOutCommand.residualOnly
  for n in [full, closed] do
    let t := (← getConstInfo n).type
    Tools.ShippingOneOutCommand.refuse n t (mkConst ``True)
    let hits := Tools.ShippingOneOutCommand.mentioned checkers t
    unless hits.isEmpty do
      throwError "{n}: the statement mentions {hits}"
    if Tools.ShippingOneOutFullCommand.trueAntecedent t then
      throwError "{n}: the trivially true residual is an antecedent"
  for n in lemmas do
    let t := (← getConstInfo n).type
    let hits ← forallTelescope t fun xs _ => do
      let mut acc : List Name := []
      for x in xs do
        let tx ← instantiateMVars (← inferType x)
        acc := acc ++ Tools.ShippingOneOutCommand.mentioned checkers tx
      return acc
    unless hits.isEmpty do
      throwError "{n}: a premise mentions {hits}"
    let hid ← Tools.ShippingOneOutCommand.hidden checkers Tools.ShippingOneOutCommand.hiddenFuel
      false false t
    unless hid.isEmpty do
      throwError "{n}: a premise hides {hid} inside a definition"
  -- (c) the inventory: the old endpoint asks the four check premises
  let oldT := (← getConstInfo old).type
  for c in [``Tools.ShippingHierPremises.shipsHierHCheck,
      ``Tools.ShippingMachineDepthH.kidsComb, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf c)).isSome do
      throwError "{old}: does not mention {c} (the inventory is wrong)"
  -- (d) the complete premise lists
  let (clLines, clOthers) ← Tests.Compiler.OneOutCallerFullTest.premiseList cl (inner := false)
  logInfo m!"{String.intercalate "\n" clLines.toList}"
  unless clOthers.isEmpty do
    throwError "{cl}: contributes premises that are not a run / a reflection / ChildBnd (NOT allowed):\n{String.intercalate "\n" (clOthers.toList.map (·.1))}"
  let (openLines, openOthers) ← Tests.Compiler.OneOutCallerFullTest.premiseList full
  logInfo m!"{String.intercalate "\n" openLines.toList}"
  unless openOthers.size == 1 && openOthers.all (·.2) do
    throwError "{full}: the premises of class other must be exactly the closing premise MachineClosesAt, found {openOthers.size}:\n{String.intercalate "\n" (openOthers.toList.map (·.1))}"
  let (closedLines, closedOthers) ← Tests.Compiler.OneOutCallerFullTest.premiseList closed
  logInfo m!"{String.intercalate "\n" closedLines.toList}"
  unless closedOthers.isEmpty do
    throwError "{closed}: premises of class other (must be none):\n{String.intercalate "\n" (closedOthers.toList.map (·.1))}"
  -- (e) the callees' reflections among the closed form's binders
  let closedT := (← getConstInfo closed).type
  for kid in machKids do
    let found ← forallTelescope closedT fun xs _ => do
      let mut found := false
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines &&
            (t.find? (·.isConstOf (kid ++ `machineData))).isSome then
          found := true
      return found
    unless found do
      throwError "{closed}: no MachineDefines binder of the machine child {kid}"
  for kid in gateKids do
    let found ← forallTelescope closedT fun xs _ => do
      let mut found := false
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines &&
            (t.find? (·.isConstOf (kid ++ `gateValue))).isSome then
          found := true
      return found
    unless found do
      throwError "{closed}: no EntryDefines binder of the gate child {kid}"
  if gateKids.isEmpty &&
      (closedT.find? (·.isConstOf ``Tools.ShippingInlineSoundness.EntryDefines)).isSome then
    throwError "{closed}: an EntryDefines premise appears — a machine child is not read as a machine-route child"
  -- (e') an endpoint that existed: the generator's own proof of the same statement
  let mut handNote := ""
  if existing then
    let alt := f ++ `machine_design_svH_full_gen
    unless (← getEnv).contains alt do
      throwError "{alt}: the generator's proof of the existing statement was not added"
    std alt
    unless ← isDefEq (← getConstInfo alt).type (← getConstInfo full).type do
      throwError "{alt}: its statement is not the existing endpoint's"
    let facts := f ++ `machine_factsH
    let doc? ← Lean.findDocString? (← getEnv) alt
    let recorded : Bool := match doc? with
      | some doc => (doc.splitOn (toString facts)).length > 1
      | none => false
    unless recorded do
      throwError "{alt}: not recorded as built from the generated lemmas ({doc?})"
    handNote := s!" The endpoint existed (hand lemmas); the statement rebuilt from the GENERATED lemmas is isDefEq it and the rebuilt proof is kernel-checked as {alt}."
  -- (f) the goal gap of the closed form
  let gapName := match closed with
    | .str p s => Name.str p (s ++ "_gap")
    | n => n ++ `gap
  let mut gapNote := s!"goal gap {gapName}: the theorem exists already, not generated again"
  unless (← getEnv).contains gapName do
    let report ← Tools.ShippingFinalGoalCommand.gapOf closed gapName
    logInfo m!"GOALGAP {gapName} from {closed}\n{String.intercalate "\n" report.toList}"
    let bad := report.filter fun l => (l.splitOn "NOT ALLOWED").length > 1
    unless bad.isEmpty do
      throwError "{closed}: the goal-gap reporter lists premises NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
    gapNote := s!"goal gap {gapName}: {report.size} lines, none NOT ALLOWED"
  std gapName
  logInfo m!"{tag} {f}: {full} ({openLines.size} lines; other: the closing premise only) and {closed} ({closedLines.size} lines; other: NONE) — none of the four check premises of {old} (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; {gapNote}.{handNote} Machine-route callees (premise: MachineDefines of the child): {machKids}; gate callees (premise: EntryDefines): {gateKids}. SCOPE of this statement: {scope} Standard axioms."

/-- The scope sentence common to the declarations of this round. `conds`:
the per-declaration data conditions, named. -/
def scopeOf (f : Name) (conds : String) (notCovered : String) : String :=
  s!"(1) data conditions decided per declaration by the kernel — {conds} — conditions, not reductions; (2) runtime boundary premises that remain: the run of the entry, MachineDefines of {f}, the reflection of each callee (MachineDefines of a machine child, EntryDefines of a gate child), ChildBnd (open form: also MachineClosesAt); (3) the result depends on the compiler's guards (checkedOptimize's fallback, deinline's guards, closeInsts' checks, mergeChecked's validation of a machine child's merge); (4) the conclusion is about DesignSV (childMap D.modules) 0 (checkedOptimize b) — the module list, not the SV string, not #sim; (5) ONE declaration: a parent WITH a register (slots ≠ [] is asked by the head), the one-output closing (instFields = []), callees that are gate children or SLOTLESS LEAF machine children with the one output out — not slotless parents, not machine children with registers or with calls, not several outputs, not {notCovered}, not all successful inputs."

end Tests.Compiler.OneOutLeafAudit
