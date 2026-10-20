import Tests.Compiler.OneOutCallerFullTest
import Tools.ShippingOneOutGenCommand

/-! # `#machine_oneout`: the one-output head's lemmas GENERATED, one declaration at a time (G1, round par/a-9)

The generator `Tools/ShippingOneOutGenCommand.lean` on five declarations,
IN THIS ORDER, each in its own section (a failure in one section is an
error of that section; the later sections are still elaborated and logged):

| | declaration | what is new against `caller` | EXPECTED outcome (stated before the build) |
|---|---|---|---|
| (i) | `caller` | nothing: the hand instance's declaration | `PRESENT` — the endpoint `caller.machine_design_svH_full` exists (hand lemmas); the statement rebuilt from the GENERATED lemmas must be `isDefEq` it; the rebuilt proof is kernel-checked as `caller.machine_design_svH_full_gen` |
| (ii) | `callerTwice` | one register; the call's 2nd argument is the INPUT `x` | `GENERATED`. The reader (`machInstance`, `machLetIndex`) turns EVERY non-domain call argument into a hardware `let` — a new one `inst0_arg1` whose value is the input and whose kind is the CALLEE's binder kind — so the argument is a `let` port and `callArgsOk` is expected true |
| (iii) | `callerD` | child `pickD`, domain-polymorphic; `nDecl = 2` (the domain binder, `x`) | `GENERATED`. `pickD.gateBinders` has the domain binder; the argument widths filter it, as `GateChildPorts.inWidths` does |
| (iv) | `callerNested` | a flattened sub-machine `counter2`; `nDecl = 2`; the 1st argument is the sub-machine's result | `GENERATED`. The sub-machine's slots are among `layout.slots`; the argument is again a new `let` |
| (v) | `callerRep` | 2 entries, both `pick`; the 2nd call's argument is the 1st call's result | `GENERATED`. The result wire `y` as an argument is NOT passed as a wire: the reader makes a `let` `inst1_arg1` whose value reads the call output's transition input, so `core_callConns₁`'s description (an argument wire is the transition port of a `let`) applies unchanged; no generalisation of that theorem is used |

These expectations are PREDICTIONS from reading the reader and the data
conditions; each is asserted by `#machine_oneout_try f "…"` (an error when
the outcome's class differs). What is known BUILT for (ii)–(v) before this
file: `f.machine_design_svHR`, and `f.machine_closes_at`, whose proof
decides `gateCallsOk` — that is `callsOk nDecl`, the slot count, no late
domain binder and `instFields = []` at the reader's `nDecl`. NOT known
before the build: `callArgsOk`, the per-entry condition, the output
name / scalar conditions, and every generated proof.

OUT OF SCOPE in this round (not run here):
* `callerMix` (`pick`, `pickD`), `callerABA` (`pick`, `pickD`, `pick`): two
  called DECLARATIONS — `machine_closes_at` may carry name-separation
  premises, which would be premises of class `other` in the closed form;
  the generator's per-entry disjunction is written for several callees but
  was not exercised.
* `callerInner`: no `callerInner.machine_ships_hierHR` (the generator's
  first scope test refuses it).

## What a GENERATED line means, and what it does not (binding)

For each declaration with a generated endpoint the test prints the complete
premise list of the open and the closed form (`ONEOUT FULL PREMISE` lines:
`run` / `reflection` / `ChildBnd` / `other` / `data`) and THROWS unless:
`other` is exactly the closing premise on the open form and EMPTY on the
closed form; every premise of `f.machine_closes_at` is a run, a reflection
or `ChildBnd`; none of the eight checker constants is written in either
statement or found by the bounded premise expansion; the first antecedent
is not `True`; every generated constant is on standard axioms; the goal-gap
reporter lists no NOT ALLOWED premise.

Even then "no check premise" is a statement with this scope:
(1) per-declaration DATA CONDITIONS are decided by the kernel on the
reflected data (`f.oneout_*`, `c.gate_width`, what `#gate_child` left) —
conditions, not reductions; (2) the run, `MachineDefines f`,
`EntryDefines c`, `ChildBnd` stay premises (no runtime model); (3) the
result depends on the compiler's guards with fallback; (4) the conclusion
is about `DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module
list, not the SV string, not `#sim`; (5) ONE declaration each: a parent
WITH a register, GATE children, the one-output closing — not slotless
parents, not machine-route children, not several outputs, not "all
successful inputs", no corpus measurement.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutFamilyTest
open Lean Meta Elab Command

/-- Standard axioms only. -/
def std (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The names the generator leaves under `f`. -/
def generatedNames (f : Name) : List Name :=
  [`machine_factsH, `machine_outsH, `machine_portsRawH, `machine_portsShippedH,
   `machine_hierTypedH, `machine_designFullH, `oneout_callsOk, `oneout_slotLen, `oneout_domB,
   `oneout_insts, `oneout_instFields, `oneout_nomem, `oneout_slots,
   `oneout_outChars, `oneout_kidIns, `oneout_callArgs,
   `oneout_entries].map (f ++ ·)

/-- The names the default path no longer generates (par/r-5: `outTy_of_core` /
`outScalar_of_core` at the run's `hcore`, `entry`). -/
def readerNames (f : Name) : List Name :=
  [`oneout_outTy, `oneout_outScalar].map (f ++ ·)

/-- The audit of one declaration after `#machine_oneout_try`. `kids`: its
distinct callees. `hand`: the endpoint existed before (built from hand
lemmas) — then the generator's own proof `_gen` is audited too and the goal
gap theorem, which exists already, is not generated again. Where no
endpoint was generated the audit is SKIPPED with a log line (the outcome's
class was asserted by the command). -/
def audit (f : Name) (kids : List Name) (hand : Bool) : MetaM Unit := do
  let full := f ++ `machine_design_svH_full
  let closed := Tools.ShippingMachineClosesGen.closedName full
  let cl := f ++ `machine_closes_at
  let old := f ++ `machine_design_svHR
  let facts := f ++ `machine_factsH
  unless (← getEnv).contains full && (← getEnv).contains closed && (← getEnv).contains facts do
    logInfo m!"ONEOUT FAMILY {f}: no generated endpoint with a closed form — premise list, axiom audit and goal gap SKIPPED; no premise of {old} counts as removed for {f}"
    return
  -- (a) what was generated exists, on standard axioms
  let kidNames := kids.flatMap fun c =>
    [c ++ `gate_full, c ++ `gate_ports, c ++ `gate_kidK, c ++ `gate_width]
  for n in generatedNames f ++ kidNames ++ [full, closed, cl] do
    unless (← getEnv).contains n do throwError "{n}: not generated"
    std n
  for n in readerNames f do
    if (← getEnv).contains n then
      throwError "{n}: generated — the default path takes it from the reader (par/r-5)"
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
  -- no premise of a generated lemma mentions or hides a checker
  for n in [facts, f ++ `machine_outsH, f ++ `machine_portsRawH, f ++ `machine_portsShippedH,
      f ++ `machine_hierTypedH, f ++ `machine_designFullH] do
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
  -- (e) the hand-built endpoint: the generator's own proof of the same statement
  let mut handNote := ""
  if hand then
    let alt := f ++ `machine_design_svH_full_gen
    unless (← getEnv).contains alt do
      throwError "{alt}: the generator's proof of the existing statement was not added"
    std alt
    unless ← isDefEq (← getConstInfo alt).type (← getConstInfo full).type do
      throwError "{alt}: its statement is not the existing endpoint's"
    let doc? ← Lean.findDocString? (← getEnv) alt
    let recorded : Bool := match doc? with
      | some doc => (doc.splitOn (toString facts)).length > 1
      | none => false
    unless recorded do
      throwError "{alt}: not recorded as built from the generated lemmas ({doc?})"
    handNote := s!" The endpoint existed (hand lemmas); the statement rebuilt from the GENERATED lemmas is isDefEq it and the rebuilt proof is kernel-checked as {alt}."
  -- (f) the goal gap of the closed form
  let mut gapNote := "goal gap: the theorem of the earlier round exists, not generated again"
  unless hand do
    let gapName := match closed with
      | .str p s => Name.str p (s ++ "_gap")
      | n => n ++ `gap
    let report ← Tools.ShippingFinalGoalCommand.gapOf closed gapName
    logInfo m!"GOALGAP {gapName} from {closed}\n{String.intercalate "\n" report.toList}"
    let bad := report.filter fun l => (l.splitOn "NOT ALLOWED").length > 1
    unless bad.isEmpty do
      throwError "{closed}: the goal-gap reporter lists premises NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
    std gapName
    gapNote := s!"goal gap {gapName}: {report.size} lines, none NOT ALLOWED"
  logInfo m!"ONEOUT FAMILY {f}: {full} ({openLines.size} lines; other: the closing premise only) and {closed} ({closedLines.size} lines; other: NONE) — none of the four check premises of {old} (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; {gapNote}.{handNote} SCOPE of this statement: (1) data conditions decided per declaration by the kernel for {f} ({f}.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _nomem, _slots, _outChars, _callArgs at the numerals of {f}.oneout_kidIns, _entries; output width / scalar from the reader: outTy_of_core / outScalar_of_core, not decided) and for the callees {kids} (gate_width, what #gate_child left) are conditions, not reductions; (2) runtime boundary premises that remain: the run of the entry, MachineDefines of {f}, ChildBnd, EntryDefines of the callees (open form: also MachineClosesAt); (3) the result depends on the compiler's guards (checkedOptimize's fallback, deinline's guards, closeInsts' checks); (4) the conclusion is about DesignSV (childMap D.modules) 0 (checkedOptimize b) — the module list, not the SV string, not #sim; (5) ONE declaration with a register, gate children and the one-output closing: not slotless parents, not machine-route children, not several outputs, not all successful inputs. Standard axioms."

/-- A refused declaration has nothing under the generator's names. -/
def leftNothing (f : Name) : MetaM Unit := do
  for n in [f ++ `machine_design_svH_full, f ++ `machine_factsH, f ++ `oneout_callsOk] do
    if (← getEnv).contains n then
      throwError "{n}: left behind by a refused generation"
  logInfo m!"ONEOUT FAMILY: {f} REFUSED, nothing left under its names. Out of scope in this round and not run: callerMix, callerABA (two called declarations: name-separation premises may appear in the closed form)."

end Tests.Compiler.OneOutFamilyTest

/-! ## (i) `caller` — expected PRESENT (statement verified against the hand-built endpoint) -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.caller "PRESENT"

run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick] true

/-! ## (ii) `callerTwice` — expected GENERATED (the input argument is a `let`) -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick] false

/-! ## (iii) `callerD` — expected GENERATED (domain-polymorphic child `pickD`) -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD] false

/-! ## (iv) `callerNested` — expected GENERATED (a flattened sub-machine; `nDecl = 2`) -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick] false

/-! ## (v) `callerRep` — expected GENERATED (two entries of `pick`; the 2nd argument of the 2nd call is a `let` reading the 1st call's output) -/

set_option maxHeartbeats 0 in
#machine_oneout_try callerRep "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``callerRep
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick] false

/-! ## A refusal is logged with its reason and leaves nothing

`callerInner` has no `machine_ships_hierHR`: the first scope test. -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner "REFUSED"

run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.leftNothing
    ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner
