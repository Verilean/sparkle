import Tests.Compiler.OneOutCallerPortsTest
import Tools.ShippingOneOutFullCommand
import Tools.ShippingFinalGoalCommand

/-! # ONE endpoint, `caller` (child `pick`): the combinational endpoint with NO check antecedent (G1, round par/a-8)

`caller.machine_design_svH_full` (and `caller.machine_design_svH_full_closed`)
is generated here by `#machine_design_svH_full` from the head
`Tools.ShippingOneOutHead.machine_design_svH_free` at the trivially true
residual (discharged: it is not an antecedent of the statement) and the four
theorems

    caller_factsH     (OneOutCallerTest)       the run's facts of the full entry's module
    caller_hierTyped  (OneOutCallerPortsTest)  hierTyped (childMap D.modules) b
    caller_designFull (OneOutCallerPortsTest)  designCheck (childMap D.modules) 0 (checkedOptimize b)
    caller_outsH      (OneOutCallerTest)       outsCheck … under the statement-kind gate

The earlier endpoint `caller.machine_design_svH_free` (two residual
conditions) is NOT touched: it stays, with its test, as the record of the
intermediate state.

## What "no check antecedent" means here, and what it does not (binding)

(i) DATA CONDITIONS, decided per declaration by the kernel (`decide` /
`rfl`) on the reflected data of `caller` and `pick`. They are conditions,
not reductions; where one fails the theorem does not exist. For `caller`
(`caller.machineData`): `callsOk 1`; `ss.length = shape.layout.slots.length`;
no domain binder after the first (`hdomB`); `shape.insts ≠ []`;
`shape.instFields = []`; `shape.layout.slots ≠ []`; every output's
`ty.bitWidth = width`; the output names character-wise `charOk`; the output
types `scalarTy`; no memory callee; `callArgsOk caller.machineData 1 kidIns`
(the widths of the types of the `let` binders of the call's arguments are
`pick`'s argument widths — nothing in the compiler compares them); the width
of the type of the binder of the call's result is `8`. For `pick`:
`pick.gateSort.width = 8`, and what `#gate_child pick` left (`pick.gate_old`,
`pick.gate_peel`, `pick.gate_wf`, the Bool / bit-vector binder positions).
Plus those of the generators run before (`caller.machine_ships_hierHR`'s
output-width premise, `caller.machine_closes_at`'s conditions).

(ii) RUNTIME BOUNDARY, premises that REMAIN (no model of the Lean runtime
under them): the run of the entry `RunsTo (synthesizeCombinational caller)
…`; `MachineDefines` of `caller`; `ChildBnd mref cref w` at the run's start
world; `EntryDefines` of `pick`; on the open form also `MachineClosesAt` of
`caller`, which the closed form replaces by the premises of
`caller.machine_closes_at` (printed below; the test throws if one of them is
not a run / a reflection / `ChildBnd`).

(iii) COMPILER GUARDS the result depends on: `checkedOptimize` ships the
input module where its hierarchical check does not bind or rejects the
candidate, and keeps a candidate only under the guards of `deinline`
(distinct instance names, linked order, `printOk`, `connsKept`); the
one-output closing's own checks (`closeInsts`: one output port, no clock /
reset input, the children's combinational check). The theorem is about the
guarded compiler.

(iv) WHAT THE CONCLUSION IS ABOUT: `DesignSV (childMap D.modules) 0
(checkedOptimize b) …` — the emitted-text semantics of the shipped module
over the MODULE LIST of the core run's design. NOT the printed
SystemVerilog string, not a parser reading it back, not `#sim`.

(v) SCOPE: ONE declaration, `caller` — a parent WITH a register, one call
entry, a GATE child (`pick`), the one-output closing. NOT slotless parents,
NOT machine-route children, NOT several outputs, NOT "all successful
inputs", no other declaration.

## What the test checks (it throws otherwise)

* the complete premise lists of both endpoints, one `ONEOUT FULL PREMISE`
  line per binder / conjunct / antecedent, classified `run`, `reflection`,
  `ChildBnd`, `other` (`data` for non-propositions);
* "other" is EMPTY for the closed form and exactly the closing premise
  `MachineClosesAt` for the open form;
* every premise of `caller.machine_closes_at` is a run, a reflection or
  `ChildBnd` (a name-separation premise is reported and is an error);
* the refuse scan and the `hidden` scan find none of the eight checker
  constants in either statement; the first antecedent is not `True`;
* standard axioms;
* `#machine_goal_gap_of` on the closed form (its lines are logged).

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_design_svH_full Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  [Tests.Compiler.OneOutCallerTest.caller_factsH,
   Tests.Compiler.OneOutCallerPortsTest.caller_hierTyped,
   Tests.Compiler.OneOutCallerPortsTest.caller_designFull,
   Tests.Compiler.OneOutCallerTest.caller_outsH]

#check @Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_full
#check @Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_full_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_full_closed

namespace Tests.Compiler.OneOutCallerFullTest
open Lean Meta Elab Command

/-- The class of a premise. -/
def kindOf (t : Lean.Expr) : String :=
  if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then "run"
  else if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
      t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then "reflection"
  else if t.isAppOf ``Tools.ShippingChildInv.ChildBnd then "ChildBnd"
  else "other"

/-- The conjuncts of a premise. -/
partial def conjuncts (t : Lean.Expr) : List Lean.Expr :=
  if t.isAppOfArity ``And 2 then conjuncts (t.getArg! 0) ++ conjuncts (t.getArg! 1)
  else [t]

/-- The antecedents of an endpoint body `∃ w…, P ∧ (A₁ → … → C)`: the `Aᵢ`. -/
partial def innerPremises {α : Type} (ty : Lean.Expr) (k : Array Lean.Expr → MetaM α) :
    MetaM α := do
  if ty.isAppOfArity ``Exists 2 then
    let dom := ty.getArg! 0
    let p := ty.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm dom fun w => innerPremises (mkApp p w).headBeta k
  else if ty.isAppOfArity ``And 2 then
    let mut R := ty.getArg! 1
    let mut out : Array Lean.Expr := #[]
    while (← Tools.ShippingFinalGoalCommand.isPropArrow R) do
      out := out.push R.bindingDomain!
      R := R.bindingBody!
    k out
  else
    throwError "expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- The complete premise list of `decl`: the lines, and the printed premises
of class `other` with whether each is a `MachineClosesAt`. `inner := false`
for a theorem that is not of the endpoints' shape (binders only). -/
def premiseList (decl : Name) (inner : Bool := true) :
    MetaM (Array String × Array (String × Bool)) := do
  let ci ← getConstInfo decl
  forallTelescope ci.type fun xs body => do
    let mut lines : Array String := #[]
    let mut others : Array (String × Bool) := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      let nm ← x.fvarId!.getUserName
      if ← isProp t then
        for c in conjuncts t do
          let pp := toString (← ppExpr c)
          let kd := kindOf c
          lines := lines.push s!"ONEOUT FULL PREMISE {decl}: {kd} | binder {nm} : {pp}"
          if kd == "other" then
            others := others.push (pp, c.isAppOf ``Tools.ShippingChildInv.MachineClosesAt)
      else
        lines := lines.push
          s!"ONEOUT FULL PREMISE {decl}: data | binder {nm} : {toString (← ppExpr t)}"
    if inner then
      let (ls, os) ← innerPremises body fun ants => do
        let mut ls : Array String := #[]
        let mut os : Array (String × Bool) := #[]
        for a in ants do
          for c in conjuncts a do
            let pp := toString (← ppExpr c)
            let kd := kindOf c
            ls := ls.push
              s!"ONEOUT FULL PREMISE {decl}: {kd} | antecedent under the existentials : {pp}"
            if kd == "other" then
              os := os.push (pp, c.isAppOf ``Tools.ShippingChildInv.MachineClosesAt)
        return (ls, os)
      lines := lines ++ ls
      others := others ++ os
    return (lines, others)

run_cmd liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  let full := f ++ `machine_design_svH_full
  let closed := Tools.ShippingMachineClosesGen.closedName full
  let cl := f ++ `machine_closes_at
  let old := f ++ `machine_design_svHR
  let std (n : Name) : MetaM Unit := do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  unless (← getEnv).contains closed do
    throwError "{closed} was not generated"
  -- (d) axioms
  for n in [full, closed, cl, ``Tools.ShippingOneOutFullCommand.strip_true] do
    std n
  -- (c) the eight checker constants: written, or hidden in a premise's definition
  let checkers := Tools.ShippingOneOutCommand.forbidden ++ Tools.ShippingOneOutCommand.residualOnly
  for n in [full, closed] do
    let t := (← getConstInfo n).type
    Tools.ShippingOneOutCommand.refuse n t (mkConst ``True)
    let hits := Tools.ShippingOneOutCommand.mentioned checkers t
    unless hits.isEmpty do
      throwError "{n}: the statement mentions {hits}"
    if Tools.ShippingOneOutFullCommand.trueAntecedent t then
      throwError "{n}: the trivially true residual is an antecedent"
  -- the old endpoint asks the four check premises (the inventory)
  let oldT := (← getConstInfo old).type
  for c in [``Tools.ShippingHierPremises.shipsHierHCheck,
      ``Tools.ShippingMachineDepthH.kidsComb, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf c)).isSome do
      throwError "{old}: does not mention {c} (the inventory is wrong)"
  -- what `caller.machine_closes_at` contributes
  let (clLines, clOthers) ← premiseList cl (inner := false)
  logInfo m!"{String.intercalate "\n" clLines.toList}"
  unless clOthers.isEmpty do
    throwError "{cl}: contributes premises that are not a run / a reflection / ChildBnd (NOT allowed):\n{String.intercalate "\n" (clOthers.toList.map (·.1))}"
  -- (a), (b) the complete premise lists
  let (openLines, openOthers) ← premiseList full
  logInfo m!"{String.intercalate "\n" openLines.toList}"
  unless openOthers.size == 1 && openOthers.all (·.2) do
    throwError "{full}: the premises of class other must be exactly the closing premise MachineClosesAt, found {openOthers.size}:\n{String.intercalate "\n" (openOthers.toList.map (·.1))}"
  let (closedLines, closedOthers) ← premiseList closed
  logInfo m!"{String.intercalate "\n" closedLines.toList}"
  unless closedOthers.isEmpty do
    throwError "{closed}: premises of class other (must be none):\n{String.intercalate "\n" (closedOthers.toList.map (·.1))}"
  logInfo m!"ONEOUT FULL caller: {full} ({openLines.size} lines; other: the closing premise only) and {closed} ({closedLines.size} lines; other: NONE) — the combinational endpoint of caller with none of the four check premises of {old} (shipsHierHCheck, kidsComb, designCheck, outsCheck) and no residual. SCOPE of this statement: (i) data conditions decided per declaration for caller (callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk caller.machineData 1 kidIns, the result binder's width 8) and for pick (gateSort.width = 8, what #gate_child left); (ii) runtime boundary premises that remain: the run of the entry, MachineDefines of caller, ChildBnd, EntryDefines of pick (open form: also MachineClosesAt); (iii) the result depends on the compiler's guards (checkedOptimize's fallback, deinline's guards, closeInsts' checks); (iv) the conclusion is about DesignSV (childMap D.modules) 0 (checkedOptimize b) — the module list, not the SV string, not #sim; (v) ONE declaration with a register, a gate child and a one-output closing: not slotless parents, not machine-route children, not all successful inputs. Standard axioms."

end Tests.Compiler.OneOutCallerFullTest
