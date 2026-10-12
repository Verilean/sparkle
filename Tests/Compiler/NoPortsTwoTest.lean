import Tests.Compiler.NoPortsTest

/-! # `#machine_no_ports` on `two`: the first parent of TWO DIFFERENT leaf register machines (G1, round par/a-12)

`two` (`Tests/Compiler/ShippingChildBoundaryTest.lean`):

    def two (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let k := cnt en          -- CntOut: n : BitVec 8, hit : Bool
        let a := acc rs          -- AccOut: s : BitVec 8, odd : Bool
        r <~ Signal.mux k.hit (a.s + k.n) rs
        return rs

By READING (`docs/parallel/A-remaining.md` §2, unit U1): a parent WITH a
register whose callees `cnt` and `acc` are both LEAF REGISTER machines (a
register, no call of their own) — the scope `#machine_no_ports` states
(`Tools/ShippingNoPortsCommand.lean`, `scopeP`): no refusal line applies.
Its design-level endpoint today is `two.machine_design_svR0`
(`ShippingChildBoundaryTest` 70), which asks `shipsHierCheck`, `kidsMixed`,
`designCheck 0`, `outsCheck 0` (evaluated true on the real compile there,
lines 113–123). `two` is NOT in `HierBindsCensusTest.candidates`, so the
sweep of `NoPortsSweepTest` never tried it. No new theorem is written in
this file: three BUILT commands are run on one more declaration.

What is NEW against `parent` / `chained` (one called declaration, `cnt`):
TWO called declarations. Every generator of the chain has a branch for it
that NO declaration of the tests has elaborated (`docs/parallel/A-noports.md`,
"NOT done"):

* `#machine_closes_at` (`closesAtCoreG`): two reflection binders; the name
  separation of `cnt` / `acc` / `two` decided by `Tools.ShippingNameSep`
  (`sepB`) or, where `sepB` is false, left as a PREMISE mentioning
  `Name.toString` — then the closed endpoint has a premise NOT ALLOWED and
  this test THROWS naming it;
* `factsTheorem`, `designTheorem`: `kidOuts := fun k => List.getD [cnt…outs,
  acc…outs] k []`, and `callWidthsOk` decided on it;
* `portsTheorem`: `kid := fun k => List.getD [cnt.machineData,
  acc.machineData] k cnt.machineData`, `callArgsOk` with `declWidths` of it,
  and the per-entry `cases k` over the two entries with `acc.machine_leafKid`
  (generated here for the first time: `acc`'s data conditions — `callsOk`,
  no late domain binder, `slots ≠ []`, output width / name / scalar on
  `s`, `odd`);
* `outsGTheorem`, `maskedTheorem`, `kidsTheorem`: per-entry cases whose
  second entry is another declaration.

## EXPECTED (stated before the build; each command THROWS otherwise)

    two.machine_design_svNR1: source → shipped design's closed emitted texts at depth 1, …
    (#machine_closes_at two: its log line; premises MachineDefines cnt, MachineDefines acc)
    NOPORTS [two.machine_design_noPortsNR1, two.machine_design_noPortsNR1_closed]: … check antecedent left: none …
    GOALGAP two.machine_design_noPortsNR1_closed_gap from … (no gap_ hypothesis)
    NOPORTS PREMISE …_closed: ALLOWED binder hr    : RunsTo (synthesizeCombinational `two) …
    NOPORTS PREMISE …_closed: ALLOWED binder entry : MachineDefines … `two two.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED binder hR0   : MachineDefines … `cnt cnt.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED binder hR1   : MachineDefines … `acc acc.machineData.shape
    NOPORTS PREMISE …_closed: ALLOWED antecedent under the existentials : ChildBnd mref cref w ∧ MachineDefines … `cnt … ∧ MachineDefines … `acc …
    NOPORTS TWO: …

The binder names and the conjunct structure of the boundary are whatever
the generators write (not read off a build).

| endpoint | premise of `two.machine_design_svNR1` | predicted state |
|---|---|---|
| `two.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN (this test; the generators are built) — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt two` (open form) | predicted absent in `_closed` (`two.machine_closes_at`), pending build |
| | `hr`, `MachineDefines two`, `MachineDefines cnt`, `MachineDefines acc`, `ChildBnd` | run boundary: they stay premises |

`two.machine_design_svNR1` is generated HERE (it did not exist); the
inventory assertion below checks that it does ask the four check premises,
so that "absent" is a comparison with a statement of this same build.

## SCOPE (binding for any report)

ONE declaration, `two`: a parent WITH a register, two different leaf
register machine children, depth 1, the general (multi-output) closing.
(i) Data conditions decided per declaration by the kernel — those listed in
`Tests/Compiler/NoPortsTest.lean` (i), for `two` at its `nDecl` and for
`cnt` and `acc` (`machine_leafKid`) — are conditions, not reductions.
(ii) The result depends on the compiler's guards with fallback.
(iii) The conclusion is about `DesignSV (childMap D.modules) 1
(checkedOptimize b)` — the module list, not the SV string, not `#sim`.
(iv) The run, the three reflections and `ChildBnd` stay premises (no runtime
model). NOT covered: a child with calls of its own, a memory child, a gate
child, a parent without a register, "all successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two

set_option maxHeartbeats 0 in
#machine_no_ports Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two 1

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed

namespace Tests.Compiler.NoPortsTwoTest
open Lean Meta Elab Command

/-- The audit of `Tests/Compiler/NoPortsTest.lean`'s `run_cmd`, for one
declaration `f` at depth 1 with the called declarations `kids`: what was
generated exists on standard axioms; no endpoint statement mentions a
checker constant; the depth endpoint it is compared with DOES ask the four
check premises; no gap hypothesis; every premise of the closed endpoint is
ALLOWED; one reflection binder per called declaration. -/
def audit (f : Name) (kids : List Name) : MetaM Unit := do
  let old := f ++ `machine_design_svNR1
  let openN := f ++ `machine_design_noPortsNR1
  let closed := f ++ `machine_design_noPortsNR1_closed
  let gap := f ++ `machine_design_noPortsNR1_closed_gap
  let cl := f ++ `machine_closes_at
  let made := [f ++ `machine_runFacts, f ++ `machine_outsG1, f ++ `machine_maskedG,
    f ++ `machine_designG1, f ++ `machine_designK1, f ++ `machine_portsG, f ++ `machine_designP1,
    cl, openN, closed, gap] ++ kids.map (· ++ `machine_leafKid)
  for n in made do
    unless (← getEnv).contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- no endpoint statement mentions a checker constant
  for n in [openN, closed, gap] do
    let ci ← getConstInfo n
    for c in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf c)).isSome then
        throwError "{n}: the statement mentions {c}"
  -- the inventory: the depth endpoint of this build asks the four check premises
  let oldT := (← getConstInfo old).type
  for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf c)).isSome do
      throwError "{old}: does not mention {c} (the inventory is wrong)"
  -- the closed form reaches no closing premise; the open one asks it
  let closedT := (← getConstInfo closed).type
  if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closed}: still asks MachineClosesAt"
  unless ((← getConstInfo openN).type.find?
      (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt (the open form is not what was read)"
  -- no gap hypothesis
  let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
  unless gaps.isEmpty do
    throwError "{f}: the gap hypotheses are {gaps}, expected none"
  -- the complete premise list of the closed endpoint
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  -- one reflection binder per called declaration
  for kid in kids do
    let found ← forallTelescope closedT fun xs _ => do
      let mut found := false
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines &&
            (t.find? (·.isConstOf (kid ++ `machineData))).isSome then
          found := true
      return found
    unless found do
      throwError "{closed}: no MachineDefines binder of the child {kid}"
  -- the shape that was read
  let r ← Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  unless calls.eraseDups == kids do
    throwError "{f}: the called declarations are {calls.eraseDups}, expected {kids}"
  if r.shape.instFields.isEmpty then throwError "{f}: not a general-closing shape"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  logInfo m!"NOPORTS TWO {f}: {openN}, {closed} and {gap} on standard axioms, with {f}.machine_runFacts, _outsG1, _maskedG, _designG1, _designK1, _portsG, _designP1, {cl} and machine_leafKid of {kids}; no endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} (generated in this file) mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck; NO gap hypothesis; {lines.size} binders and antecedents of the closed endpoint listed, 0 NOT ALLOWED; a MachineDefines binder per called declaration. Call entries {calls} — {kids.length} DIFFERENT called declarations: the several-callee branches of the chain's generators elaborated on a declaration. SCOPE: one declaration, a parent WITH a register, leaf register machine children, depth 1; data conditions decided per declaration (conditions, not reductions); the run, the reflections and ChildBnd remain premises; compiler guards with fallback; the conclusion is DesignSV of the module list, not the SV string, not #sim."

end Tests.Compiler.NoPortsTwoTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsTwoTest.audit ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two
    [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
     ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc]
