import Tests.Compiler.NoKidsTest
import Tools.ShippingNoPortsCommand

/-! # The depth SV endpoint with NO compiler-check premise (G1, round par/a-4)

`#machine_no_ports f n` (`Tools/ShippingNoPortsCommand.lean`) on `parent`
and `chained` (`Tests/Compiler/ShippingMachineSeqTest.lean`; child: the leaf
register machine `cnt`) at depth 1. Generated per declaration `f`:
`cnt.machine_leafKid`, `f.machine_portsG` (`portsMatchB` of the shipped
module from the core run — `core_portsMatch_shipped_leaf` at `f`'s data),
`f.machine_designP1` (`designCheck` with no check premise),
`f.machine_design_noPortsNR1` and its `_closed` form:
`∃ raw D, … ∧ (Bnd → …)`.

`#machine_goal_gap_of` on the closed forms logs the `GOALGAP` lines. Then,
as ERRORS otherwise:

* standard axioms only (the endpoints, the gap theorems, every new general
  theorem and the ones it composes);
* no statement of an endpoint mentions `portsMatchB`, `kidsPass`,
  `designCheck`, `shipsHierCheck`, `outsCheck` or `kidsMaskedN` (nor
  `hierCheck`);
* the gap theorem of each closed endpoint has NO `gap_…` hypothesis;
* every premise of each closed endpoint — each proposition among its
  binders and each antecedent under its `∃ raw D, … ∧` — is ALLOWED in the
  sense of `Tools.ShippingFinalGoalCommand.allowed` (`RunsTo`,
  `MachineDefines`, `EntryDefines`, `ChildBnd`, conjunctions of those).

The COMPLETE premise list of each closed endpoint is logged, one line per
binder and per antecedent, prefixed `NOPORTS PREMISE <decl>:` — to be read
by a human: the expected content is the run of the entry
(`RunsTo (synthesizeCombinational f) …`), the reflections (`MachineDefines`
of `f` and of `cnt`) and `ChildBnd`, nothing else.

## What the empty gap means, and what it does NOT

(i) DATA CONDITIONS decided by the generator per declaration (kernel
`decide` on the reflected `machineData`; a declaration where one fails is
NOT covered — the command reports an error, it proves nothing false). For
the parent `f` with `nDecl` declared binders: `f.machineData.callsOk nDecl`;
`ss.length = shape.layout.slots.length`; no domain binder after `nDecl`;
`shape.insts ≠ []`; `shape.instFields ≠ []`; `shape.layout.slots ≠ []`;
every output's `ty.bitWidth = width`; no memory callee; the output names
character-wise `charOk` (hence `sanitizeName`-stable); the output types
`scalarTy`;
`callWidthsOk f.machineData nDecl (fun _ => cnt.machineData.shape.layout.outs)`;
`callArgsOk f.machineData nDecl (fun _ => declWidths cnt.machineData)`;
every entry's callee is `cnt`. For the child `cnt` (`cnt.machine_leafKid`):
`callsOk nIn`; no domain binder after `nIn`; `shape.insts = []`;
`shape.layout.slots ≠ []`; `ss.length = shape.layout.slots.length`; the
outputs' `ty.bitWidth = width`, names `charOk`, types `scalarTy`. Plus those
of the earlier generators this one calls (`machine_runFacts`,
`machine_outsG1`, `machine_maskedG`, `machine_designG1`,
`machine_designK1`, `machine_closes_at`, `machine_ok`).

(ii) COMPILER GUARDS the result depends on (they are IN the compiler; the
theorems are about the guarded compiler and say nothing about how often a
guard falls back): `checkedOptimize` ships the INPUT module when the
hierarchy gate holds and its check does not bind (the fallback); the
optimizer's candidate is kept only if (1) its instance names are distinct,
(2) the design-free linked order holds, (3) `printOk` accepts its text,
(4) a register merge keeps masked outputs masked (and passes `printOk`),
(5) `connsKept`: connected wires keep their declared width — otherwise the
input module is shipped.

(iii) WHAT THE CONCLUSION IS ABOUT: the module LIST — `DesignSV (childMap
D.modules) 1 (checkedOptimize b) …`, the emitted-text semantics of the
shipped top module over the children's modules of the design `D` of the
run. It is NOT a statement about the printed SystemVerilog string, about a
parser reading it back, or about any simulator; `#sim` (which optimizes
twice) and the JIT C are outside. The writer theorem
(`writer_prints_endpoint_artifact`) relates the writer's module list to this
object, not its string.

(iv) SCOPE: a parent WITH a register whose callees are all LEAF REGISTER
machines (no calls of their own, a register), depth 1; here `parent` and
`chained` only. No memory child, no gate child, no child with calls, no
parent without a register.

(v) STANDING RUNTIME ASSUMPTIONS: `ChildBnd mref cref w` (the child cache's
laws at the start world, `RefLaws`) and the reflections `MachineDefines`
stay PREMISES. The result is conditional on them: there is no model of the
Lean runtime (`ST.Ref`, `MetaM`) under them, `RunsTo` is the project's
relation for a run of the entry, and nothing proves that an actual
`#synthesizeVerilog` call satisfies them.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_no_ports Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

set_option maxHeartbeats 0 in
#machine_no_ports Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid
#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_portsG
#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_designP1
#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noPortsNR1_closed
#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_noPortsNR1_closed

namespace Tests.Compiler.NoPortsTest
open Lean Meta Elab Command

/-- The antecedents of an endpoint body `∃ w…, P ∧ (A₁ → … → C)`: the `Aᵢ`,
printed, each with whether it is allowed. -/
partial def innerAntecedents (ty : Lean.Expr) : MetaM (Array (String × Bool)) := do
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun w => innerAntecedents (mkApp p w).headBeta
  else if ty.isAppOfArity ``And 2 then
    let mut R := ty.getArg! 1
    let mut out : Array (String × Bool) := #[]
    while (← Tools.ShippingFinalGoalCommand.isPropArrow R) do
      let A := R.bindingDomain!
      out := out.push (toString (← ppExpr A), Tools.ShippingFinalGoalCommand.allowed A)
      R := R.bindingBody!
    return out
  else
    throwError "expected ∃ … , P ∧ (…), found{indentExpr ty}"

/-- The complete premise list of the endpoint `decl`: one line per binder
(a proposition: `ALLOWED` / `NOT ALLOWED`; anything else: `data`) and per
antecedent under its existentials; and the NOT ALLOWED lines. -/
def premiseLines (decl : Name) : MetaM (Array String × Array String) := do
  let ci ← getConstInfo decl
  forallTelescope ci.type fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Array String := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      let nm ← x.fvarId!.getUserName
      let pp := toString (← ppExpr t)
      if ← isProp t then
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"NOPORTS PREMISE {decl}: ALLOWED     binder {nm} : {pp}"
        else
          let l := s!"NOPORTS PREMISE {decl}: NOT ALLOWED binder {nm} : {pp}"
          lines := lines.push l
          bad := bad.push l
      else
        lines := lines.push s!"NOPORTS PREMISE {decl}: data        binder {nm} : {pp}"
    let inner ← innerAntecedents body
    for (s, ok) in inner do
      if ok then
        lines := lines.push s!"NOPORTS PREMISE {decl}: ALLOWED     antecedent under the existentials : {s}"
      else
        let l := s!"NOPORTS PREMISE {decl}: NOT ALLOWED antecedent under the existentials : {s}"
        lines := lines.push l
        bad := bad.push l
    return (lines, bad)

/-- The six checker constants (and `hierCheck`). -/
def checkers : List Name :=
  [``Tools.ShippingDesignSV.portsMatchB,
   ``Tools.ShippingDesignSV.kidsPass,
   ``Tools.ShippingDesignSV.designCheck,
   ``Tools.ShippingHierPremisesBase.shipsHierCheck,
   ``Tools.ShippingDesignSVBack.outsCheck,
   ``Tools.ShippingMachineShipsDepth.kidsMaskedN,
   ``Tools.ShippingHierPremisesBase.hierCheck]

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

run_cmd liftTermElabM do
  -- the general theorems: the new ones and the ones they compose
  for n in [``Tools.ShippingPortsMatchShippedLeaf.core_portsMatch_shipped_leaf,
      ``Tools.ShippingNoPorts.machine_design_noPorts,
      ``Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf,
      ``Tools.ShippingPortsMatchShipped.portsMatchB_shipped,
      ``Tools.ShippingPortsMatchShipped.checkedOptimize_conns,
      ``Tools.ShippingChecksWidths.core_hierGate,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid] do
    stdAxioms n
  -- the head's statement mentions no checker constant except `designCheck`
  -- (in its hypothesis `hDesign`, which the generator discharges)
  let hd ← getConstInfo ``Tools.ShippingNoPorts.machine_design_noPorts
  for c in checkers do
    unless c == ``Tools.ShippingDesignSV.designCheck ||
        c == ``Tools.ShippingDesignSVBack.outsCheck do
      if (hd.type.find? (·.isConstOf c)).isSome then
        throwError "machine_design_noPorts: the statement mentions {c}"
  let mut summary : Array String := #[]
  for f in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained] do
    let closed := f ++ `machine_design_noPortsNR1_closed
    let made := [f ++ `machine_portsG, f ++ `machine_designP1,
      f ++ `machine_design_noPortsNR1, closed, f ++ `machine_design_noPortsNR1_closed_gap]
    for n in made do
      unless (← getEnv).contains n do throwError "{n}: not generated"
      stdAxioms n
    for n in [f ++ `machine_design_noPortsNR1, closed,
        f ++ `machine_design_noPortsNR1_closed_gap] do
      let ci ← getConstInfo n
      for c in checkers do
        if (ci.type.find? (·.isConstOf c)).isSome then
          throwError "{n}: the statement mentions {c}"
    -- no gap hypothesis
    let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames
      (f ++ `machine_design_noPortsNR1_closed_gap)
    unless gaps.isEmpty do
      throwError "{f}: the gap hypotheses are {gaps}, expected none"
    -- the complete premise list of the closed endpoint
    let (lines, bad) ← premiseLines closed
    logInfo m!"{String.intercalate "\n" lines.toList}"
    unless bad.isEmpty do
      throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
    summary := summary.push
      s!"{f}: no gap hypothesis, {lines.size} binders and antecedents listed, 0 not allowed"
  logInfo m!"NOPORTS TEST: parent and chained — machine_portsG, machine_designP1, machine_design_noPortsNR1, its _closed form and its gap theorem on standard axioms; core_portsMatch_shipped_leaf, machine_design_noPorts, core_portsMatch_raw_leaf, portsMatchB_shipped, checkedOptimize_conns, core_hierGate, cnt.machine_leafKid on standard axioms; no endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck; NO gap hypothesis; every premise of the closed endpoints is allowed (a run, a reflection, ChildBnd or a conjunction of those: the NOPORTS PREMISE lines); {summary}"

end Tests.Compiler.NoPortsTest
