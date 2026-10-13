import Tests.Compiler.ShippingDesignSVMemTest
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tests.Compiler.ShippingChildBoundaryTest
import Tests.Compiler.NoPortsTest
import Tools.ShippingNoPortsMemCommand

/-! # `#machine_no_ports_mem` on the memory-only family: GENERATED in a closure WITHOUT the hand tests (round par/b-20)

## TARGET-ONLY — never in `Tests/AllTests.lean`, never co-imported with a hand test

This file CREATES the names the hand tests own:

    memCounter / syncNarrow / memWide / twoMems / mixedMems .machine_design_noPortsR0[_closed[_gap]]
        (hand: `NoPortsMemOnlyAt<Decl>Test`, `NoPortsMemOnlyClosed<Decl>Test`, and the
         target-only `NoPortsMemOnlyAtProbe`)
    withMemory.machine_design_noPortsR0[_closed[_gap]]
        (hand: `NoPortsMemWithMemoryTest`)

Importing it together with any of those is a duplicate declaration. It
imports none of them (its imports: the declarations' own endpoint files, the
audit helpers of `Tests.Compiler.NoPortsTest`, and the command). The audit
THROWS if a `…_regen` of an endpoint exists (that would mean a hand test was
in the imports and the compare path ran instead of the generation).

The compare path is exercised separately, on ONE hand test:
`Tests/Compiler/NoPortsMemGenCompareTest.lean`.

## What is run

* GENERATED (`#machine_no_ports_mem_try f "GENERATED"`): the five
  untransported memory-only parents `memCounter`, `twoMems`, `mixedMems`
  (`ShippingMachineMemLinkedTest`), `memWide`, `syncNarrow`
  (`ShippingDesignSVMemTest`), and the transported `withMemory`
  (`ShippingMachineFuseTest`) — six declarations (with `seqMem`, refused
  here, these are the seven memory declarations that have a hand endpoint);
* REFUSED, LOGGED with the reason (`… "REFUSED"`): `seqMem` (mixed memory /
  machine children), `cnt` (no call), `parent` (no memory callee), `midH`
  (no memory callee: a gate child);
* `#machine_goal_gap_of` on the six closed endpoints;
* the audit (an error on any failure).

## EXPECTED (stated before the build; the audit THROWS otherwise)

Nothing new is removed: these are the hand statements, produced by the
command. Each line is "endpoint — premise — predicted state".

| endpoint | premise | predicted state |
|---|---|---|
| `f.machine_design_noPortsR0`, `f` ∈ the five untransported | `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0` (of `f.machine_design_sv0`) | WRITTEN, NOT BUILT — predicted absent, as in the BUILT hand endpoint |
| | boundary `True` (of the base) | `ChildBnd mref cref w` (ADDED antecedent, allowed) |
| | `MachineCloses f` (of the base) | `MachineClosesAt f` — STILL A PREMISE, the one NOT ALLOWED |
| | the run, `MachineDefines f` | stay |
| `f.machine_design_noPortsR0_closed`, the same five | `MachineClosesAt f` | predicted ABSENT (`f.noPortsMem_closes`, no premise); 0 NOT ALLOWED |
| | the run, `MachineDefines f`, antecedent `ChildBnd` | stay |
| `withMemory.machine_design_noPortsR0` | `shipsHierCheck`, `kidsMem` (of `withMemory.machine_ships_hier`; it has no design-level base) | predicted absent, as in the BUILT hand endpoint |
| | boundary `True`; `MachineCloses withMemory` | `ChildBnd` (ADDED); `MachineClosesAt withMemory` (NOT ALLOWED) |
| `withMemory.machine_design_noPortsR0_closed` | `MachineClosesAt withMemory` | predicted ABSENT; 0 NOT ALLOWED; reads `withMemory.machineSourceDecl`, not `withMemory.machineSource` |
| `…_closed_gap` (six) | gap hypotheses | predicted NONE |
| `seqMem`, `cnt`, `parent`, `midH` | — | REFUSED with a reason line; nothing added |

SCOPE: one declaration each, a memory-only parent with register slots, depth
0; data conditions decided per declaration (conditions, not reductions);
compiler guards with fallback; `DesignSV` of the module list — not the SV
string, not `#sim`. The run, the reflection of `f` and `ChildBnd` at the
start world remain premises.

WRITTEN, NOT BUILT (par/b-20). -/

/-! ## The six generations -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "GENERATED"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow "GENERATED"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide "GENERATED"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems "GENERATED"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems "GENERATED"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory "GENERATED"

/-! ## The refusals (LOGGED with their reason; nothing is added) -/

set_option maxHeartbeats 0 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem "REFUSED"

set_option maxHeartbeats 0 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt "REFUSED"

set_option maxHeartbeats 0 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent "REFUSED"

set_option maxHeartbeats 0 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH "REFUSED"

/-! ## The goal gaps -/

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed

namespace Tests.Compiler.NoPortsMemGenFamilyTest
open Lean Meta Elab Command

/-- Does the statement `t` mention the constant `k`? -/
def mentions (t : Lean.Expr) (k : Name) : Bool :=
  (t.find? (·.isConstOf k)).isSome

/-- The `gap_…` hypotheses of a goal-gap theorem
(`Tests.Compiler.NoPortsMemSeqMemClosedTest.gapsOf`, restated: that file is a
hand test and must not be imported here). -/
def gapsOf (thm : Name) : MetaM (List String) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : List String := []
    for x in xs do
      let xn := (← x.fvarId!.getUserName).toString
      if xn.startsWith "gap_" then out := out ++ [xn]
    return out

/-- The proposition binders of a statement. -/
def propTypes (t : Lean.Expr) : MetaM (Array Lean.Expr) :=
  forallTelescope t fun xs _ => do
    let mut out : Array Lean.Expr := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then out := out.push ty
    return out

/-- The per-declaration NAME lemmas of the previous closing path
(`#machine_no_ports_mem_oldnames`): since round par/b-30 the command must
NOT leave them. -/
def oldNameLemmas (f : Name) (nMems : Nat) : List Name :=
  let notin := (List.range nMems).map fun j => s!"notin{j}"
  let several :=
    if nMems ≥ 2 then
      ((List.range nMems).map fun j => s!"at{j}") ++ ["sep", "parent"] ++
        ((List.range nMems).flatMap fun i =>
          ((List.range nMems).filter fun j => i < j).map fun j => s!"namesNe{i}_{j}")
    else []
  (notin ++ several).map fun s => f ++ Name.mkSimple s!"noPortsMem_{s}"

/-- The lemmas the command leaves for `f` (the same for any number of
placeholders: no name lemma). -/
def lemmas (f : Name) (_nMems : Nat) : List Name :=
  let one := ["entry", "calls", "slots", "domB", "outTy", "callWidths", "callArgs", "outChars",
    "outScalar", "data", "runFacts", "outsG0", "kidsMemG", "designP0", "alias", "argsN", "field",
    "argsNd", "outHead", "closeData", "closes"]
  one.map fun s => f ++ Name.mkSimple s!"noPortsMem_{s}"

/-- The audit of one generated declaration (an error on any failure):

* the endpoints, the gap theorem and every lemma exist, on standard axioms;
  no `…_regen` of an endpoint (the generation ran, not the compare path);
* no statement mentions a checker constant; the open endpoint asks
  `MachineClosesAt` (not `MachineCloses`), `ChildBnd`, and concludes about
  `DesignSV`; the closed endpoint and the gap theorem mention none of
  `MachineClosesAt`, `MachineCloses`, `ChildRanIn`;
* `f.noPortsMem_closes` has NO proposition premise;
* the open endpoint has three proposition binders, the closed one two — the
  run and `MachineDefines … f …`;
* the premise list by the goal-gap classifier: exactly one NOT ALLOWED in
  the open endpoint, none in the closed one, one line fewer;
* no gap hypothesis;
* `hasSv0`: the base `f.machine_design_sv0` mentions the four checks and
  `MachineCloses`; otherwise `f.machine_ships_hier` mentions `shipsHierCheck`,
  `kidsMem`, `MachineCloses`;
* `transported`: the endpoints read `f.machineSourceDecl`, not `f.machineSource`. -/
def audit (f : Name) (nMems : Nat) (hasSv0 transported : Bool) : MetaM Unit := do
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  let gap := f ++ `machine_design_noPortsR0_closed_gap
  let cl := f ++ `noPortsMem_closes
  let env ← getEnv
  for s in ["machine_design_noPortsR0_regen", "machine_design_noPortsR0_closed_regen"] do
    if env.contains (f ++ Name.mkSimple s) then
      throwError "{f ++ Name.mkSimple s}: exists — the endpoint was there before this file (a hand test is in the imports: NAME CLASH); this file must be built in a closure without the hand tests"
  for n in lemmas f nMems ++ [openN, closed, gap] do
    unless env.contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- par/b-30: no per-declaration name lemma, and the closing is the general
  -- theorem without name hypotheses (a DIRECT constant of its proof term)
  for n in oldNameLemmas f nMems do
    if env.contains n then
      throwError "{n}: generated — the command still takes the per-declaration name path"
  let clUsed : Array Name := match env.find? cl with
    | some (.thmInfo ti) => ti.value.getUsedConstants
    | _ => #[]
  unless clUsed.contains ``Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names do
    throwError "{cl}: its proof does not apply machineClosesAt_of_memOnlyData_names: {clUsed}"
  if clUsed.contains ``Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData then
    throwError "{cl}: its proof applies the theorem WITH name hypotheses"
  Tests.Compiler.NoPortsTest.stdAxioms ``Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
  for n in [``Tools.ShippingMemOnly.memOnly_runFacts, ``Tools.ShippingMemOnly.memOnly_outsCheck,
      ``Tools.ShippingMemOnly.memOnly_kidsMem, ``Tools.ShippingMemOnly.memOnly_designCheck,
      ``Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData,
      ``Tools.ShippingMemTransport.composedG_src,
      ``Tools.ShippingNoPorts.machine_design_noPorts] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  let openT := (← getConstInfo openN).type
  let closedT := (← getConstInfo closed).type
  let gapT := (← getConstInfo gap).type
  let forbidden := Tests.Compiler.NoPortsTest.checkers ++
    Tools.ShippingNoPortsMemCommand.forbiddenMem
  for (n, t) in [(openN, openT), (closed, closedT), (gap, gapT)] do
    for k in forbidden do
      if mentions t k then throwError "{n}: the statement mentions {k}"
    if mentions t ``Tools.ShippingMachineEntry.MachineCloses then
      throwError "{n}: asks the all-worlds MachineCloses"
  for k in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildBnd,
      ``Tools.ShippingDesignSV.DesignSV] do
    unless mentions openT k do throwError "{openN}: does not mention {k}"
  for (n, t) in [(closed, closedT), (gap, gapT)] do
    for k in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildRanIn] do
      if mentions t k then throwError "{n}: the statement mentions {k}"
  for k in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingDesignSV.DesignSV] do
    unless mentions closedT k do throwError "{closed}: does not mention {k}"
  -- the closing theorem: no proposition premise, it concludes the closing of `f`
  let clT := (← getConstInfo cl).type
  let clP ← propTypes clT
  unless clP.isEmpty do
    throwError "{cl}: {clP.size} proposition premise(s), expected none"
  let clOk ← forallTelescope clT fun _ body => do
    if body.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 then
      isDefEq (body.getArg! 4) (toExpr f)
    else
      pure false
  unless clOk do throwError "{cl}: does not conclude MachineClosesAt of {f}:{indentExpr clT}"
  -- the binders
  let pOpen ← propTypes openT
  let pClosed ← propTypes closedT
  unless pOpen.size == 3 && pClosed.size == 2 do
    throwError "{closed}: {pClosed.size} proposition binders ({openN}: {pOpen.size}), expected 2 and 3"
  let headsOk ← forallTelescope closedT fun xs _ => do
    let mut props : Array Lean.Expr := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then props := props.push ty
    if props.size == 2 then
      let p0 := props[0]!
      let p1 := props[1]!
      if p0.isAppOf ``Tools.ShippingEntrySoundness.RunsTo &&
          p1.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
        isDefEq (p1.getArg! 4) (toExpr f)
      else
        pure false
    else
      pure false
  unless headsOk do
    throwError "{closed}: its proposition binders are not (RunsTo …, MachineDefines … {f} …)"
  -- the premise lists
  let (linesO, badO) ← Tests.Compiler.NoPortsTest.premiseLines openN
  let (linesC, badC) ← Tests.Compiler.NoPortsTest.premiseLines closed
  logInfo m!"{String.intercalate "\n" linesO.toList}"
  logInfo m!"{String.intercalate "\n" linesC.toList}"
  unless badO.size == 1 do
    throwError "{openN}: {badO.size} premises NOT ALLOWED, expected exactly 1 (MachineClosesAt {f}):\n{String.intercalate "\n" badO.toList}"
  unless badC.isEmpty do
    throwError "{closed}: {badC.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" badC.toList}"
  unless linesC.size + 1 == linesO.size do
    throwError "{closed}: {linesC.size} premises listed against {linesO.size} of {openN}, expected one fewer"
  let innerC ← forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  unless innerC.size == 1 do
    throwError "{closed}: {innerC.size} antecedents under the existentials, expected 1 (ChildBnd): {innerC.map (·.1)}"
  -- the gap theorem
  let gaps ← gapsOf gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  -- what the statements are relative to
  let baseN := if hasSv0 then f ++ `machine_design_sv0 else f ++ `machine_ships_hier
  unless env.contains baseN do throwError "{baseN}: not in the imports (the inventory is wrong)"
  let baseT := (← getConstInfo baseN).type
  let asked : List Name :=
    if hasSv0 then
      [``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingMachineShipsHier.kidsMem,
       ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSVBack.outsCheck,
       ``Tools.ShippingMachineEntry.MachineCloses]
    else
      [``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingMachineShipsHier.kidsMem,
       ``Tools.ShippingMachineEntry.MachineCloses]
  for k in asked do
    unless mentions baseT k do throwError "{baseN}: does not mention {k} (the inventory is wrong)"
  if mentions baseT ``Tools.ShippingChildInv.ChildBnd then
    throwError "{baseN}: asks ChildBnd already (the report says it is ADDED)"
  if !hasSv0 && env.contains (f ++ `machine_design_sv0) then
    throwError "{f}: {f}.machine_design_sv0 EXISTS — the report says there is no design-level base"
  -- the source of a transported endpoint
  let srcD := f ++ `machineSourceDecl
  if transported then
    unless env.contains srcD do throwError "{srcD}: missing — {f} is not transported"
    for (n, t) in [(openN, openT), (closed, closedT)] do
      unless mentions t srcD do throwError "{n}: does not read the declaration's source {srcD}"
      if mentions t (f ++ `machineSource) then throwError "{n}: reads the rewritten source"
  else if env.contains srcD then
    logInfo m!"NOPORTS MEM GEN AUDIT {f}: {srcD} EXISTS although the file says {f} is not transported (LOGGED, not asserted; the command's own log line says which it is)"
  let trS : String := if transported then "transported" else "not transported"
  logInfo m!"NOPORTS MEM GEN AUDIT {f}: GENERATED by #machine_no_ports_mem ({nMems} distinct placeholder(s), {trS}); {openN}, {closed}, {gap} and {(lemmas f nMems).length} lemmas {f}.noPortsMem_* on standard axioms. {openN}: {linesO.size} premises listed, 1 NOT ALLOWED (MachineClosesAt {f}); {closed}: {linesC.size} premises listed, 0 NOT ALLOWED — the run, MachineDefines {f}, and ONE antecedent under the existentials (ChildBnd). {cl}: NO premise. {gap}: NO gap hypothesis. No statement mentions a checker constant or MachineCloses, while {baseN} mentions {asked}. Nothing new is removed: these are the statements of the BUILT hand tests, produced by the command (their isDefEq with the hand statements is NOT checked here — the hand tests are not in this closure; Tests.Compiler.NoPortsMemGenCompareTest checks it for memCounter)."

end Tests.Compiler.NoPortsMemGenFamilyTest

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemGenFamilyTest.audit
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter 1 true false
  Tests.Compiler.NoPortsMemGenFamilyTest.audit
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow 1 true false
  Tests.Compiler.NoPortsMemGenFamilyTest.audit
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide 1 true false
  Tests.Compiler.NoPortsMemGenFamilyTest.audit
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems 1 true false
  Tests.Compiler.NoPortsMemGenFamilyTest.audit
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems 2 true false
  Tests.Compiler.NoPortsMemGenFamilyTest.audit
    ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory 1 false true

/-! ## The refused declarations left nothing -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let refused : List Lean.Name :=
    [``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem,
     ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
     ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
     ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH]
  let env ← Lean.getEnv
  for f in refused do
    for s in ["noPortsMem_entry", "noPortsMem_data", "noPortsMem_closes",
        "machine_design_noPortsR0", "machine_design_noPortsR0_closed"] do
      if env.contains (f ++ Lean.Name.mkSimple s) then
        throwError "{f}: {s} exists — it was not refused (or a hand test is in the imports)"
  Lean.logInfo m!"NOPORTS MEM GEN FAMILY: GENERATED (six): memCounter, syncNarrow, memWide, twoMems (one placeholder each; twoMems two entries of it), mixedMems (two placeholders: both read kinds), withMemory (transported). REFUSED with reasons (logged above), nothing added: {refused}. Nothing new is removed for any declaration: the same statements as the BUILT hand tests, by command. TARGET-ONLY: this file creates the hand tests' endpoint names."
