import Tests.Compiler.NoPortsMemOnlyAtLib
import Tests.Compiler.NoPortsMemSeqMemClosedTest
import Tools.ShippingMemOnlyCloses
import Tools.ShippingNameSep

/-! # Memory-only parents: the closed depth-0 endpoint — shared data log, closing call and audit (round par/a-19)

Used by the five tests `Tests/Compiler/NoPortsMemOnlyClosed<Decl>Test.lean`
(`memCounter`, `syncNarrow`, `twoMems`, `mixedMems`, `memWide`). Nothing here
is a theorem; the general theorem is
`Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly`.

`closeLast`, `gapsOf`, `propBinders` are IMPORTED from
`Tests.Compiler.NoPortsMemSeqMemClosedTest` (BUILT at 710ed31f), not copied.

## What the closed endpoint is relative to

`f.machine_design_noPortsR0_closed` is `f.machine_design_noPortsR0` (BUILT at
4bd77170, `NoPortsMemOnlyAt<Decl>Test`) with its last binder
`MachineClosesAt f` discharged by `f_closes`, which has NO premise.

There is NO base closed endpoint for a memory-only parent (no
`f.machine_design_svR0`, no `…_closed` of `f.machine_design_sv0`). The closed
endpoint is a NEW statement. Against `f.machine_design_sv0`:

1. absent: `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0`;
2. the boundary `True` is `ChildBnd mref cref w` (an ADDED antecedent, of the
   run's start world);
3. the all-worlds premise `MachineCloses f` is gone, and nothing is in its
   place: the at-form closing is PROVED (`f_closes`), not asked;
4. the run and `MachineDefines f` stay.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.NoPortsMemOnlyClosed
open Lean Meta Elab Command

/-- The reader's data the closing relies on, LOGGED first, then asserted:
every call entry one of the placeholders `mems`; four argument `let`s and the
field `out` per entry; no two entries with one callee and one argument list;
no output starting with `i`; the open endpoint present, no closed one. -/
def logData (f : Name) (mems : List Name) : MetaM Unit := do
  let rf ← Tools.ShippingMachineCommand.readMachine f
  let fe := rf.shape.insts.map (·.1)
  let args := rf.shape.insts.map (·.2.1)
  let outs := rf.shape.layout.outs.map (·.name)
  let memNames := mems.map fun m =>
    ((Sparkle.Compiler.MachMemory.memChild? m).map fun md => md.1.name).getD "(not a placeholder)"
  logInfo m!"MEMONLY CLOSED DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {fe}, argument lets {args}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {outs}; the placeholders expected {mems}, their modules' names {memNames}"
  if fe.isEmpty then throwError "{f}: no call entry"
  for e in fe do
    unless mems.contains e do
      throwError "{f}: the call entries are {fe}; {e} is none of {mems}"
  for m in mems do
    unless fe.contains m do
      throwError "{f}: the call entries are {fe}; the placeholder {m} is not among them"
    if (Sparkle.Compiler.MachMemory.memChild? m).isNone then
      throwError "{f}: {m} is not a memory placeholder"
  for a in args do
    unless a.length == 4 do
      throwError "{f}: an entry has the argument lets {a}, not 4 (hargsN is false)"
  unless rf.shape.instFields.length == fe.length do
    throwError "{f}: instFields={rf.shape.instFields} against {fe.length} entries (hfield is false: getD reads \"\")"
  for fld in rf.shape.instFields do
    unless fld == "out" do
      throwError "{f}: instFields={rf.shape.instFields}; {fld} is not out (hfield is false)"
  let keys := (fe.zip args).map fun p => (p.1.toString, p.2)
  let mut seen : List (String × List Nat) := []
  for k in keys do
    if seen.contains k then
      throwError "{f}: two entries of one callee with one argument list {k.2} (hargsNd is FALSE: STOP, report the statement)"
    seen := seen ++ [k]
  for o in outs do
    if o.toList.head? == some 'i' then
      throwError "{f}: the output {o} starts with 'i' — hout is false (hfresh is not decided by the first character)"
  let env ← getEnv
  for n in [f ++ `machine_design_noPortsR0, f ++ `machine_design_sv0, f ++ `machineData,
      f ++ `machine_ok, f ++ `machine_body] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_design_noPortsR0_closed, f ++ `machine_design_noPortsR0_closed_gap] do
    if env.contains n then throwError "{n}: exists already"

/-- `f.machine_design_noPortsR0_closed`: the open endpoint with its last
binder `MachineClosesAt f` discharged by the premise-free theorem `cl`
(the imported `closeLast`). -/
def closeIt (f cl : Name) : MetaM Name := do
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemSeqMemClosedTest.closeLast f openN cl closed
  return closed

/-- Are the proposition binders of `stmt`, in order, applications of the
constants `heads` — a `MachineDefines` one being of the declaration `f`
(its fifth argument)? Decided under the binders of `stmt`. -/
def allPropsOk (stmt : Lean.Expr) (f : Name) (heads : List Name) : MetaM Bool :=
  forallTelescope stmt fun xs _ => do
    let mut props : Array Lean.Expr := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then props := props.push ty
    unless props.size == heads.length do return false
    let mut ok := true
    let mut i : Nat := 0
    for h in heads do
      let p := props[i]!
      if h == ``Tools.ShippingMachineEntry.MachineDefines then
        unless p.isAppOfArity h 6 do ok := false
        if p.isAppOfArity h 6 then
          unless ← isDefEq (p.getArg! 4) (toExpr f) do ok := false
      else
        unless p.isAppOf h do ok := false
      i := i + 1
    return ok

/-- The audit of `f.machine_design_noPortsR0_closed` and of its gap theorem
(an error on any failure):

* standard axioms of the general theorems, of `thms`, of `cl`, of the closed
  endpoint and of the gap theorem;
* `cl` has NO proposition premise and concludes `MachineClosesAt … f …`;
* the closed statement and the gap theorem mention no checker constant, no
  `MachineClosesAt`, no `MachineCloses`, no `ChildRanIn`; the open endpoint
  asks `MachineClosesAt`; the base `f.machine_design_sv0` asks `MachineCloses`
  and the four checks;
* the closed endpoint has exactly TWO proposition binders — the run
  (`RunsTo`) and `MachineDefines … f …` — printed as the first two of the open
  endpoint;
* under the existentials ONE antecedent, allowed, printed as the open
  endpoint's, and it is `ChildBnd`;
* the premise list by the goal-gap classifier: 0 NOT ALLOWED, one line fewer
  than the open endpoint's (which has exactly one NOT ALLOWED);
* the gap theorem has no gap hypothesis. -/
def auditClosed (f cl : Name) (thms : List Name) : MetaM Unit := do
  let old := f ++ `machine_design_sv0
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  let gap := f ++ `machine_design_noPortsR0_closed_gap
  -- (a) standard axioms
  for n in [``Tools.ShippingMemCloses.closeInstsGM_run_allM,
      ``Tools.ShippingMemCloses.memIface,
      ``Tools.ShippingMemCloses.memKid_iface,
      ``Tools.ShippingMemCloses.machineClosesAt_of_kidsDM,
      ``Tools.ShippingMemOnlyCloses.memNameAt_eq,
      ``Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly,
      ``Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData,
      ``Tools.ShippingMemOnlyCloses.sep_of_one,
      ``Tools.ShippingMemOnlyCloses.parent_of_one] ++ thms ++ [cl, openN, closed, gap] do
    unless (← getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the closing theorem: NO proposition premise; it concludes the closing of `f`
  let clT := (← getConstInfo cl).type
  let clB ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders clT
  unless clB.isEmpty do
    throwError "{cl}: {clB.size} proposition premise(s), expected none: {clB}"
  let clOk ← forallTelescope clT fun _ body => do
    if body.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 then
      isDefEq (body.getArg! 4) (toExpr f)
    else
      pure false
  unless clOk do throwError "{cl}: does not conclude MachineClosesAt of {f}:{indentExpr clT}"
  -- (c) the statements
  let oldT := (← getConstInfo old).type
  let openT := (← getConstInfo openN).type
  let closedT := (← getConstInfo closed).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt (the inventory is wrong)"
  unless (oldT.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome do
    throwError "{old}: does not ask MachineCloses (the report says the base asks the all-worlds form)"
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsHier.kidsMem, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  if (oldT.find? (·.isConstOf ``Tools.ShippingChildInv.ChildBnd)).isSome then
    throwError "{old}: asks ChildBnd already (the report says it is ADDED)"
  for n in [closed, gap] do
    let t := (← getConstInfo n).type
    for k in Tests.Compiler.NoPortsTest.checkers ++ Tests.Compiler.NoPortsMemOnly.forbiddenMem do
      if (t.find? (·.isConstOf k)).isSome then throwError "{n}: the statement mentions {k}"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{n}: asks MachineClosesAt"
    if (t.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome then
      throwError "{n}: asks MachineCloses"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.ChildRanIn)).isSome then
      throwError "{n}: mentions ChildRanIn"
  unless (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.ChildBnd)).isSome do
    throwError "{closed}: does not mention ChildBnd (the report says it is the one antecedent)"
  -- (d) the binders: exactly the run and the reflection of `f`
  let bOpen ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders openT
  let bClosed ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders closedT
  logInfo m!"MEMONLY CLOSED BINDERS {openN}: {bOpen}"
  logInfo m!"MEMONLY CLOSED BINDERS {closed}: {bClosed}"
  unless bOpen.size == 3 && bClosed.size == 2 do
    throwError "{closed}: {bClosed.size} proposition binders ({openN}: {bOpen.size}), expected 2 and 3:\n{bClosed}\nvs\n{bOpen}"
  unless bClosed[0]! == bOpen[0]! && bClosed[1]! == bOpen[1]! do
    throwError "{closed}: its proposition binders are not the first two of {openN}:\n{bClosed}\nvs\n{bOpen}"
  let headsOk ← allPropsOk closedT f
    [``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingMachineEntry.MachineDefines]
  unless headsOk do
    throwError "{closed}: its proposition binders are not (RunsTo …, MachineDefines … {f} …):\n{bClosed}"
  -- (e) under the existentials: ONE antecedent, allowed, the open form's
  let innerOpen ← forallTelescope openT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let inner ← forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  logInfo m!"MEMONLY CLOSED ANTECEDENTS {openN}: {innerOpen.size} — {innerOpen.map (·.1)}"
  logInfo m!"MEMONLY CLOSED ANTECEDENTS {closed}: {inner.size} — {inner.map (·.1)}"
  unless inner.size == 1 && innerOpen.size == 1 do
    throwError "{closed}: expected ONE antecedent under the existentials (and one in {openN}): {inner.map (·.1)} vs {innerOpen.map (·.1)}"
  unless inner[0]!.2 do
    throwError "{closed}: its antecedent is NOT ALLOWED: {inner[0]!.1}"
  unless inner[0]!.1 == innerOpen[0]!.1 do
    throwError "{closed}: its antecedent {inner[0]!.1} is not the open form's {innerOpen[0]!.1}"
  -- (f) the complete premise list: 0 NOT ALLOWED, one line fewer than the open form
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  let (linesOpen, badOpen) ← Tests.Compiler.NoPortsTest.premiseLines openN
  unless badOpen.size == 1 do
    throwError "{openN}: {badOpen.size} premises NOT ALLOWED, expected exactly 1 (MachineClosesAt {f})"
  unless lines.size + 1 == linesOpen.size do
    throwError "{closed}: {lines.size} premises listed against {linesOpen.size} of {openN}, expected one fewer"
  -- (g) the gap theorem: no gap hypothesis
  let gaps ← Tests.Compiler.NoPortsMemSeqMemClosedTest.gapsOf gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  logInfo m!"MEMONLY CLOSED AUDIT {f}: {closed} and {gap} on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly (a corollary of Tools.ShippingMemCloses.machineClosesAt_of_kidsDM with the child interface discharged by memKid_iface) and the hand lemmas {thms}. {cl} has NO proposition premise. Against {openN} ({linesOpen.size} premises listed, {badOpen.size} NOT ALLOWED: MachineClosesAt {f}) the closed endpoint has {lines.size} premises listed, 0 NOT ALLOWED: the run, MachineDefines {f}, and under the existentials ONE antecedent, ChildBnd of the run's start world. {gap}: NO gap hypothesis. No checker constant, no MachineClosesAt, no MachineCloses, no ChildRanIn in the statements. RELATIVE TO: there is NO base closed endpoint of a memory-only parent; this is a NEW statement — against {old}: the four checks (shipsHierCheck, kidsMem, designCheck 0, outsCheck 0) absent, the boundary True is ChildBnd (ADDED), the all-worlds premise MachineCloses {f} is gone with nothing in its place (the at-form closing is proved, not asked). SCOPE: one declaration, a memory-only parent with register slots, depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. The run, the reflection of {f} and ChildBnd remain premises. NOT covered: a generator, depth ≥ 1, a memory entry beside a shared descendant."

end Tests.Compiler.NoPortsMemOnlyClosed
