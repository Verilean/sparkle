import Tests.Compiler.NoPortsMemOnlyClosedLib
import Tools.ShippingMemTransport

/-! # A memory-only parent with a TRANSPORTED endpoint: data log, at-form generator and audits (round par/b-17)

For `withMemory` (`Tests/Compiler/ShippingMachineFuseTest.lean` 42–51): the
one memory declaration whose endpoint is transported (its nested loops are
fused; `Tools/ShippingMemTransport.lean` says what the transport is). The
built at-form generator `Tests.Compiler.NoPortsMemOnly.generateM0`
(`Tests/Compiler/NoPortsMemOnlyCounterTest.lean` 223–316) refuses it at 276.

## Why it refuses, and what differs (READ)

`generateM0 (atForm := true)` reads the data arguments of
`f.machine_composedT` by `lambdaTelescope ct.value` expecting 11 binders over
`machine_linkedT_mem` on 21 arguments (288–299). For a transported parent
the value is `Eq.mpr _ _ (congrArg motive heq) (fun … => machine_linkedT_mem …)`
(`Tools/ShippingMachineMemCommand.lean` 93–98): an application, not a
lambda — 0 binders. And the composed theorem it would build from the `RA`
twin is about the REWRITTEN source `f.machineSource`, while the `src`
argument of `f.machine_ships_hier` (position 14, passed on to the head by
`finishM0`) is the declaration's `f.machineSourceDecl`. Nothing else
differs: the head `machine_design_noPorts` has separate `src` (composed
theorem) and `srcL` (wired endpoint, "its source may be the fused /
sign-normalised one a transported endpoint rewrites",
`Tools/ShippingNoPorts.lean` 66–67), the wired `RA` twin is applied to the
UNTRANSPORTED arguments (as `generateWith` does,
`Tools/ShippingMachineShipsHierCommand.lean` 50–54), and the four run
hypotheses speak of the reader's data only.

## `generateT0`

The at-form branch of `generateM0` with those two points handled: the data
arguments are read under the `Eq.mpr`, and the composed theorem is moved to
the declaration's source by `Tools.ShippingMemTransport.composedG_src` at
the endpoint's own equation. REUSED by import, not copied: `finishM0` (the
head's application and the four discharges), `forbiddenMem`. RESTATED here
(they are inside `generateM0`'s body and cannot be imported): the checks on
`f.machine_ships_hier` (24 arguments, `ResetM`, `kidsMem`, boundary `True`)
and the at-form assembly of the wired endpoint and the composed theorem.
For an untransported parent it builds what `generateM0 (atForm := true)`
builds (NOT run on one here: the five names exist already).

## The audits

`withMemory` has NO design-level base endpoint (`#machine_design_sv0
withMemory` was never run), so the audits of `NoPortsMemOnlyAtLib` /
`NoPortsMemOnlyClosedLib` (which compare with `f.machine_design_sv0`) do
not apply. `auditOpen` / `auditClosed` compare with `f.machine_ships_hier`
and assert what each side mentions; the differences are listed in the test.

Nothing here is a theorem about the compiler.

WRITTEN, NOT BUILT (par/b-17). -/
namespace Tests.Compiler.NoPortsMemWithMemory
open Lean Meta Elab Command

/-- The reader's data of a memory-only parent and the shape of its endpoints,
LOGGED first, then asserted. -/
def logData (f : Name) (nDecl : Nat) (mems : List Name) : MetaM Unit := do
  let rf ← Tools.ShippingMachineCommand.readMachine f
  let fe := rf.shape.insts.map (·.1)
  let args := rf.shape.insts.map (·.2.1)
  let outs := rf.shape.layout.outs.map (·.name)
  let env ← getEnv
  let mut have_ : List Name := []
  let mut lack : List Name := []
  for s in [`machineData, `machine_ok, `machine_body, `machine_sound, `machineSource,
      `machineSourceDecl, `machine_composedT, `machine_closes, `machine_ships_hier,
      `machine_ships_hierR, `machine_design_sv0, `machine_design_svR0,
      `machine_design_noPorts0, `machine_design_noPortsR0, `machine_design_noPortsR0_closed] do
    if env.contains (f ++ s) then have_ := have_ ++ [s] else lack := lack ++ [s]
  logInfo m!"WITHMEMORY DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, slots={rf.shape.layout.slots.length}, loops={rf.shape.loops.length}, runs empty={rf.shape.runs.isEmpty}, call entries {fe}, instFields={rf.shape.instFields}, argument lets {args}, lets={rf.shape.layout.lets}, outputs {outs}; the memory placeholders expected {mems}; constants present {have_}; absent {lack}"
  -- the endpoint's shape: its wired twin's head, its transport
  let (headL, eargs, back?) ← Tools.ShippingMachineSeqCommand.endpointParts f
  let tr ← (match back? with
    | Option.some p => do
      let t ← inferType p.1
      pure m!"TRANSPORTED along{indentExpr t}\n(the rewritten source:{indentExpr p.2}\n)"
    | Option.none => pure m!"NOT transported")
  logInfo m!"WITHMEMORY ENDPOINT {f}: the wired twin's head {headL} on {eargs.size} arguments; {tr}"
  for s in [`machine_composedT, `machine_ships_hier] do
    match env.find? (f ++ s) with
    | Option.some (ConstantInfo.thmInfo ti) =>
      let v := ti.value
      let nB ← lambdaTelescope v fun ys _ => pure ys.size
      let hd : Name := v.getAppFn.constName?.getD Name.anonymous
      logInfo m!"WITHMEMORY ENDPOINT {f ++ s}: the proof term's head {hd}, {v.getAppNumArgs} arguments, {nB} leading binders"
    | _ => logInfo m!"WITHMEMORY ENDPOINT {f ++ s}: not a theorem of the imports"
  -- asserted
  unless rf.nDecl == nDecl do
    throwError "{f}: nDecl = {rf.nDecl}, the hand theorems are written for {nDecl}"
  if fe.isEmpty then throwError "{f}: no call entry"
  for e in fe do
    unless mems.contains e do
      throwError "{f}: the call entries are {fe}; {e} is none of {mems}"
  for m in mems do
    unless fe.contains m do
      throwError "{f}: the call entries are {fe}; the placeholder {m} is not among them"
    if (Sparkle.Compiler.MachMemory.memChild? m).isNone then
      throwError "{f}: {m} is not a memory placeholder"
  if rf.shape.instFields.isEmpty then throwError "{f}: instFields = [] — not the general closing"
  if rf.shape.layout.slots.isEmpty then
    throwError "{f}: NO REGISTER SLOT — hsl : d.shape.layout.slots ≠ [] of kidsM_runFacts / kidsM_designCheck fails; nothing below applies"
  -- the closing's data (`machineClosesAt_memOnly`)
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
      throwError "{f}: the output {o} starts with 'i' — hout is false"
  for n in [f ++ `machine_ships_hier, f ++ `machine_composedT, f ++ `machine_sound,
      f ++ `machineData, f ++ `machine_ok, f ++ `machine_body] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_design_noPortsR0, f ++ `machine_design_noPortsR0_closed,
      f ++ `machine_design_noPortsR0_closed_gap] do
    if env.contains n then throwError "{n}: exists already"

/-- **`f.machine_design_noPortsR0` of a memory-only parent whose endpoint may
be transported**: the head `machine_design_noPorts` at `n = 0` on the
arguments of `f.machine_ships_hier`, closing predicate `MachineClosesAt`,
boundary `ChildBnd` in place of the old `True`; the wired endpoint is the
`RA` twin of the endpoint's head on its UNTRANSPORTED arguments (about the
rewritten source, the head's `srcL`); the composed theorem is
`machine_linkedT_mem` on it with the data arguments of the existing
`f.machine_composedT` — read under its `Eq.mpr` when the endpoint is
transported — and is then moved to the declaration's source by
`composedG_src` at the endpoint's own equation. The four run hypotheses are
discharged by `Tests.Compiler.NoPortsMemOnly.finishM0` (imported). -/
def generateT0 (f : Name) (facts outs mem design : Name) : MetaM Name := do
  let ships := f ++ `machine_ships_hier
  let name := f ++ `machine_design_noPortsR0
  if (← getEnv).contains name then throwError "{name}: exists already"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_ships_hier first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hier do
    throwError "{ships}: not built from machine_ships_hier"
  let a := v.getAppArgs
  unless a.size == 24 do
    throwError "{ships}: {a.size} arguments of machine_ships_hier, expected 24"
  unless a[3]!.isConstOf ``Tools.ShippingMachineShipsHier.ResetM do
    throwError "{ships}: its reset is{indentExpr a[3]!}\nnot ResetM — not the memory route"
  unless (a[5]!.find? (·.isConstOf ``Tools.ShippingMachineShipsHier.kidsMem)).isSome do
    throwError "{ships}: its child bound is{indentExpr a[5]!}\nnot kidsMem — not the memory route"
  -- the new boundary, over the old boundary's own binders; the old one must be `True`
  let bndNew ← lambdaTelescope a[4]! fun bs oldB => do
    unless bs.size == 7 do
      throwError "{ships}: its boundary has {bs.size} binders, expected 7:{indentExpr a[4]!}"
    unless oldB.isConstOf ``True do
      throwError "{ships}: the old boundary is{indentExpr oldB}\nnot True (this generator replaces True by ChildBnd and nothing else)"
    mkLambdaFVars bs (← mkAppM ``Tools.ShippingChildInv.ChildBnd #[bs[1]!, bs[3]!, bs[4]!])
  -- the endpoint: its wired twin's head, its UNTRANSPORTED arguments, its transport
  let (headL, eargs, back?) ← Tools.ShippingMachineSeqCommand.endpointParts f
  let headA := headL.appendAfter "RA"
  unless (← getEnv).contains headA do throwError "{f}: no head {headA}"
  let pLA := mkAppN (mkConst headA) eargs
  -- the data arguments of the existing composed theorem, under its transport
  let some (.thmInfo ct) := (← getEnv).find? (f ++ `machine_composedT)
    | throwError "{f}: no machine_composedT"
  let mut cv := ct.value
  if cv.isAppOfArity ``Eq.mpr 4 then
    if back?.isNone then
      throwError "{f}.machine_composedT is transported, {f}.machine_sound is not"
    cv := cv.getAppArgs[3]!
  else if back?.isSome then
    throwError "{f}.machine_sound is transported, {f}.machine_composedT is not an Eq.mpr on 4 arguments"
  let rest ← lambdaTelescope cv fun ys body => do
    unless ys.size == 11 do
      throwError "{f}.machine_composedT: {ys.size} binders under its transport, expected 11"
    unless body.isAppOfArity ``Tools.ShippingMachineMemLinked.machine_linkedT_mem 21 do
      throwError "{f}.machine_composedT: not machine_linkedT_mem on 21 arguments"
    let rest := body.getAppArgs.extract 11 21
    for r in rest do
      if r.hasAnyFVar (fun id => ys.any (·.fvarId! == id)) then
        throwError "{f}.machine_composedT: a data argument depends on the run"
    pure rest
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let cT ← instantiateMVars (← inferType xs[10]!)
    unless cT.isAppOfArity ``Tools.ShippingMachineEntry.MachineCloses 6 do
      throwError "{ships}: its closing premise is{indentExpr cT}\nnot MachineCloses"
    let atT := mkAppN (mkConst ``Tools.ShippingChildInv.MachineClosesAt) cT.getAppArgs
    let C ← mkLambdaFVars #[xs[0]!, xs[1]!, xs[2]!, xs[3]!] atT
    -- the wired endpoint under `MachineClosesAt` and `ChildBnd` (the rewritten source)
    let soundL ← forallTelescope (← inferType pLA) fun zs _ => do
      unless zs.size == 12 do
        throwError "{f}: {headA} has {zs.size} binders after its data, expected 12"
      mkLambdaFVars zs
        (← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[mkAppN pLA zs])
    -- the composed theorem, moved to the declaration's source
    let composed ← forallTelescope (← inferType pLA) fun zs _ => do
      let hNew ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[mkAppN pLA zs]
      let linked ← mkAppM ``Tools.ShippingMachineMemLinked.machine_linkedT_mem (#[hNew] ++ rest)
      let memF ← mkAppM ``Tools.ConeFold.memFree
        #[← mkAppM ``Sparkle.IR.AST.Module.body #[zs[6]!]]
      withLocalDeclD `hm memF fun hm => do
        let cg0 ← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_Tmem #[linked, hm]
        let cg ← (match back? with
          | Option.some p => mkAppM ``Tools.ShippingMemTransport.composedG_src #[cg0, p.1]
          | Option.none => pure cg0)
        mkLambdaFVars (zs.push hm) cg
    withLocalDeclD `closes atT fun cl =>
      Tests.Compiler.NoPortsMemOnly.finishM0 f a bndNew C soundL composed (xs.pop.push cl) cl
        facts outs mem design
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in Tests.Compiler.NoPortsMemOnly.forbiddenMem do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  -- a transported endpoint: the statement is about the declaration's source
  if let some (_, srcN) := back? then
    if (type.find? (· == srcN)).isSome then
      throwError "{name}: REFUSED, the statement reads the rewritten source{indentExpr srcN}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- Does the statement `t` mention the constant `c`? -/
def mentions (t : Lean.Expr) (c : Name) : Bool :=
  (t.find? (·.isConstOf c)).isSome

/-- The audit of `f.machine_design_noPortsR0` against `f.machine_ships_hier`
(an error on any failure):

* standard axioms of `composedG_src`, of the `memOnly_*` theorems, of
  `thms` and of the endpoint; no closed form exists;
* the endpoint's statement mentions no checker constant; it mentions
  `DesignSV`, `ChildBnd`, `MachineClosesAt` and not `MachineCloses`;
* `f.machine_ships_hier` mentions `shipsHierCheck`, `kidsMem`,
  `MachineCloses`, and none of `MachineClosesAt`, `ChildBnd`, `DesignSV`,
  `designCheck`, `outsCheck`; one of its antecedents prints `True`;
* a transported `f`: both statements mention `f.machineSourceDecl` and
  neither `f.machineSource`;
* three proposition binders, the last `MachineClosesAt … f f.machineData.shape`;
  the goal-gap classifier lists EXACTLY ONE premise NOT ALLOWED;
* under the existentials ONE antecedent, allowed.

LOGGED: both premise lists, both binder lists, whether a design-level base
`f.machine_design_sv0` is in the environment. -/
def auditOpen (f : Name) (thms : List Name) : MetaM Unit := do
  let base := f ++ `machine_ships_hier
  let openN := f ++ `machine_design_noPortsR0
  let dataN := f ++ `machineData
  for n in [``Tools.ShippingMemTransport.composedG_src,
      ``Tools.ShippingMemOnly.memOnly_runFacts, ``Tools.ShippingMemOnly.memOnly_outsCheck,
      ``Tools.ShippingMemOnly.memOnly_kidsMem, ``Tools.ShippingMemOnly.memOnly_designCheck,
      ``Tools.ShippingNoPorts.machine_design_noPorts] ++ thms ++ [base, openN] do
    unless (← getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  for s in [`machine_design_noPortsR0_closed, `machine_design_noPortsR0_closed_gap] do
    if (← getEnv).contains (f ++ s) then
      throwError "{f ++ s}: a closed form EXISTS — this audit states that MachineClosesAt is still a premise"
  let openT := (← getConstInfo openN).type
  let baseT := (← getConstInfo base).type
  for k in Tests.Compiler.NoPortsTest.checkers ++ Tests.Compiler.NoPortsMemOnly.forbiddenMem do
    if mentions openT k then throwError "{openN}: the statement mentions {k}"
  for k in [``Tools.ShippingDesignSV.DesignSV, ``Tools.ShippingChildInv.ChildBnd,
      ``Tools.ShippingChildInv.MachineClosesAt] do
    unless mentions openT k do throwError "{openN}: does not mention {k}"
  if mentions openT ``Tools.ShippingMachineEntry.MachineCloses then
    throwError "{openN}: mentions MachineCloses (the all-worlds form)"
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsHier.kidsMem, ``Tools.ShippingMachineEntry.MachineCloses] do
    unless mentions baseT k do throwError "{base}: does not mention {k} (the inventory is wrong)"
  for k in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildBnd,
      ``Tools.ShippingDesignSV.DesignSV, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    if mentions baseT k then
      throwError "{base}: mentions {k} (the list of differences in the report is wrong)"
  -- the source both statements are about
  let srcD := f ++ `machineSourceDecl
  let srcF := f ++ `machineSource
  if (← getEnv).contains srcD then
    for (n, t) in [(base, baseT), (openN, openT)] do
      unless mentions t srcD do throwError "{n}: does not read the declaration's source {srcD}"
      if mentions t srcF then throwError "{n}: reads the rewritten source {srcF}"
  else
    logInfo m!"WITHMEMORY AUDIT {f}: no {srcD} — the endpoint is not transported"
  -- the binders
  let bBase ← Tests.Compiler.NoPortsMemOnly.propBinders baseT
  let bOpen ← Tests.Compiler.NoPortsMemOnly.propBinders openT
  logInfo m!"WITHMEMORY BINDERS {base}: {bBase}"
  logInfo m!"WITHMEMORY BINDERS {openN}: {bOpen}"
  unless bOpen.size == 3 do
    throwError "{openN}: {bOpen.size} proposition binders, expected 3 (the run, MachineDefines, MachineClosesAt)"
  let lastOk ← forallTelescope openT fun xs _ => do
    let t ← instantiateMVars (← inferType xs.back!)
    pure (t.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && t.getArg! 4 == toExpr f &&
      ((t.getArg! 5).find? (·.isConstOf dataN)).isSome)
  unless lastOk do
    throwError "{openN}: its last binder is not MachineClosesAt of {f} at {dataN}"
  -- the antecedents under the existentials
  let inner ← forallTelescope openT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerBase ← forallTelescope baseT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  logInfo m!"WITHMEMORY ANTECEDENTS {base}: {innerBase.size} — {innerBase.map (·.1)}"
  logInfo m!"WITHMEMORY ANTECEDENTS {openN}: {inner.size} — {inner.map (·.1)}"
  unless inner.size == 1 do
    throwError "{openN}: {inner.size} antecedents under the existentials, expected 1 (ChildBnd): {inner.map (·.1)}"
  unless inner[0]!.2 do throwError "{openN}: its antecedent is NOT ALLOWED: {inner[0]!.1}"
  unless innerBase.any (fun x => x.1 == "True") do
    throwError "{base}: no antecedent printed True (the report says its boundary is True): {innerBase.map (·.1)}"
  -- the complete premise list: exactly one NOT ALLOWED
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines openN
  logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.size == 1 do
    throwError "{openN}: the classifier lists {bad.size} premises NOT ALLOWED, expected exactly 1:\n{String.intercalate "\n" bad.toList}"
  let hasSv0 : String := if (← getEnv).contains (f ++ `machine_design_sv0) then "yes" else "no"
  logInfo m!"WITHMEMORY AUDIT {f}: {openN} on standard axioms, by the head machine_design_noPorts at depth 0, the memOnly_* theorems at {f}'s data, composedG_src and the hand lemmas {thms}. It is a NEW statement; {f} has no design-level base endpoint ({f}.machine_design_sv0 in the environment: {hasSv0}). Against {base}: (1) the conclusion is DesignSV of the module list at depth 0 (a closed run exists and every closed run shows the source), where {base} concludes a stateful linked run of the shipped IR module — {base} does not mention DesignSV; (2) {base}'s antecedents ({innerBase.size}: shipsHierCheck, its boundary True, kidsMem) are replaced by ONE, ChildBnd of the run's start world (ADDED); (3) the closing binder is MachineClosesAt {f} where {base} has the all-worlds MachineCloses {f} — STILL A PREMISE, the ONE premise NOT ALLOWED ({bad.size} by the classifier); (4) the run and MachineDefines {f} stay; (5) both read the declaration's source. SCOPE: one declaration, a memory-only parent with register slots, depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim."

/-- The audit of `f.machine_design_noPortsR0_closed` and of its gap theorem
(an error on any failure): standard axioms; `cl` has no proposition premise
and concludes `MachineClosesAt … f …`; the closed statement and the gap
theorem mention no checker constant, no `MachineClosesAt`, no
`MachineCloses`, no `ChildRanIn`; the closed endpoint's proposition binders
are the first two of the open endpoint's (the run, `MachineDefines … f …`);
ONE antecedent under the existentials, allowed, the open form's; the
classifier lists 0 premises NOT ALLOWED, one line fewer than the open
form's; no gap hypothesis; a transported `f`: the statement reads
`f.machineSourceDecl` and not `f.machineSource`. -/
def auditClosed (f cl : Name) (thms : List Name) : MetaM Unit := do
  let base := f ++ `machine_ships_hier
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  let gap := f ++ `machine_design_noPortsR0_closed_gap
  for n in [``Tools.ShippingMemCloses.machineClosesAt_of_kidsDM,
      ``Tools.ShippingMemCloses.memKid_iface,
      ``Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly,
      ``Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData,
      ``Tools.ShippingMemOnlyCloses.sep_of_one,
      ``Tools.ShippingMemOnlyCloses.parent_of_one,
      ``Tools.ShippingMemTransport.composedG_src] ++ thms ++ [cl, openN, closed, gap] do
    unless (← getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- the closing theorem: no proposition premise; it concludes the closing of `f`
  let clT := (← getConstInfo cl).type
  let clB ← Tests.Compiler.NoPortsMemOnly.propBinders clT
  unless clB.isEmpty do
    throwError "{cl}: {clB.size} proposition premise(s), expected none: {clB}"
  let clOk ← forallTelescope clT fun _ body => do
    if body.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 then
      isDefEq (body.getArg! 4) (toExpr f)
    else
      pure false
  unless clOk do throwError "{cl}: does not conclude MachineClosesAt of {f}:{indentExpr clT}"
  -- the statements
  let openT := (← getConstInfo openN).type
  let closedT := (← getConstInfo closed).type
  unless mentions openT ``Tools.ShippingChildInv.MachineClosesAt do
    throwError "{openN}: does not ask MachineClosesAt (the inventory is wrong)"
  for n in [closed, gap] do
    let t := (← getConstInfo n).type
    for k in Tests.Compiler.NoPortsTest.checkers ++ Tests.Compiler.NoPortsMemOnly.forbiddenMem ++
        [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses,
         ``Tools.ShippingChildInv.ChildRanIn] do
      if mentions t k then throwError "{n}: the statement mentions {k}"
  for k in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingDesignSV.DesignSV] do
    unless mentions closedT k do throwError "{closed}: does not mention {k}"
  let srcD := f ++ `machineSourceDecl
  if (← getEnv).contains srcD then
    unless mentions closedT srcD do throwError "{closed}: does not read the declaration's source {srcD}"
    if mentions closedT (f ++ `machineSource) then
      throwError "{closed}: reads the rewritten source"
  -- the binders: exactly the run and the reflection of `f`
  let bOpen ← Tests.Compiler.NoPortsMemOnly.propBinders openT
  let bClosed ← Tests.Compiler.NoPortsMemOnly.propBinders closedT
  logInfo m!"WITHMEMORY CLOSED BINDERS {openN}: {bOpen}"
  logInfo m!"WITHMEMORY CLOSED BINDERS {closed}: {bClosed}"
  unless bOpen.size == 3 && bClosed.size == 2 do
    throwError "{closed}: {bClosed.size} proposition binders ({openN}: {bOpen.size}), expected 2 and 3"
  unless bClosed[0]! == bOpen[0]! && bClosed[1]! == bOpen[1]! do
    throwError "{closed}: its proposition binders are not the first two of {openN}:\n{bClosed}\nvs\n{bOpen}"
  let headsOk ← Tests.Compiler.NoPortsMemOnlyClosed.allPropsOk closedT f
    [``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingMachineEntry.MachineDefines]
  unless headsOk do
    throwError "{closed}: its proposition binders are not (RunsTo …, MachineDefines … {f} …):\n{bClosed}"
  -- under the existentials: ONE antecedent, allowed, the open form's
  let innerOpen ← forallTelescope openT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let inner ← forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  logInfo m!"WITHMEMORY CLOSED ANTECEDENTS {closed}: {inner.size} — {inner.map (·.1)}"
  unless inner.size == 1 && innerOpen.size == 1 do
    throwError "{closed}: expected ONE antecedent under the existentials (and one in {openN}): {inner.map (·.1)} vs {innerOpen.map (·.1)}"
  unless inner[0]!.2 do throwError "{closed}: its antecedent is NOT ALLOWED: {inner[0]!.1}"
  unless inner[0]!.1 == innerOpen[0]!.1 do
    throwError "{closed}: its antecedent {inner[0]!.1} is not the open form's {innerOpen[0]!.1}"
  -- the complete premise list: 0 NOT ALLOWED, one line fewer than the open form
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  let (linesOpen, badOpen) ← Tests.Compiler.NoPortsTest.premiseLines openN
  unless badOpen.size == 1 do
    throwError "{openN}: {badOpen.size} premises NOT ALLOWED, expected exactly 1 (MachineClosesAt {f})"
  unless lines.size + 1 == linesOpen.size do
    throwError "{closed}: {lines.size} premises listed against {linesOpen.size} of {openN}, expected one fewer"
  -- the gap theorem: no gap hypothesis
  let gaps ← Tests.Compiler.NoPortsMemSeqMemClosedTest.gapsOf gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  logInfo m!"WITHMEMORY CLOSED AUDIT {f}: {closed} and {gap} on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly and the hand lemmas {thms}. {cl} has NO proposition premise. Against {openN} ({linesOpen.size} premises listed, {badOpen.size} NOT ALLOWED: MachineClosesAt {f}) the closed endpoint has {lines.size} premises listed, 0 NOT ALLOWED: the run, MachineDefines {f}, and under the existentials ONE antecedent, ChildBnd of the run's start world. {gap}: NO gap hypothesis. RELATIVE TO: {f} has NO design-level base endpoint; this is a NEW statement — against {base}: the conclusion is DesignSV of the module list at depth 0 instead of the shipped IR module's linked run; shipsHierCheck and kidsMem are absent; the boundary True is ChildBnd (ADDED); the all-worlds premise MachineCloses {f} is gone with nothing in its place (the at-form closing is proved, not asked). SCOPE: one declaration, a memory-only parent with register slots, depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. The run, the reflection of {f} and ChildBnd remain premises."

end Tests.Compiler.NoPortsMemWithMemory
