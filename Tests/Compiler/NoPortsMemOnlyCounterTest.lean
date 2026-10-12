import Tests.Compiler.NoPortsGrandHTest
import Tests.Compiler.ShippingDesignSVMemTest
import Tools.ShippingMemOnly

/-! # `memCounter` by hand: the depth-0 endpoint of a MEMORY-ONLY parent without the four check premises (G1, unit U4, round par/b-14)

`memCounter` (`Tests/Compiler/ShippingMachineMemLinkedTest.lean` 16–23, READ):

    def memCounter (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
        (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
      let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
        let addr := Signal.fst st
        let rd := Signal.memoryComboRead wa wd we addr
        bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : …))) (Signal.register 0#8 rd)
      Signal.snd st

Its design-level endpoint today is `memCounter.machine_design_sv0` (BUILT,
`Tests/Compiler/ShippingDesignSVTest.lean` 87): `ships_design_svN_all` at
depth 0 (`Tools/ShippingShipsDesignSVAll.lean` 30–98) over
`memCounter.machine_ships_hier`, which is `machine_ships_hier`
(`Tools/ShippingMachineShipsHier.lean` 324–414: `machine_ships_hierC` at
`C := MachineCloses`, the ALL-WORLDS closing) on the route `.mem`
(`Tools/ShippingMachineShipsHierCommand.lean` 40–43, 71–75, 86–98). Under its
existentials it asks, in this order,

    shipsHierCheck (childMap D.modules) b = true →
    designCheck (childMap D.modules) 0 (checkedOptimize b) = true →
    outsCheck (childMap D.modules) 0 (checkedOptimize b) = true →
    True →                                   -- the "old boundary" (see below)
    kidsMem (childMap D.modules) b.body = true → …

and its proposition binders are the run, `MachineDefines memCounter` and
`MachineCloses memCounter`.

The old boundary is `True` — INFERRED by reading, ASSERTED by the generator
below (it throws unless the boundary argument of `machine_ships_hier` is
`fun … => True`): the boundary is the conjunction of the composed theorem's
premises after its eleven run binders (`ShippingMachineShipsHierCommand`
58–65, `conj [] = True` at 17–18), and `memCounter.machine_composedT` is
`machine_linkedT_mem` applied to the wired head
`machine_traceL_of_loop_causal` (`Tools/ShippingMachineMemCommand.lean`
56–100), whose run binders are `hr`, `entry`, `closes : MachineCloses`
(`Tools/ShippingMachineSeqLinked.lean` 102–105) and nothing else.

## MEASURED (run 20261013-055644-b13b-alltests, `NoPortsMemDataProbe`)

    memCounter: nDecl=3, binders=10, call entries [SparkleMem.combo.4.8],
      argument lets [[1, 2, 3, 0]], instFields=[out], slots=2, lets=4, outputs [out], loops=1
    constants present [machineData, machine_ok, machine_body, machine_ships_hier, machine_design_sv0];
      absent [machine_closes, machine_ships_hierR, machine_design_svR0]
    #machine_design_svR0 memCounter: REFUSED — "no sequential child"

So the parent HAS register slots (2): the "parent without a register" axis
does not apply. The R0 generator refuses for another reason: its composed
theorem is built from the sequential children (`generateCoreSR`,
`Tools/ShippingMachineSeqCommandR.lean` 93), and a memory-only parent has none.

## What this file does

It applies the head `Tools.ShippingNoPorts.machine_design_noPorts` at `n = 0`
DIRECTLY to the arguments of the existing `memCounter.machine_ships_hier`
(read off its proof term), with

    C   := fun mctx mref cctx cref => MachineCloses mctx mref cctx cref memCounter data.shape
           (the old endpoint's own closing premise, unchanged)
    Bnd := fun _ mref _ cref w _ _ => ChildBnd mref cref w
           (NEW: the old boundary `True` is replaced by the child boundary of the
            run's start world — the built `kidsM_*` theorems ask it, `hB`)
    Bd / Inv / Reset := the theorem's own `kidsMem` / `memInv` / `ResetM`

the wired endpoint and the composed theorem being the old ones with the new
boundary ignored (`fun … hr e c _ => soundL hr e c`, the same wrapper as
`machine_ships_hier`'s own proof, 412–414). The four run hypotheses are
`Tools.ShippingMemOnly.memOnly_runFacts / _outsCheck / _kidsMem /
_designCheck` at `memCounter`'s data (`memCounter_data`), the closing passed
as `machineClosesAt_of_closes closes`.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `memCounter.machine_design_sv0` | predicted state |
|---|---|---|
| `memCounter.machine_design_noPorts0` | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` | predicted absent, pending build |
| | the old boundary `True` | REPLACED by `ChildBnd mref cref w` — an antecedent the old endpoint does NOT have |
| | `MachineCloses memCounter` (all worlds, every logger) | STILL A PREMISE (a binder), unchanged |
| | `hr`, `MachineDefines memCounter` | stay |

The new endpoint is NOT a strengthening of the old one: it trades four
decidable check premises for the runtime boundary `ChildBnd`.

## SCOPE (binding for any report)

ONE declaration, `memCounter`: a `Signal.loop` parent with two register
slots and ONE combinational-read memory (aw 4, dw 8), depth 0. Data
conditions decided per declaration by the kernel (`MemOnlyData`: `callsOk 3`,
slot lengths, no late domain binder, `insts ≠ []`, `slots ≠ []`,
`instFields ≠ []`, output width / name / scalar, every entry the placeholder
`SparkleMem.combo.4.8`, `callWidthsOk` / `callArgsOk` against the memory
module's `[out : BitVec 8]` / `[4, 8, 1, 4]`) are conditions, not
reductions. The result depends on the compiler's guards with fallback. The
conclusion is about `DesignSV (childMap D.modules) 0 (checkedOptimize b)` —
the module list, not the SV string, not `#sim`. The run, the reflection, the
boundary `ChildBnd` AND THE ALL-WORLDS CLOSING `MachineCloses` stay premises;
whether `MachineCloses` can hold of a shape with calls is NOT examined here
(`Tools/ShippingChildRun.lean` 439–443 says "for a shape with calls only
[`MachineClosesAt`] can hold"). NOT covered: an endpoint asking
`MachineClosesAt` (attempted, logs only, in `NoPortsMemOnlyAtProbe`), the
closing, a generator, depth ≥ 1.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
  let mem := Sparkle.Compiler.MachMemory.memChildName true 4 8
  let rf ← Tools.ShippingMachineCommand.readMachine f
  let fe := rf.shape.insts.map (·.1)
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for s in [`machineData, `machine_ok, `machine_body, `machine_sound, `machine_composedT,
      `machine_closes, `machine_ships_hier, `machine_ships_hierR, `machine_design_sv0,
      `machine_design_svR0, `machine_design_noPorts0] do
    if env.contains (f ++ s) then have_ := have_ ++ [s] else lack := lack ++ [s]
  Lean.logInfo m!"NOPORTS MEMONLY DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {fe}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}, loops={rf.shape.loops.length}; the memory placeholder {mem}; constants present {have_}; absent {lack}"
  unless rf.nDecl == 3 do throwError "{f}: nDecl = {rf.nDecl}, the hand theorems are written for 3"
  if fe.isEmpty then throwError "{f}: no call entry"
  for e in fe do
    unless e == mem do
      throwError "{f}: the call entries are {fe}; {e} is not {mem}"
  if rf.shape.instFields.isEmpty then throwError "{f}: instFields = [] — not the general closing"
  if rf.shape.layout.slots.isEmpty then
    throwError "{f}: NO REGISTER SLOT — the parent-without-a-register axis (hsl : d.shape.layout.slots ≠ [] of kidsM_runFacts / kidsM_designCheck fails); nothing below applies"
  for n in [f ++ `machine_ships_hier, f ++ `machine_design_sv0, f ++ `machineData,
      f ++ `machine_ok, f ++ `machine_body] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_design_noPorts0] do
    if env.contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsMemOnly
open Lean Meta Elab Command

/-- The checker constants an endpoint of a memory parent must not mention:
those of the depth chain and the flat child bounds. -/
def forbiddenMem : List Name :=
  Tools.ShippingNoPortsCommand.forbidden ++
    [``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingMachineShipsHier.kidsMem,
     ``Tools.ShippingMachineShipsHier.kidsMasked, ``Tools.ShippingHierPremisesBase.hierCheck]

/-- The head `machine_design_noPorts` at `n = 0` on the arguments `a` of a
memory-route `machine_ships_hier`, with the boundary `bndNew`, the closing
predicate `C`, the wired endpoint `soundL` and the composed theorem
`composed` (both under `C` and `bndNew`), at the run binders `xs'`; the four
run hypotheses are discharged by the theorems `facts` / `outs` / `mem` /
`design` (explicit arguments: the core run, the post-processing fact, the
reflection, `MachineClosesAt` — `closesAt` —, [the gate], then hypotheses
found among the conjuncts of the endpoint's boundary: NO binder is added). -/
def finishM0 (f : Name) (a : Array Lean.Expr) (bndNew C soundL composed : Lean.Expr)
    (xs' : Array Lean.Expr) (closesAt : Lean.Expr) (facts outs mem design : Name) :
    MetaM Lean.Expr := do
  let args : Array (Option Lean.Expr) :=
    #[some (mkNatLit 0), some a[3]!, some bndNew, some C, some a[5]!, some a[6]!,
      some a[7]!, some a[8]!, some a[9]!, some a[10]!,
      some a[11]!, some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!,
      some a[17]!, some a[18]!, some a[19]!, some a[20]!,
      some soundL, some composed, some a[23]!] ++ xs'.map some
  let pre ← instantiateMVars
    (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
  if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
  -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs'[9] = entry
  let .forallE _ TF _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
  let hFacts ← forallTelescope TF fun zs goal => do
    unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
    let p ← mkAppM facts #[zs[3]!, zs[4]!, xs'[9]!, closesAt]
    mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith facts p zs[5]! goal #[])
  let pre := mkApp pre hFacts
  -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
  let .forallE _ TO _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's output-check hypothesis is not where it is expected"
  let hOuts ← forallTelescope TO fun zs goal => do
    unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
    let p ← mkAppM outs #[zs[3]!, zs[4]!, xs'[9]!, closesAt, zs[5]!]
    mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith outs p zs[6]! goal #[])
  let pre := mkApp pre hOuts
  -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
  let .forallE _ TM _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
  let hMem ← forallBoundedTelescope TM (some 6) fun zs goal => do
    unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
    let p ← mkAppM mem #[zs[3]!, zs[4]!, xs'[9]!, closesAt]
    mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith mem p zs[5]! goal #[])
  let pre := mkApp pre hMem
  -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
  let .forallE _ TD _ _ ← whnfR (← inferType pre)
    | throwError "{f}: the head's design-check hypothesis is not where it is expected"
  let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
    unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
    let p ← mkAppM design #[zs[3]!, zs[4]!, xs'[9]!, closesAt]
    mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith design p zs[5]! goal #[])
  mkLambdaFVars xs' (mkApp pre hDesign)

/-- **The depth-0 endpoint of a memory-only parent without check premises.**

`atForm = false` → `f.machine_design_noPorts0`: the closing predicate is the
old endpoint's own `MachineCloses` (all worlds); the wired endpoint and the
composed theorem are the arguments of `f.machine_ships_hier` with the new
boundary ignored.

`atForm = true` → `f.machine_design_noPortsR0` (an ATTEMPT, used by the probe
only): the closing predicate is `MachineClosesAt`; the wired endpoint is the
`RA` twin of the endpoint's head under `ChildBnd`
(`Tools/ShippingMachineSeqLinkedR.lean`), forgotten to `MachineTraceLB`; the
composed theorem is `machine_linkedT_mem` on it with the data arguments of
the existing `f.machine_composedT` (read off its proof term).

Both: the boundary is `ChildBnd mref cref w` in place of the old `True`
(the generator THROWS if the old boundary is anything else). -/
def generateM0 (f : Name) (facts outs mem design : Name) (atForm : Bool := false) :
    MetaM Name := do
  let ships := f ++ `machine_ships_hier
  let name := f ++ (if atForm then `machine_design_noPortsR0 else `machine_design_noPorts0)
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
  let bndAt (zs : Array Lean.Expr) : Lean.Expr :=
    bndNew.beta #[zs[0]!, zs[1]!, zs[2]!, zs[3]!, zs[4]!, zs[6]!, zs[7]!]
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let cT ← instantiateMVars (← inferType xs[10]!)
    unless cT.isAppOfArity ``Tools.ShippingMachineEntry.MachineCloses 6 do
      throwError "{ships}: its closing premise is{indentExpr cT}\nnot MachineCloses"
    let atT := mkAppN (mkConst ``Tools.ShippingChildInv.MachineClosesAt) cT.getAppArgs
    if !atForm then
      let C ← mkLambdaFVars #[xs[0]!, xs[1]!, xs[2]!, xs[3]!] cT
      -- the old wired endpoint, the new boundary ignored
      let soundL ← forallTelescope (← inferType a[21]!) fun zs _ => do
        unless zs.size == 11 do
          throwError "{ships}: the wired endpoint has {zs.size} binders, expected 11"
        withLocalDeclD `hB (bndAt zs) fun hB =>
          mkLambdaFVars (zs.push hB) (mkAppN a[21]! zs)
      -- the old composed theorem, its boundary `True` given, the new one ignored
      let composed ← forallTelescope (← inferType a[22]!) fun zs _ => do
        unless zs.size == 13 do
          throwError "{ships}: the composed theorem has {zs.size} binders, expected 13"
        unless (← whnfR (← inferType zs[11]!)).isConstOf ``True do
          throwError "{ships}: the composed theorem's boundary is not True"
        withLocalDeclD `hB (bndAt zs) fun hB =>
          mkLambdaFVars (zs.extract 0 11 ++ #[hB, zs[12]!])
            (mkAppN a[22]! (zs.extract 0 11 ++ #[mkConst ``True.intro, zs[12]!]))
      let closesAt ← mkAppM ``Tools.ShippingChildInv.machineClosesAt_of_closes #[xs[10]!]
      finishM0 f a bndNew C soundL composed xs closesAt facts outs mem design
    else
      let (headL, eargs, back?) ← Tools.ShippingMachineSeqCommand.endpointParts f
      if back?.isSome then throwError "{f}: a transported endpoint — not handled here"
      let headA := headL.appendAfter "RA"
      unless (← getEnv).contains headA do throwError "{f}: no head {headA}"
      let pLA := mkAppN (mkConst headA) eargs
      let C ← mkLambdaFVars #[xs[0]!, xs[1]!, xs[2]!, xs[3]!] atT
      -- the wired endpoint under `MachineClosesAt` and `ChildBnd`
      let soundL ← forallTelescope (← inferType pLA) fun zs _ => do
        unless zs.size == 12 do
          throwError "{f}: {headA} has {zs.size} binders after its data, expected 12"
        mkLambdaFVars zs
          (← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[mkAppN pLA zs])
      -- the data arguments of the existing composed theorem
      let some (.thmInfo ct) := (← getEnv).find? (f ++ `machine_composedT)
        | throwError "{f}: no machine_composedT"
      let rest ← lambdaTelescope ct.value fun ys body => do
        unless ys.size == 11 do
          throwError "{f}.machine_composedT: {ys.size} binders, expected 11"
        unless body.isAppOfArity ``Tools.ShippingMachineMemLinked.machine_linkedT_mem 21 do
          throwError "{f}.machine_composedT: not machine_linkedT_mem on 21 arguments"
        let rest := body.getAppArgs.extract 11 21
        for r in rest do
          if r.hasAnyFVar (fun id => ys.any (·.fvarId! == id)) then
            throwError "{f}.machine_composedT: a data argument depends on the run"
        pure rest
      let composed ← forallTelescope (← inferType pLA) fun zs _ => do
        let hNew ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB #[mkAppN pLA zs]
        let linked ← mkAppM ``Tools.ShippingMachineMemLinked.machine_linkedT_mem (#[hNew] ++ rest)
        let memF ← mkAppM ``Tools.ConeFold.memFree
          #[← mkAppM ``Sparkle.IR.AST.Module.body #[zs[6]!]]
        withLocalDeclD `hm memF fun hm => do
          mkLambdaFVars (zs.push hm)
            (← mkAppM ``Tools.ShippingMachineShipsHier.composedG_of_Tmem #[linked, hm])
      withLocalDeclD `closes atT fun cl =>
        finishM0 f a bndNew C soundL composed (xs.pop.push cl) cl facts outs mem design
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in forbiddenMem do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The proposition binders of a statement, printed. -/
def propBinders (t : Lean.Expr) : MetaM (Array String) :=
  forallTelescope t fun xs _ => do
    let mut out : Array String := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then out := out.push (toString (← ppExpr ty))
    return out

/-- The audit of a memory-only parent's endpoint `f.machine_design_noPorts0`
against `f.machine_design_sv0` (an error on any failure): standard axioms of
`thms` and the endpoint; no checker constant; the old endpoint asks the four;
both ask `MachineCloses` and neither `MachineClosesAt`; the same three
proposition binders; ONE antecedent under the existentials, `ChildBnd`, which
the old endpoint does not ask (LOGGED as added); the premise list with the
goal-gap classifier's verdicts (LOGGED). -/
def auditM0 (f : Name) (thms : List Name) : MetaM Unit := do
  let old := f ++ `machine_design_sv0
  let openN := f ++ `machine_design_noPorts0
  -- (a) standard axioms
  for n in [``Tools.ShippingMemOnly.kidsMem_of, ``Tools.ShippingMemOnly.core_kidsMemM,
      ``Tools.ShippingMemOnly.memOnly_kids, ``Tools.ShippingMemOnly.memOnly_runFacts,
      ``Tools.ShippingMemOnly.memOnly_outsCheck, ``Tools.ShippingMemOnly.memOnly_kidsMem,
      ``Tools.ShippingMemOnly.memOnly_designCheck, ``Tools.ShippingMemKid.memKid_facts,
      ``Tools.ShippingMemKid.kidsM_runFacts, ``Tools.ShippingMemKid.kidsM_outsCheck,
      ``Tools.ShippingMemKid.kidsM_designCheck, ``Tools.ShippingMemKid.core_callStmtM] ++
      thms ++ [openN] do
    unless (← getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the endpoint's statement mentions no checker constant
  let openT := (← getConstInfo openN).type
  for k in Tests.Compiler.NoPortsTest.checkers ++ forbiddenMem do
    if (openT.find? (·.isConstOf k)).isSome then
      throwError "{openN}: the statement mentions {k}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsHier.kidsMem, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the closing: the all-worlds form, asked by BOTH; the at-form by neither
  for (n, t) in [(old, oldT), (openN, openT)] do
    unless (t.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome do
      throwError "{n}: does not ask MachineCloses (the report says it stays a premise)"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{n}: mentions MachineClosesAt (the report says the all-worlds form)"
  -- (e) the binders: the SAME as the base endpoint's, printed the same, in the same order
  let bOld ← propBinders oldT
  let bNew ← propBinders openT
  unless bOld == bNew do
    throwError "{openN}: its proposition binders differ from {old}'s:\n{bNew}\nvs\n{bOld}"
  unless bNew.size == 3 do
    throwError "{openN}: {bNew.size} proposition binders, expected 3 (the run, MachineDefines, MachineCloses)"
  -- (f) the antecedents under the existentials: exactly one, the NEW boundary
  -- `ChildBnd`, which the base endpoint does not ask; the base endpoint's are
  -- LOGGED (five by reading: shipsHierCheck, designCheck, outsCheck, True, kidsMem)
  let inner ← forallTelescope openT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerOld ← forallTelescope oldT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  logInfo m!"NOPORTS MEMONLY ANTECEDENTS {old}: {innerOld.size} — {innerOld.map (·.1)}"
  logInfo m!"NOPORTS MEMONLY ANTECEDENTS {openN}: {inner.size} — {inner.map (·.1)}"
  unless inner.size == 1 do
    throwError "{openN}: {inner.size} antecedents under the existentials, expected 1 (ChildBnd): {inner.map (·.1)}"
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.ChildBnd)).isSome do
    throwError "{openN}: does not ask ChildBnd (the report says it is the one antecedent)"
  if (oldT.find? (·.isConstOf ``Tools.ShippingChildInv.ChildBnd)).isSome then
    throwError "{old}: asks ChildBnd already (the report says it is ADDED)"
  unless innerOld.any (fun x => x.1 == "True") do
    throwError "{old}: no antecedent printed True (the report says the old boundary is True): {innerOld.map (·.1)}"
  -- (g) the complete premise list, with the goal-gap classifier's verdicts (LOGGED, not
  -- asserted: MachineCloses is a premise of this endpoint)
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines openN
  logInfo m!"{String.intercalate "\n" lines.toList}"
  logInfo m!"NOPORTS MEMONLY AUDIT {f}: {openN} on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid (memKid_facts, kidsM_*, core_callStmtM) and the hand lemmas {thms}. The endpoint's statement mentions none of portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck, kidsMixed, kidsMem, kidsMasked, while {old} mentions shipsHierCheck, kidsMem, designCheck and outsCheck. Proposition binders: the SAME {bNew.size} as {old}'s (the run, MachineDefines {f}, MachineCloses {f} — the ALL-WORLDS closing, STILL A PREMISE). Under the existentials: 1 antecedent, ChildBnd of the run's start world — ADDED: {old} has {innerOld.size} antecedents, among them True (its boundary) and not ChildBnd. The goal-gap classifier lists {bad.size} premise(s) NOT ALLOWED (logged above; not asserted). SCOPE: one declaration, a memory-only parent with register slots, depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. NOT covered: the closing (neither form), an endpoint asking MachineClosesAt, a generator, depth ≥ 1."

end Tests.Compiler.NoPortsMemOnly

namespace Tests.Compiler.NoPortsMemOnlyCounterTest
open Tools.ShippingMemKid (memOuts memIns)

/-- The placeholder's child is the built module (the generators' own `rfl`,
`Tools/ShippingMachineMemCommand.lean` 46). -/
theorem mem_isMem : Sparkle.Compiler.MachMemory.memChild?
    (Sparkle.Compiler.MachMemory.memChildName true 4 8) =
      some (Sparkle.Compiler.MachMemory.memModule true 4 8) := by
  first | rfl | decide

/-- Every call entry of `memCounter` is of the memory placeholder (decided on
the reflected data; no order, no count). -/
theorem memCounter_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName true 4 8 := by
  first | decide | decide +kernel

theorem memCounter_calls :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).callsOk 3 =
      true := by
  first | decide | decide +kernel

theorem memCounter_slots :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).ss.length =
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.layout.slots.length := by
  first | decide | decide +kernel

theorem memCounter_domB :
    ∀ b ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.binders.drop 3,
      b.2 ≠ .domain := by
  first | decide | decide +kernel

theorem memCounter_outTy :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem memCounter_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData 3
    (fun _ => memOuts 8) = true := by
  first | decide | decide +kernel

theorem memCounter_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData 3
    (fun _ => memIns 4 8) = true := by
  first | decide | decide +kernel

theorem memCounter_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem memCounter_outScalar :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- **The data conditions of `memCounter`** (every field decided above or a
generated constant of the declaration). -/
theorem memCounter_data : Tools.ShippingMemOnly.MemOnlyData
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData 3 4 8 :=
  Tools.ShippingMemOnly.MemOnlyData.mk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_body
    memCounter_calls memCounter_slots memCounter_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    memCounter_outTy
    (fun k hk => Exists.intro true
      ((congrArg Sparkle.Compiler.MachMemory.memChild? (memCounter_entry k hk)).trans mem_isMem))
    memCounter_callWidths memCounter_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (memCounter_outChars o ho))
    memCounter_outScalar

/-- **The run's facts of `memCounter`'s full-entry module** (`memOnly_runFacts`). -/
theorem memCounter_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemOnly.memOnly_runFacts memCounter_data hB hcore hpost entry closes

/-- **The output check at depth 0 under the statement-kind gate**
(`memOnly_outsCheck`). -/
theorem memCounter_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_outsCheck memCounter_data hB hcore hpost entry closes hg

/-- **The children's bound of the memory route, `kidsMem`** (`memOnly_kidsMem`):
every instance's child is the built memory module, no connection names its
read latch. -/
theorem memCounter_kidsMemG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemOnly.memOnly_kidsMem memCounter_data hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`memOnly_designCheck`). -/
theorem memCounter_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_designCheck memCounter_data hB hcore hpost entry closes

end Tests.Compiler.NoPortsMemOnlyCounterTest

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemOnly.generateM0 f
      ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_runFacts
      ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_outsG0
      ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_kidsMemG
      ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_designP0
  Lean.logInfo m!"NOPORTS MEMONLY [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents — by hand (memCounter_data: MemOnlyData; memCounter_runFacts, memCounter_outsG0, memCounter_kidsMemG, memCounter_designP0: Tools.ShippingMemOnly.memOnly_* at depth 0). Its boundary is ChildBnd of the run's start world in place of the old True (ADDED); MachineCloses (all worlds) is STILL a binder"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnly.auditM0
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
    [``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_entry,
     ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_data,
     ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_runFacts,
     ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_outsG0,
     ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_designP0]
