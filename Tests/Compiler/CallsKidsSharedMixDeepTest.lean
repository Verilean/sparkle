import Tests.Compiler.NoPortsMixDeepTest
import Tools.ShippingCallsKidsSGen

/-! # `mixDeep`: the general closing RELATIVE to the end cache — NOT a closed endpoint (round par/a-17)

`mixDeep → {mid2 → midH → rcH, midH → rcH, cnt}`: `midH` (and `rcH`) is
reached under two different callees. `Tests/Compiler/NoPortsMixDeepTest.lean`
(BUILT) has the OPEN depth-2 endpoint only; its audit throws if
`mixDeep.machine_design_noPortsNR2_closed` exists in ITS environment. This
file is downstream of it and STILL creates no such constant: the closing
`MachineClosesAt mixDeep` is not derived (reason and the exact missing
statements: `docs/parallel/A-shared-descendant.md`).

What this file generates, by `#machine_closes_shared`:

    mixDeep.closes_shared : MachineDefines mid2 → MachineDefines midH →
      EntryDefines rcH → MachineDefines cnt →          (the order is LOGGED, not asserted)
      Tools.ShippingCallsKidsS.MachineClosesAtS mctx mref cctx cref mixDeep
        mixDeep.machineData.shape (mixDeep.machineData.shape.insts.map (·.1))

`MachineClosesAtS` is `MachineClosesAt` with one more antecedent: the world
the machine synthesis ENDS in satisfies `CacheAgrees` over the callees (the
cache's entries of two different callees agree on every module name they
both have). It is weaker than `MachineClosesAt`; no endpoint accepts it.

## EXPECTED (the audit THROWS otherwise)

| endpoint | premise | state |
|---|---|---|
| `mixDeep.machine_design_noPortsNR2` (OPEN, BUILT) | `MachineClosesAt mixDeep` | STAYS — NOT ALLOWED, not removed by this file |
| | the boundary | STAYS, not reduced |
| `mixDeep.machine_design_noPortsNR2_closed` | — | does NOT exist (asserted) |
| `mixDeep.closes_shared` (new; not an endpoint) | `hdisjD` of `machineClosesAt_of_kidsD` | absent: not a hypothesis of `machineClosesAtS_of_kids` |
| | the other hypotheses of the general closing | decided on `mixDeep`'s data (predicted; NOT BUILT) |
| | — | its conclusion has the antecedent `CacheAgrees … w'` (NOT derived) |

So NO endpoint loses a premise in this file.

## SCOPE

One declaration. A statement about `synthesizeMachineCertified`'s result
being `some`, relative to a cache condition that is not proved. Nothing
about the SV string or `#sim`.

UNVERIFIED at the time of writing: nothing in this file was built. -/

/-! ## The reader data this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let r2 ← Tools.ShippingMachineCommand.readMachine m2
  let rm ← Tools.ShippingMachineCommand.readMachine m
  let rcn ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let ge := rg.shape.insts.map (·.1)
  let e2 := r2.shape.insts.map (·.1)
  let em := rm.shape.insts.map (·.1)
  let ecn := rcn.shape.insts.map (·.1)
  let argsG := rg.shape.insts.map (·.2.1)
  let cands := [g ++ `closes_shared, g ++ `closes_deep, g ++ `machine_closes_at,
    g ++ `machine_design_noPortsNR2, g ++ `machine_design_noPortsNR2_closed,
    m2 ++ `iface_deep, m2 ++ `closes_deep, m ++ `iface_deep, m ++ `closes_deep,
    c ++ `machine_closes, rc ++ `gate_peel]
  let present := cands.filter fun n => env.contains n
  let absent := cands.filter fun n => !env.contains n
  Lean.logInfo m!"SHARED MIXDEEP DATA {g}: nDecl={rg.nDecl}; call entries (one per projected field) {ge}; their argument positions {argsG}; instFields {rg.shape.instFields}; slots {rg.shape.layout.slots.length}; outputs {rg.shape.layout.outs.map (·.name)}\n{m2}: nDecl={r2.nDecl}; call entries {e2}; instFields {r2.shape.instFields}\n{m}: nDecl={rm.nDecl}; call entries {em}; instFields {rm.shape.instFields}\n{c}: nDecl={rcn.nDecl}; call entries {ecn}\nin the imports: {present}\nNOT in the imports: {absent}"
  if rg.shape.instFields.isEmpty then throwError "{g}: instFields = [] — not the general closing"
  unless ge.contains m2 && ge.contains m && ge.contains c do
    throwError "{g}: its call entries {ge} do not hold {m2}, {m} and {c}"
  unless e2.contains m do
    throwError "{m2}: {m} is not among its call entries {e2} — no shared descendant (the note is wrong)"
  unless em.contains rc do
    throwError "{m}: {rc} is not among its call entries {em}"
  unless ecn.isEmpty do throwError "{c}: has calls — not a leaf"
  for n in [g ++ `closes_shared, g ++ `machine_design_noPortsNR2_closed] do
    if env.contains n then throwError "{n}: exists already"
  let openN := g ++ `machine_design_noPortsNR2
  unless env.contains openN do
    throwError "{openN}: missing (the BUILT open endpoint)"

/-! ## The relative closing -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_closes_shared Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let name := g ++ `closes_shared
  let openN := g ++ `machine_design_noPortsNR2
  let closed := g ++ `machine_design_noPortsNR2_closed
  -- (a) standard axioms: the general theorems and the generated one
  for n in [``Tools.ShippingCallsRunFinal.mapM_loop_final,
      ``Tools.ShippingCallsRunFinal.closeInstsGM_run_allF,
      ``Tools.ShippingCallsKidsS.closes_of_agree,
      ``Tools.ShippingCallsKidsS.machineClosesAtS_of_kids,
      ``Tools.ShippingCallsKidsS.machineClosesAt_of_kidsD_again, name] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the generated statement: every premise a reflection; the conclusion is
  -- MachineClosesAtS, and MachineClosesAt does not occur
  let ty := (← Lean.getConstInfo name).type
  let (lines, bad, concl) ← Lean.Meta.forallTelescope ty fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Array String := #[]
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then
        let s := toString (← Lean.Meta.ppExpr t)
        let isRefl := t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
          t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines
        lines := lines.push s
        unless isRefl do bad := bad.push s
    pure (lines, bad, body)
  Lean.logInfo m!"SHARED MIXDEEP PREMISES {name}: {lines.size} propositions among the binders:\n{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{name}: a premise that is not a reflection: {bad}"
  unless concl.isAppOf ``Tools.ShippingCallsKidsS.MachineClosesAtS do
    throwError "{name}: the conclusion is not MachineClosesAtS"
  if (ty.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{name}: the statement mentions MachineClosesAt"
  -- (c) NOTHING is closed: the open endpoint still asks the closing, and no closed form exists
  let openT := (← Lean.getConstInfo openN).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt (the inventory is wrong)"
  if (← Lean.getEnv).contains closed then
    throwError "{closed}: exists — this file adds no closed form"
  Lean.logInfo m!"SHARED MIXDEEP AUDIT {g}: {name} on standard axioms, {lines.size} premises, all reflections; its conclusion is MachineClosesAtS over the callees — MachineClosesAt with the antecedent CacheAgrees of the run's end world, which is NOT derived. {openN} still asks MachineClosesAt of {g}; {closed} does not exist. NO endpoint loses a premise. Not derived and not assumed: that the end world of a real run of {g}'s machine synthesis satisfies CacheAgrees (docs/parallel/A-shared-descendant.md)."
