import Tests.Compiler.NoPortsSlotlessLib
import Tests.Compiler.ShippingChildBoundaryTest
import Tools.ShippingNoPortsSlotlessCommand

/-! # `#machine_no_ports_seq`: the generator for parents of leaf register machines, with or without a register (G1, unit U5a, round par/a-21)

TARGET-BUILT ONLY. This file GENERATES `twinCalls.*` and `mesh2x2.*`
(`machine_ships_hierNR1`, `machine_design_svNR1`, `machine_closes_at`,
`machine_design_noPortsNR1(_closed)(_gap)`), names OWNED by the hand tests
`NoPortsSlotlessTwinCallsTest` / `NoPortsSlotlessMesh2x2Test`. It does not
import them and must never be imported together with them (not in
`Tests.AllTests`).

`Tools/ShippingNoPortsSlotlessCommand.lean` on:

* `engineOnce` at depth 1 — the COMPARE path, a parent WITHOUT a register:
  `engineOnce.machine_design_noPortsNR1` and its `_closed` exist (hand,
  BUILT at 23a6f28c). The command rebuilds both statements from its own
  generated lemmas (`engineOnce.machine_kidsK1`, `…_seqKidS`,
  `…_runFactsK1`, `…_designPK1`, `…_outsGK1`, `…_maskedGK1`), adds them as
  `…_regen` (kernel-checked) and REQUIRES `isDefEq` with the existing
  statements.
* `parent` at depth 1 — the COMPARE path, a parent WITH a register
  (`#machine_no_ports`'s endpoint, BUILT, `NoPortsTest`): the slot case is
  unchanged — the same statements, now proved through the second disjunct
  (`SeqKid`: the child `cnt` is sequential), the parent's own register not
  used.
* `twinCalls`, `mesh2x2` at depth 1 — GENERATED here (base endpoints by the
  built commands first), goal-gap theorems, the audit.
* refusals, LOGGED (`_try`): `seqMem` (a memory child), `grand` (callee
  `mid` has calls of its own), `pe` (no call).
  NOT EXERCISED: the refusal of a parent without a register whose callees
  are all combinational — no declaration of that shape is known in the
  tests (`docs/parallel/verification-a20.md`: "no real declaration"); the
  line exists in `scopeS` only.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| declaration | endpoint | premise (of `f.machine_design_svNR1`) | predicted state |
|---|---|---|---|
| `engineOnce` | `…machine_design_noPortsNR1(_closed)` | — | nothing new removed: REBUILT, statements `isDefEq` the BUILT hand ones (`…_regen` added) |
| `parent` | `…machine_design_noPortsNR1(_closed)` | — | nothing new removed: REBUILT, statements `isDefEq` the BUILT generated ones (`…_regen` added) |
| `twinCalls` | `…machine_design_noPortsNR1` | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1` | predicted absent, pending build |
| | `…machine_design_noPortsNR1_closed` (+ `_gap`) | `MachineClosesAt twinCalls` | predicted absent; 0 NOT ALLOWED; no gap hypothesis |
| `mesh2x2` | the same two | the same | the same |
| `seqMem`, `grand`, `pe` | — | — | REFUSED with a reason line; nothing added |

SCOPE: one declaration each, depth 1, a parent under the general closing
whose callees are all leaf register machines; data conditions decided per
declaration (conditions, not reductions); compiler guards with fallback;
`DesignSV` of the module list — not the SV string, not `#sim`; the run, the
reflections and `ChildBnd` remain premises.

WRITTEN, NOT BUILT. -/

/-! ## 1. The reader data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let e := ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
  let t := ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
  let m := ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
  let p := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent
  for g in [e, t, m] do
    let r ← Tests.Compiler.NoPortsSlotlessLib.logData "NOPORTS SEQ FAMILY" g
    unless r.shape.layout.slots.isEmpty do
      throwError "{g}: {r.shape.layout.slots.length} slots — expected a parent without a register"
  let rp ← Tests.Compiler.NoPortsSlotlessLib.logData "NOPORTS SEQ FAMILY" p
  if rp.shape.layout.slots.isEmpty then
    throwError "{p}: no slot — expected a parent WITH a register (the slot case of the compare path)"
  for f in [e, p] do
    for s in ["machine_design_noPortsNR1", "machine_design_noPortsNR1_closed"] do
      unless (← Lean.getEnv).contains (f ++ Lean.Name.mkSimple s) do
        throwError "{f}: {s} is not in the imports (the compare path needs the built endpoint)"
      if (← Lean.getEnv).contains (f ++ Lean.Name.mkSimple (s ++ "_regen")) then
        throwError "{f}: {s}_regen exists already (another family test is imported)"
  for f in [t, m] do
    for s in ["machine_ships_hierNR1", "machine_design_svNR1", "machine_closes_at",
        "machine_design_noPortsNR1", "machine_design_noPortsNR1_closed"] do
      if (← Lean.getEnv).contains (f ++ Lean.Name.mkSimple s) then
        throwError "{f}: {s} exists already — the hand test is imported: NAME CLASH (this file is target-built only)"

/-! ## 2. The compare path: a parent without a register, a parent with one -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_seq Sparkle.Tests.Compiler.MultiInstance.engineOnce 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_seq Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

/-! ## 3. Generation: `twinCalls`, `mesh2x2` -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.twinCalls 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.MultiInstance.twinCalls

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_seq Sparkle.Tests.Compiler.MultiInstance.twinCalls 1

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.mesh2x2 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.MultiInstance.mesh2x2

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_seq Sparkle.Tests.Compiler.MultiInstance.mesh2x2 1

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_design_noPortsNR1_closed

/-! ## 4. Refusals (LOGGED, nothing kept) -/

set_option maxHeartbeats 0 in
#machine_no_ports_seq_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem 1

set_option maxHeartbeats 0 in
#machine_no_ports_seq_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 1

set_option maxHeartbeats 0 in
#machine_no_ports_seq_try Sparkle.Tests.Compiler.MultiInstance.pe 1

/-! ## 5. The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let e := ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
  let t := ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
  let m := ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
  let p := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent
  let pe := ``Sparkle.Tests.Compiler.MultiInstance.pe
  -- (1) the compare path RAN (the rebuilt theorems exist) and agrees
  for f in [e, p] do
    for s in ["machine_design_noPortsNR1", "machine_design_noPortsNR1_closed"] do
      let x := f ++ Lean.Name.mkSimple s
      let r := f ++ Lean.Name.mkSimple (s ++ "_regen")
      unless (← Lean.getEnv).contains r do
        throwError "{r}: missing — the compare path did not rebuild {x}"
      Tests.Compiler.NoPortsTest.stdAxioms r
      unless ← Lean.Meta.isDefEq (← Lean.getConstInfo x).type (← Lean.getConstInfo r).type do
        throwError "{r}: its statement is not that of {x}"
  -- (2) the generated lemmas: standard axioms; the two run theorems that
  -- asked the parent's register are proved from the S theorems
  for f in [e, p, t, m] do
    for s in ["machine_kidsK1", "machine_seqKidS", "machine_runFactsK1", "machine_designPK1",
        "machine_outsGK1", "machine_maskedGK1"] do
      let n := f ++ Lean.Name.mkSimple s
      unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
      Tests.Compiler.NoPortsTest.stdAxioms n
    for (s, thm) in [("machine_runFactsK1", ``Tools.ShippingSlotlessKidFacts.kids_runFactsS),
        ("machine_designPK1", ``Tools.ShippingSlotlessKidFacts.kids_designCheckS),
        ("machine_seqKidS", ``Tools.ShippingSlotlessClk.seqKid_of_leafAt)] do
      let n := f ++ Lean.Name.mkSimple s
      let some (Lean.ConstantInfo.thmInfo ti) := (← Lean.getEnv).find? n
        | throwError "{n}: not a theorem"
      unless (ti.value.find? (·.isConstOf thm)).isSome do
        throwError "{n}: its proof does not apply {thm}"
  -- (3) twinCalls, mesh2x2: GENERATED (no `_regen`), no checker, the four of the base endpoint
  let mut summary : Array String := #[]
  for f in [t, m] do
    let old := f ++ `machine_design_svNR1
    let openN := f ++ `machine_design_noPortsNR1
    let closed := f ++ `machine_design_noPortsNR1_closed
    let gap := f ++ `machine_design_noPortsNR1_closed_gap
    for n in [old, openN, closed, gap] do
      unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
      Tests.Compiler.NoPortsTest.stdAxioms n
    for n in [openN, closed, gap] do
      let ci ← Lean.getConstInfo n
      for k in Tests.Compiler.NoPortsTest.checkers do
        if (ci.type.find? (·.isConstOf k)).isSome then throwError "{n}: the statement mentions {k}"
    if (← Lean.getEnv).contains (f ++ `machine_design_noPortsNR1_regen) then
      throwError "{openN}: existed before this file (the hand test was imported: NAME CLASH)"
    let oldT := (← Lean.getConstInfo old).type
    for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
        ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
        ``Tools.ShippingDesignSVBack.outsCheck] do
      unless (oldT.find? (·.isConstOf k)).isSome do
        throwError "{old}: does not mention {k} (the inventory is wrong)"
    let openT := (← Lean.getConstInfo openN).type
    let closedT := (← Lean.getConstInfo closed).type
    unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
      throwError "{openN}: does not ask MachineClosesAt"
    if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{closed}: still asks MachineClosesAt"
    let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
    unless gaps.isEmpty do throwError "{f}: the gap hypotheses are {gaps}, expected none"
    let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
    Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
    unless bad.isEmpty do
      throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
    summary := summary.push s!"{f}: GENERATED {openN} and {closed} (standard axioms, no checker constant, {lines.size} premises of the closed form listed, 0 NOT ALLOWED), {gap} with no gap hypothesis; {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck"
  -- (4) the refused declarations left nothing
  for f in [``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, pe] do
    for s in ["machine_kidsK1", "machine_seqKidS", "machine_runFactsK1", "machine_designPK1"] do
      if (← Lean.getEnv).contains (f ++ Lean.Name.mkSimple s) then
        throwError "{f}: {s} exists — it was not refused"
  Lean.logInfo m!"NOPORTS SEQ FAMILY: {e} (no register) and {p} (a register) — COMPARE path, both statements of each rebuilt by #machine_no_ports_seq and isDefEq the built ones, kept as _regen on standard axioms (nothing new removed; the slot case is unchanged). For all four declarations machine_runFactsK1 / machine_designPK1 apply kids_runFactsS / kids_designCheckS and machine_seqKidS applies seqKid_of_leafAt (checked on the proof terms). {String.intercalate ". " summary.toList}. REFUSED with reasons (logged above), nothing added: seqMem (memory child), grand (callee with calls of its own), {pe} (no call). NOT EXERCISED: the refusal of a parent without a register whose callees are all combinational (no such declaration in the tests). TARGET-BUILT ONLY: it creates names owned by NoPortsSlotlessTwinCallsTest and NoPortsSlotlessMesh2x2Test. SCOPE: one declaration each, depth 1, a parent under the general closing whose callees are all leaf register machines; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim; the run, the reflections and ChildBnd remain premises."
