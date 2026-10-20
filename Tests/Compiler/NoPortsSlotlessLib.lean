import Tests.Compiler.NoPortsSlotlessEngineOnceTest

/-! # Shared meta code of the slotless-parent tests (G1, unit U5a, round par/a-21)

`Tests/Compiler/NoPortsSlotlessEngineOnceTest.lean` (BUILT, not edited) has
its data log and its audit inline in `run_cmd`s. The tests of `twinCalls`
and `mesh2x2` and the family test of `#machine_no_ports_seq` need the same
two, so they are written here ONCE, as functions:

* `logData tag g` — the reader data of `g`, one `… DATA` line and one
  `… ENTRY` line PER CALL ENTRY (callee, argument `let`s, field): short
  lines, so that a truncated log still shows every entry. Then the
  evaluation of the one hypothesis on the path whose truth depends on the
  argument `let`s, `hfieldsNd` of
  `Tools.ShippingCallsSeqKids.machineClosesAt_of_seqKids`

      callee equal → argument lets equal → field equal → k = k'

  as three lists of entry pairs `k < k'` with the same callee: the same
  arguments (one instance; told apart by the FIELD only), the same field
  (told apart by the ARGUMENT `let`s only), both the same (`hfieldsNd` is
  FALSE if this list is not empty). LOGGED, nothing asserted here.
* `audit` — the audit of the engineOnce test, step 6, with the declaration,
  the hand lemmas and the no-register theorem as parameters. An error on any
  failure.

This file imports the engineOnce test, hence `pe.machine_closes`,
`pe.seq_child_runN`, `pe.machine_leafKid` come with it (they are NOT
recreated by any file of this round).

WRITTEN, NOT BUILT. -/
namespace Tests.Compiler.NoPortsSlotlessLib
open Lean Meta

/-- The reader data of `g`, LOGGED (see the header). Returns the reading. -/
def logData (tag : String) (g : Name) : MetaM Tools.ShippingMachineCommand.Read := do
  let r ← Tools.ShippingMachineCommand.readMachine g
  logInfo m!"{tag} DATA {g}: nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, lets={r.shape.layout.lets}, entries={r.shape.insts.length}, instFields={r.shape.instFields}, outputs {r.shape.layout.outs.map (·.name)}"
  let mut rows : Array (Nat × Name × List Nat × String) := #[]
  let mut k : Nat := 0
  for c in r.shape.insts do
    let fld : String := r.shape.instFields.getD k "?"
    rows := rows.push (k, c.1, c.2.1, fld)
    logInfo m!"{tag} ENTRY {g} [{k}]: callee {c.1}, argument lets {c.2.1}, field {fld}"
    k := k + 1
  let mut sameArgs : Array (Nat × Nat) := #[]
  let mut sameField : Array (Nat × Nat) := #[]
  let mut both : Array (Nat × Nat) := #[]
  for a in rows do
    for b in rows do
      if a.1 < b.1 && a.2.1 == b.2.1 then
        let ea : Bool := a.2.2.1 == b.2.2.1
        let ef : Bool := a.2.2.2 == b.2.2.2
        if ea && ef then both := both.push (a.1, b.1)
        else if ea then sameArgs := sameArgs.push (a.1, b.1)
        else if ef then sameField := sameField.push (a.1, b.1)
  logInfo m!"{tag} FIELDSND {g}: entry pairs k<k' of one callee — same argument lets, different field (ONE instance, told apart by the field): {toString sameArgs.toList}; same field, different argument lets (told apart by the ARGUMENT lets only): {toString sameField.toList}; same argument lets AND same field (hfieldsNd FALSE if not empty): {toString both.toList}"
  return r

/-- The audit of a hand-proved slotless parent `f` of the leaf register
machine `pe` (step 6 of the engineOnce test): `hand` — the hand lemmas;
`noSlots` — the theorem that `f`'s reflected data has no register. -/
def audit (tag : String) (f pe : Name) (hand : List Name) (noSlots : Name) : MetaM Unit := do
  let old := f ++ `machine_design_svNR1
  let openN := f ++ `machine_design_noPortsNR1
  let closed := f ++ `machine_design_noPortsNR1_closed
  let gap := f ++ `machine_design_noPortsNR1_closed_gap
  -- (a) standard axioms: the general theorems, the built ones they apply,
  -- the hand lemmas, the endpoints
  for n in [``Tools.ShippingSlotlessClk.seqKid_of_leafAt,
      ``Tools.ShippingSlotlessClk.core_seqKid_inputs,
      ``Tools.ShippingSlotlessClk.core_slotless_seq,
      ``Tools.ShippingSlotlessClk.core_raw_factsS,
      ``Tools.ShippingSlotlessClk.core_clkS,
      ``Tools.ShippingSlotlessKidFacts.kids_runFactsS,
      ``Tools.ShippingSlotlessKidFacts.kids_designCheckS,
      ``Tools.ShippingKidFacts.kids_outsCheck,
      ``Tools.ShippingKidFacts.kids_maskedN,
      ``Tools.ShippingLeafKidFacts.leafKid_facts,
      ``Tools.ShippingNoPorts.machine_design_noPorts,
      pe ++ `machine_leafKid] ++ hand ++ [noSlots, old, openN, closed, gap] do
    unless (← getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no endpoint statement mentions a checker constant
  for n in [openN, closed, gap] do
    let ci ← getConstInfo n
    for k in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf k)).isSome then
        throwError "{n}: the statement mentions {k}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the closing: asked by the open form, not by the closed one
  let openT := (← getConstInfo openN).type
  let closedT := (← getConstInfo closed).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt"
  if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closed}: still asks MachineClosesAt"
  -- (e) the data: the parent has NO register (a theorem about the reflected data)
  let nsInfo ← getConstInfo noSlots
  let nsT := nsInfo.type
  -- (f) no gap hypothesis
  let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
  unless gaps.isEmpty do
    throwError "{f}: the gap hypotheses are {gaps}, expected none"
  -- (g) the complete premise list of the closed endpoint (LOGGED), every one ALLOWED
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"{tag} AUDIT {f}: {openN}, {closed} and {gap} on standard axioms, with the built general theorems of Tools.ShippingSlotlessClk / Tools.ShippingSlotlessKidFacts (kids_runFactsS, kids_designCheckS at the second disjunct, seqKid_of_leafAt), the built kids_outsCheck / kids_maskedN / leafKid_facts / machine_design_noPorts and the hand lemmas {hand}. The parent has no register: {nsT}. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. MachineClosesAt asked by the open form only. NO gap hypothesis; {lines.size} binders and antecedents of the closed form listed, 0 NOT ALLOWED. SCOPE: one declaration, depth 1, a parent WITHOUT a register under the general closing whose callees are all the leaf register machine {pe}; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim; the run, the reflections and ChildBnd remain premises. NOT covered: a parent without a register of combinational children."

end Tests.Compiler.NoPortsSlotlessLib
