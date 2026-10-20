import Tests.Compiler.NoPortsGrandHBTest
import Tools.ShippingNoPortsKidsCommand

/-! # `#machine_no_ports_kids`: the generator for callees of two kinds (G1, round par/a-14)

`Tools/ShippingNoPortsKidsCommand.lean` on:

* `grandH` at depth 1 — the COMPARE path: `grandH.machine_design_noPortsNR1`
  and its `_closed` exist (hand, BUILT, `NoPortsGrandHTest`). The command
  rebuilds both statements from its own generated lemmas
  (`midH.machine_oneOutKid`, `grandH.machine_kidsK1`, `…_runFactsK1`,
  `…_outsGK1`, `…_maskedGK1`, `…_designPK1`), adds them as `…_regen`
  (kernel-checked) and REQUIRES `isDefEq` with the existing statements.
* `mixD1` at depth 1 — GENERATED here (`midH`: one-output; `cnt`: leaf).
  NAME CLASH: `Tests/Compiler/NoPortsMixD1Test.lean` (the hand version) adds
  the same two constants; this file does not import it and the two must
  never be imported together (one of them target-built only).
  Then the boundary of `mixD1`'s closed form is reduced
  (`#machine_boundary_close`) and its goal-gap theorem generated.
* refusals, LOGGED (`_try`): `topD2` 2, `mixDeep` 2 (callee `mid2`: calls
  under the general closing), `grand` 2 (callee `mid`: the same).
* leaf-only parents, LOGGED ONLY (`_try`, compare path against
  `#machine_no_ports`'s endpoints; whether the closed forms agree is NOT
  predicted — `closeEndpointAt`'s binder order was not read): `parent` 1.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| declaration | endpoint | premise (of `f.machine_design_svNR1`) | predicted state |
|---|---|---|---|
| `grandH` | `grandH.machine_design_noPortsNR1(_closed)` | — | nothing new removed: REBUILT, statements `isDefEq` the BUILT ones (`…_regen` added) |
| `mixD1` | `mixD1.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | | `MachineClosesAt mixD1` | predicted absent in `_closed` (`mixD1.closes_deep`), pending build |
| | `mixD1.machine_design_noPortsNR1_closedB` (+ `_gap`) | the boundary's `MachineDefines midH`, `MachineDefines cnt`, `True`, ∀-contexts conjunct | predicted absent from the antecedent (only `ChildBnd` stays); 0 NOT ALLOWED; no gap hypothesis |
| `topD2`, `mixDeep`, `grand` | — | — | REFUSED with a reason line; nothing added |

SCOPE: as `NoPortsGrandHTest` / `NoPortsMixD1Test` — one declaration each,
a parent WITH a register under the general closing, depth 1, callees: leaf
register machines or register machines with one-output calls of ONE gate
child; data conditions decided per declaration; compiler guards with
fallback; `DesignSV` of the module list, not the SV string, not `#sim`; the
run, the reflections and `ChildBnd` remain premises.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_kids Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_kids Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 1

set_option maxHeartbeats 0 in
#machine_no_ports_kids_try Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 2
set_option maxHeartbeats 0 in
#machine_no_ports_kids_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep 2
set_option maxHeartbeats 0 in
#machine_no_ports_kids_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_kids_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

set_option maxHeartbeats 0 in
#machine_boundary_close
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closedB

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let gH := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  let mx := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  -- (1) grandH: the compare path RAN (the rebuilt theorems exist) and agrees
  for s in ["machine_design_noPortsNR1", "machine_design_noPortsNR1_closed"] do
    let e := gH ++ Lean.Name.mkSimple s
    let r := gH ++ Lean.Name.mkSimple (s ++ "_regen")
    unless (← Lean.getEnv).contains r do
      throwError "{r}: missing — the compare path did not rebuild {e}"
    Tests.Compiler.NoPortsTest.stdAxioms r
    unless ← Lean.Meta.isDefEq (← Lean.getConstInfo e).type (← Lean.getConstInfo r).type do
      throwError "{r}: its statement is not that of {e}"
  -- (2) the generated lemmas, on standard axioms
  for n in [m ++ `machine_oneOutKid, gH ++ `machine_kidsK1, gH ++ `machine_runFactsK1,
      gH ++ `machine_outsGK1, gH ++ `machine_maskedGK1, gH ++ `machine_designPK1,
      mx ++ `machine_kidsK1, mx ++ `machine_runFactsK1, mx ++ `machine_outsGK1,
      mx ++ `machine_maskedGK1, mx ++ `machine_designPK1,
      ``Tools.ShippingLeafKidFacts.leafKid_facts] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (3) mixD1: GENERATED (no `_regen`), no checker, the four of the base endpoint
  let old := mx ++ `machine_design_svNR1
  let openN := mx ++ `machine_design_noPortsNR1
  let closed := mx ++ `machine_design_noPortsNR1_closed
  for n in [openN, closed] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
    let ci ← Lean.getConstInfo n
    for k in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf k)).isSome then throwError "{n}: the statement mentions {k}"
  if (← Lean.getEnv).contains (mx ++ `machine_design_noPortsNR1_regen) then
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
  -- the binders of the closed form: the run and reflections only
  let (nProps, refl) ← Lean.Meta.forallTelescope closedT fun xs _ => do
    let mut props : Nat := 0
    let mut refl : List Lean.Name := []
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then
        props := props + 1
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then pure ()
        else if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
            t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then
          for k in [mx, m, c, rc] do
            if (t.find? fun e => e == Lean.toExpr k).isSome then refl := refl ++ [k]
        else
          throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
    return (props, refl)
  unless nProps == 5 && refl.length == 4 && refl.contains mx && refl.contains m &&
      refl.contains c && refl.contains rc do
    throwError "{closed}: {nProps} proposition binders, reflections of {refl}; expected the run and one reflection each of {mx}, {m}, {c}, {rc}"
  -- (4) the refused declarations left nothing
  for (f, n) in [(``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 2),
      (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep, 2),
      (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, 2)] do
    for s in [s!"machine_design_noPortsNR{n}", s!"machine_kidsK{n}", s!"machine_runFactsK{n}"] do
      if (← Lean.getEnv).contains (f ++ Lean.Name.mkSimple s) then
        throwError "{f}: {s} exists — it was not refused"
  -- (5) mixD1's reduced boundary and its goal gap
  let closedB := mx ++ `machine_design_noPortsNR1_closedB
  let gap := mx ++ `machine_design_noPortsNR1_closedB_gap
  let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  Lean.logInfo m!"NOPORTS KIDS FAMILY: {gH} — COMPARE path, both statements rebuilt by the generator and isDefEq the hand ones (nothing new removed). {mx} — GENERATED: {openN} and {closed} on standard axioms, no statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck; closed form: {nProps} proposition binders (the run and the reflections of {refl}); {closedB}: ONE antecedent under the existentials, ChildBnd; {lines.size} premises listed, 0 NOT ALLOWED; {gap}: no gap hypothesis. REFUSED with reasons (logged above), nothing added: topD2, mixDeep, grand. SCOPE: one declaration each, a parent WITH a register under the general closing, depth 1, callees = leaf register machines or register machines with one-output calls of ONE gate child; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim; the run, the reflections and ChildBnd remain premises."
