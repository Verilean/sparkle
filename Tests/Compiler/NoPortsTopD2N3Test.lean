import Tests.Compiler.NoPortsTopD2Test

/-! # `topD2` at depth 3: the depth-3 endpoint without the four check premises (G1, unit U3, round par/a-16)

`topD2 → mid2 → midH → rcH`. `NoPortsTopD2Test` (BUILT, fcabc921) reaches
`topD2.machine_design_noPortsNR2`; `topD2.machine_design_svNR3`
(`Tests/Compiler/ShippingChildBoundaryTest.lean` 297, `#machine_design_svNR
topD2 3`, READ) is the same declaration one depth higher and keeps its four
check premises (MEASURED on its closed form: `verification-a14.md` 134–138).

This file IMPORTS `NoPortsTopD2Test` and reuses, unchanged:

    mid2_kid       GenKid … mid2 … 1        (its fields that do not mention the depth)
    mid2_entry, topD2_entry, topD2_callWidths, topD2_callArgs, topD2_outChars
    topD2_runFacts   RunFacts (childMap D.modules) b          — the statement has no depth
    topD2_maskedG    kidsMaskedN D.modules b.body = true      — the statement has no depth
    generateX, closeDeepX

New constants (namespace `Tests.Compiler.NoPortsTopD2N3Test`; none of the
NR2 names is redefined):

* `mid2_kid2`: `GenKid … mid2 … 2` — every field of `mid2_kid` that does not
  depend on the depth, `kidsLo := (mid2_kid …).kidsHi` (`KidFacts midH … 2`),
  `kidsHi` by `Tools.ShippingOneOutKidDepth.factsN (midH_kid …) 2`
  (`KidFacts midH … 3`).
* `topD2_kids3`: `KidFacts` of every call entry's callee at depth 3
  (`GenKid.facts` at `n = 2`).
* `topD2_outsG3`, `topD2_designP3` (`kids_outsCheck`, `kids_designCheck` at
  depth 3).
* `topD2.machine_design_noPortsNR3` (`generateX … 3`, the same two extra
  binders) and its `_closed` (`closeDeepX` over the BUILT
  `topD2.closes_deep`).

## READ vs INFERRED

READ (BUILT logs): `topD2.machine_design_svNR3` and `…_svNR3_closed` exist;
the closed form keeps `shipsHierCheck`, `designCheck … 3`, `outsCheck … 3`,
`kidsMaskedN` and its boundary reduces to `ChildBnd` under the four
reflection binders (`verification-a14.md` 134–138). `topD2`: `nDecl = 1`,
entries all `mid2`; `mid2`: `nDecl = 2`, entries all `midH` (asserted by the
BUILT `NoPortsTopD2Test`).
INFERRED (asserted by the first `run_cmd`): `topD2.machine_ships_hierNR3`
exists and has the shape `generateX` asks (`machine_ships_hierC`, 25
arguments, 11 binders) — `#machine_design_svNR` leaves it for depth 2
(BUILT), for depth 3 it is not in a log.
INFERRED: `KidFacts … (1 + 1)` is accepted where `KidFacts … 2` is asked, and
`(2 + 1)` where `3` is (the first was accepted in the BUILT `topD2_kids`).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `topD2.machine_design_svNR3` | predicted state |
|---|---|---|
| `topD2.machine_design_noPortsNR3` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 3 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 3 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt topD2` (open form) | predicted absent in `_closed` (`topD2.closes_deep`, BUILT), pending build |
| | the boundary | STAYS in this file, unchanged (reduced in `NoPortsTopD2N3BTest`) |
| | `hr`, `MachineDefines topD2` | stay |
| | — | ADDED to the open form: `MachineDefines midH` and `EntryDefines rcH` at the run's contexts (binders of the base CLOSED endpoint already) |

## SCOPE (binding for any report)

ONE declaration, `topD2`, at depth 3 (its depth-2 endpoint is
`NoPortsTopD2Test`). Everything else as there: data conditions decided per
declaration are conditions, not reductions; the compiler's guards with
fallback; the conclusion is about `DesignSV (childMap D.modules) 3
(checkedOptimize b)` — the module list (children UNOPTIMISED), not the SV
string, not `#sim`. The run, the reflections and the boundary stay premises.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let r2 ← Tools.ShippingMachineCommand.readMachine m2
  let ge := rg.shape.insts.map (·.1)
  let e2 := r2.shape.insts.map (·.1)
  let need := [g ++ `closes_deep, g ++ `machine_ships_hierNR3, g ++ `machine_design_svNR3,
    ``Tests.Compiler.NoPortsTopD2Test.mid2_kid, ``Tests.Compiler.NoPortsTopD2Test.topD2_runFacts,
    ``Tests.Compiler.NoPortsTopD2Test.topD2_maskedG,
    ``Tests.Compiler.NoPortsGrandHTest.midH_kid, ``Tools.ShippingOneOutKidDepth.factsN]
  let mut present : List Lean.Name := []
  let mut absent : List Lean.Name := []
  for n in need do
    if (← Lean.getEnv).contains n then present := present ++ [n] else absent := absent ++ [n]
  Lean.logInfo m!"NOPORTS TOPD2 N3 DATA {g}: nDecl={rg.nDecl}, call entries {ge}, instFields={rg.shape.instFields}; {m2}: nDecl={r2.nDecl}, call entries {e2}, instFields={r2.shape.instFields}; {m}; in the imports: {present}; NOT in the imports: {absent}"
  unless absent.isEmpty do throwError "not in the imports (this file builds on them): {absent}"
  unless rg.nDecl == 1 do throwError "{g}: nDecl = {rg.nDecl}, the hand theorems are written for 1"
  unless ge.eraseDups == [m2] do
    throwError "{g}: the call entries are {ge}, expected every entry to be {m2}"
  unless e2.eraseDups == [m] do
    throwError "{m2}: the call entries are {e2}, expected every entry to be {m}"
  for n in [g ++ `machine_design_noPortsNR3, g ++ `machine_design_noPortsNR3_closed] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsTopD2N3Test
open Tools.ShippingGenKid (GenKid)
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingCallsChildPorts (argWidths)
open Tests.Compiler.NoPortsGrandHTest (midH_kid)
open Tests.Compiler.NoPortsTopD2Test (mid2Names mid2_kid mid2_entry topD2_entry topD2_callWidths
  topD2_callArgs topD2_outChars)

set_option maxHeartbeats 4000000 in
/-- **`mid2` as a child, one depth higher**: the fields of the BUILT
`mid2_kid` that do not mention the depth; `KidFacts` of `midH` at depth 2 is
its `kidsHi`, at depth 3 `Tools.ShippingOneOutKidDepth.factsN … 2`. -/
theorem mid2_kid2 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    GenKid mref cref ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2 mid2Names
      (fun _ =>
        (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape.layout.outs)
      (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData 2)
      2 :=
  have K := mid2_kid hRm2 hRm hRr
  { ok := K.ok
    body := K.body
    calls := K.calls
    ss := K.ss
    dom := K.dom
    insts := K.insts
    general := K.general
    slots := K.slots
    outTy := K.outTy
    outName := K.outName
    outScalar := K.outScalar
    nomem := K.nomem
    hkD := K.hkD
    hIlen := K.hIlen
    hSL := K.hSL
    hSlen := K.hSlen
    hLlen := K.hLlen
    hNIn := K.hNIn
    kid := K.kid
    self := K.self
    kidsLo := K.kidsHi
    kidsHi := by
      intro k hk
      rw [mid2_entry k hk]
      exact Tools.ShippingOneOutKidDepth.factsN (midH_kid hRm hRr) 2
    callW := K.callW
    callA := K.callA
    entry := K.entry
    closes := K.closes }

/-- **`KidFacts` of every call entry's callee of `topD2`**, three levels of
check below it (`GenKid.facts` at `n = 2`). -/
theorem topD2_kids3 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.insts.length),
      KidFacts mref cref
        ((Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.insts[k]).1
        (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs
        (argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 3 := by
  intro k hk
  rw [topD2_entry k hk]
  exact (mid2_kid2 hRm2 hRm hRr).facts

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 3 under the statement-kind gate**
(`kids_outsCheck`). -/
theorem topD2_outsG3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 3
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 3
    (topD2_kids3 hRm2 hRm hRr)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 3 of the shipped module, with no check premise**
(`kids_designCheck`). -/
theorem topD2_designP3 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 3
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_designCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 3
    (topD2_kids3 hRm2 hRm hRr) topD2_callWidths topD2_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topD2_outChars o ho))
    (by decide)

end Tests.Compiler.NoPortsTopD2N3Test

/-! ## The endpoint and its closed form -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let extras (ctx : Array Lean.Expr) : Lean.Meta.MetaM (Array (Lean.Name × Lean.Expr)) := do
    let mshape ← Lean.Meta.mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
      #[Lean.mkConst (m ++ `machineData)]
    let tM ← Lean.Meta.mkAppM ``Tools.ShippingMachineEntry.MachineDefines
      (ctx ++ #[Lean.toExpr m, mshape])
    let tR ← Lean.Meta.mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
      (ctx ++ #[Lean.toExpr rc, Lean.mkConst (rc ++ `gateValue)])
    return #[(`hRm, tM), (`hRr, tR)]
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsTopD2Test.generateX g 3 extras
      ``Tests.Compiler.NoPortsTopD2Test.topD2_runFacts
      ``Tests.Compiler.NoPortsTopD2N3Test.topD2_outsG3
      ``Tests.Compiler.NoPortsTopD2Test.topD2_maskedG
      ``Tests.Compiler.NoPortsTopD2N3Test.topD2_designP3
  let closed := Tools.ShippingMachineClosesGen.closedName name
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsTopD2Test.closeDeepX g name (g ++ `closes_deep) closed 2
  Lean.logInfo m!"NOPORTS TOPD2 N3 [{name}, {closed}]: the depth-3 endpoint of topD2 without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mid2_kid2: GenKid at n = 2 from the fields of the BUILT mid2_kid, KidFacts of midH at depth 3 by Tools.ShippingOneOutKidDepth.factsN … 2; topD2_kids3: GenKid.facts; topD2_outsG3, topD2_designP3: kids_* at depth 3; the BUILT topD2_runFacts and topD2_maskedG, whose statements have no depth); two binders ADDED against the open base endpoint: the reflections of {m} and {rc} at the run's contexts"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let old := g ++ `machine_design_svNR3
  let openN := g ++ `machine_design_noPortsNR3
  let closed := g ++ `machine_design_noPortsNR3_closed
  -- (a) standard axioms
  for n in [``Tests.Compiler.NoPortsTopD2N3Test.mid2_kid2,
      ``Tests.Compiler.NoPortsTopD2N3Test.topD2_kids3,
      ``Tests.Compiler.NoPortsTopD2N3Test.topD2_outsG3,
      ``Tests.Compiler.NoPortsTopD2N3Test.topD2_designP3, openN, closed] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no endpoint statement mentions a checker constant
  for n in [openN, closed] do
    let ci ← Lean.getConstInfo n
    for k in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf k)).isSome then
        throwError "{n}: the statement mentions {k}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (c') the depth: the conclusion is about depth 3 (the literal 3 is an
  -- argument of DesignSV in the new statement as in the old one)
  let openT := (← Lean.getConstInfo openN).type
  let closedT := (← Lean.getConstInfo closed).type
  let depthOf (t : Lean.Expr) : Option Lean.Expr :=
    (t.find? fun e => e.isAppOf ``Tools.ShippingDesignSV.DesignSV && e.getAppNumArgs ≥ 2).map
      fun e => e.getAppArgs[1]!
  let some dOld := depthOf oldT | throwError "{old}: no DesignSV in the statement"
  let some dNew := depthOf closedT | throwError "{closed}: no DesignSV in the statement"
  if dOld.hasLooseBVars || dNew.hasLooseBVars then
    throwError "{closed}: the depth argument of DesignSV is not a closed term ({dNew} / {dOld})"
  unless ← Lean.Meta.isDefEq dOld dNew do
    throwError "{closed}: DesignSV at depth {dNew}, {old} at {dOld}"
  unless ← Lean.Meta.isDefEq dNew (Lean.mkNatLit 3) do
    throwError "{closed}: DesignSV at depth {dNew}, expected 3"
  -- (d) the closing: asked by the open form, not by the closed one
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt"
  if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closed}: still asks MachineClosesAt"
  -- (e) the binders of the closed form: the run, and reflections only
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
          for k in [g, m2, m, rc] do
            if (t.find? fun e => e == Lean.toExpr k).isSome then refl := refl ++ [k]
        else
          throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
    return (props, refl)
  unless nProps == 5 && refl.length == 4 && refl.contains g && refl.contains m2 &&
      refl.contains m && refl.contains rc do
    throwError "{closed}: {nProps} proposition binders, reflections of {refl}; expected the run and one reflection each of {g}, {m2}, {m}, {rc}"
  -- (f) the antecedents under the existentials: exactly one (the boundary)
  let inner ← Lean.Meta.forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerOld ← Lean.Meta.forallTelescope oldT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  unless inner.size == 1 do
    throwError "{closed}: {inner.size} antecedents under the existentials, expected 1 (the boundary)"
  let same := innerOld.any fun a => a.1 == inner[0]!.1
  -- (g) the complete premise list, with the goal-gap classifier's verdicts (LOGGED)
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.size ≤ 1 do
    throwError "{closed}: {bad.size} premises the classifier does not allow, expected at most the inherited boundary:\n{String.intercalate "\n" bad.toList}"
  Lean.logInfo m!"NOPORTS TOPD2 N3 AUDIT {g}: {openN} and {closed} on standard axioms, with GenKid.facts at n = 2, Tools.ShippingOneOutKidDepth.factsN, the kids_* theorems and the hand lemmas mid2_kid2, topD2_kids3, topD2_outsG3, topD2_designP3 (and the BUILT mid2_kid, topD2_runFacts, topD2_maskedG). No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. DesignSV at depth {dNew} in both. Closed form: {nProps} proposition binders — the run and the reflections of {refl}; MachineClosesAt asked by the open form only. Under the existentials: 1 antecedent, the boundary; printed the same as an antecedent of {old}: {same}. The goal-gap classifier lists {bad.size} premise(s) NOT ALLOWED in THIS closed form (the inherited boundary; its reduction is NoPortsTopD2N3BTest, not claimed here). ADDED against the open base endpoint: the reflections of {m} and {rc} at the run's contexts. SCOPE: one declaration at depth 3, a parent WITH a register under the general closing, one callee under the general closing whose callee is a register machine with a one-output call of a gate; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim."
