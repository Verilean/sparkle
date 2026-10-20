import Tests.Compiler.MemNameCollisionSatTest
import Tools.ShippingSatAssemblyS
-- BUILT by the integrator: sl1 exit 0 (675 jobs; audit passed) (round par/init phase 3).
-- Registered in Tests.AllTests (all6, 1446 jobs).
-- Writing-time guesses: (g1) `generateTopW` accepts the head `machine_design_noPortsTBS` (its
-- hypotheses are TBW's, in the same order; only the conclusion differs; (14) is stated without
-- `BoundOff`, so the refusal check does not fire); (g2) the `hRegs` lambda `fun hcore => …`
-- elaborates against the implicit binders `{raw D w1}`; (g3) `decide` proves the data conditions
-- `hinitW` (inits 0), `houtTy`, `hon` (`outNameOk` on the output names) on the concrete data.

/-! # The four collision parents through the TBS head and `sat_of_designClosedBS` (round par/init)

The route for nonzero slot inits, type-checked on the four collision parents (their inits are
`0`, so this exercises the route, not a nonzero value):

* `<p>_designClosedBS`: the generated chain of `MemNameCollisionSatTest` with the head
  `Tools.ShippingNoPortsTyped.machine_design_noPortsTBS` (target start state `stO`);
* `<p>_satS`: `Tools.ShippingSatAssemblyS.sat_of_designClosedBS` at it, with the run facts of
  `MemNameCollisionSatTest` plus `designCheck` (`<p>_designP0`) and `slotRegs_runMT`, and the data
  conditions `hinitW`, `houtTy`, `hon` by `decide`. The emitted text runs from
  `stOf b regs slots` (each slot register at its reset value; removed registers at 0).

A NONZERO-init instance parent needs, beyond this file, the same chain for that parent: its
`#machine_*` endpoints (`machine_ships_hierRG`, `machine_composedTRGA`), the run-fact lemmas
(`_runFacts`, `_outsG0`, `_typedRun`, `_designP0`, `_closesR`, `_names`, `_gate`, `_oi`,
`_inputWires`, `_kidsSat`) — the collision parents get them from the gate-certificate files —
and then the two commands below; nothing in L1–L6 depends on the init being 0. -/

/-! ## The TBS-headed endpoints, by the generator (the kernel checks the results) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  let sn := `Sparkle.Tests.Compiler.MemNameCollisionSatSTest
  for (p, cC, src, eqN, fN, tN, rN) in [(`collMixSame, `syncName, `fakeSrc, `syncGate_value, cn, yn, ns),
      (`collMixDiff, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collMixArgs, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collWidth, `comboName, `fakeN, `comboGate_value, an, an, an)] do
    let n ← Tools.ShippingGateTypedCommandW.generateTopW
      { parent := ns ++ p, name := sn ++ p.appendAfter "_designClosedBS",
        childConst := ns ++ cC, gateValue := ns ++ src ++ `gateValue,
        valueEq? := some (ns ++ eqN),
        runFacts := fN ++ p.appendAfter "_runFacts", outsG0 := fN ++ p.appendAfter "_outsG0",
        typedRun := tN ++ p.appendAfter "_typedRun", designP0 := fN ++ p.appendAfter "_designP0",
        closesR := rN ++ p.appendAfter "_closesR",
        head := ``Tools.ShippingNoPortsTyped.machine_design_noPortsTBS,
        names? := some (bn ++ p.appendAfter "_names") }
    Lean.logInfo m!"GATESATS [{n}]: head machine_design_noPortsTBS"

/-! ## The satisfaction theorems (one elaborated term each; the statement is its type) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixSame_satS (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssemblyS.sat_of_designClosedBS
      (Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixSame_designClosedBS hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixSame_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixSame_kidsSat hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.collMixSame_designP0 hcore hpost entry hR0 hB)
      (fun hcore => Tools.ShippingSlotRegsRun.slotRegs_runMT (nDecl := 3)
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machineData Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machine_body
        (by first | decide | decide +kernel) (by first | decide | decide +kernel)
        (by first | decide | decide +kernel)
        hB hcore entry (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame_closesR hR0))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixDiff_satS (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssemblyS.sat_of_designClosedBS
      (Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixDiff_designClosedBS hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixDiff_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixDiff_kidsSat hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collMixDiff_designP0 hcore hpost entry hR0 hB)
      (fun hcore => Tools.ShippingSlotRegsRun.slotRegs_runMT (nDecl := 3)
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machineData Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machine_body
        (by first | decide | decide +kernel) (by first | decide | decide +kernel)
        (by first | decide | decide +kernel)
        hB hcore entry (Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collMixDiff_closesR hR0))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixArgs_satS (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssemblyS.sat_of_designClosedBS
      (Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixArgs_designClosedBS hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixArgs_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixArgs_kidsSat hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collMixArgs_designP0 hcore hpost entry hR0 hB)
      (fun hcore => Tools.ShippingSlotRegsRun.slotRegs_runMT (nDecl := 3)
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machineData Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machine_body
        (by first | decide | decide +kernel) (by first | decide | decide +kernel)
        (by first | decide | decide +kernel)
        hB hcore entry (Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collMixArgs_closesR hR0))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collWidth_satS (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.comboName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeN.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssemblyS.sat_of_designClosedBS
      (Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collWidth_designClosedBS hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collWidth_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collWidth_kidsSat hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collWidth_designP0 hcore hpost entry hR0 hB)
      (fun hcore => Tools.ShippingSlotRegsRun.slotRegs_runMT (nDecl := 3)
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machineData Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machine_body
        (by first | decide | decide +kernel) (by first | decide | decide +kernel)
        (by first | decide | decide +kernel)
        hB hcore entry (Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collWidth_closesR hR0))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)))

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let sn := `Sparkle.Tests.Compiler.MemNameCollisionSatSTest
  for n in [``Tools.ShippingNoPortsTyped.machine_design_noPortsTBS,
      ``Tools.ShippingHierOptRunS.hierRefineCheck_linkedS,
      ``Tools.ShippingNonzeroInitWidths.weS_driven_checkedOptimize,
      ``Tools.ShippingSlotRegsRun.slotRegs_runMT, ``Tools.ShippingSatAssemblyS.sat_of_designClosedBS] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  for p in [`collMixSame, `collMixDiff, `collMixArgs, `collWidth] do
    for suf in ["_designClosedBS", "_satS"] do
      Tests.Compiler.NoPortsTest.stdAxioms (sn ++ p.appendAfter suf)
    let t := (← Lean.getConstInfo (sn ++ p.appendAfter "_satS")).type
    for k in [``Tools.ShippingDesignSVBounds.InvN, ``Tools.ShippingMachineShipsHier.Reset1,
        ``Tools.ShippingSeqOptSoundness.seedIn] do
      let prem ← Lean.Meta.forallTelescope t fun xs _ => do
        let mut found := false
        for x in xs do
          if ((← Lean.Meta.inferType x).find? (·.isConstOf k)).isSome then found := true
        pure found
      if prem then throwError "{p}_satS: a premise mentions {k}"
    Lean.logInfo m!"GATESATS {p}_satS: {t}"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionSatSTest.collMixSame_satS
