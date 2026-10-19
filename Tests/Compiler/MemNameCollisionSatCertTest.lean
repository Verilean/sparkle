import Tests.Compiler.MemNameCollisionSatTest
import Tests.Compiler.MemNameCollisionGateCertGenTest
import Tools.ShippingSatCert
-- BUILT by the integrator: sc1 exit 0 (675 jobs, axioms standard; round par/satc, base 87874a82).
-- Writing-time guesses:
--   (t1) each `satOfCert` application elaborates with its implicit arguments found by unification
--        with `<p>_designClosedBW hr entry hR0` (as `sat_of_designClosedBW`'s in
--        `MemNameCollisionSatTest`, built sa1/sa2); the `by` blocks (`memGateOk`, `satDataOk`) are
--        elaborated last by `addSat`'s `synthesizeSyntheticMVarsNoPostponing`;
--   (t2) `first | decide | decide +kernel` evaluates `memGateOk …` (the generator of
--        `MemNameCollisionGateCert2Test` proves the same Bool by kernel `Eq.refl true`) and
--        `satDataOk …` (the same conditions `MemNameCollisionSatTest` decides one by one);
--   (t3) the audit's `==` (`Expr.eqv`, binder names ignored) holds because the binders are copied
--        verbatim from `<p>_sat` and both bodies are the instantiated conclusion of the same
--        statement text (`satOfCert`'s conclusion is `sat_of_designClosedBW`'s, character for
--        character, under the same `open`s);
--   (t4) co-import of `MemNameCollisionSatTest` and `MemNameCollisionGateCertGenTest` (both already
--        in `Tests/AllTests.lean`); `addSat` is `MemNameCollisionSatTest`'s root-level helper.

/-! # The four collision parents' satisfaction theorems from the certificate (round par/satc)

`<p>_sat` (`MemNameCollisionSatTest`) applies `sat_of_designClosedBW` to the hand-written per-parent
run facts `<p>_gate`, `<p>_oi`, `<p>_inputWires`, `<p>_kidsSat` (through `<p>_kidNoRegs`) and
`<p>_names`. Here `<p>_satC` is ONE application of the generic
`Tools.ShippingSatCert.satOfCert` per parent, to:

| parent | memory origin | child const | gate source | certificate | closing |
|---|---|---|---|---|---|
| `collMixSame` | `.mem false 4 8` | `syncName` | `fakeSrc` | `collMixSame_cert` | `collMixSame_closesR` |
| `collMixDiff` | `.mem true 4 8` | `syncName` | `fakeSrc` | `collMixDiff_cert` | `collMixDiff_closesR` |
| `collMixArgs` | `.mem false 4 8` | `syncName` | `fakeSrc` | `collMixArgs_cert` | `collMixArgs_closesR` |
| `collWidth` | `.mem true 4 8` | `comboName` | `fakeN` | `collWidth_cert` | `collWidth_closesR` |

(`<p>_cert : gateParentCertOk …`, `MemNameCollisionGateCertGenTest`), `memGateOk …` and
`satDataOk …` decided inline, the parent's `machine_ok` / `machine_body`, the gate source's
`gate_old` / `gate_peel` / `gate_wf`, the head's conclusion `<p>_designClosedBW hr entry hR0`.

STILL per parent: the closing `<p>_closesR`, the reflection binder `hR0` (a premise), the value
equation (inside the generated `<p>_designClosedBW`), and the data above. `<p>_designClosedBW` is
still generated from the hand-written run lemmas (`generateTopW`); OPEN: its certificate route.

SCOPE: `memGateOk` covers parents with a single gate child and a single memory origin, data
(gate result) width ≠ 1; the certificate does NOT cover all compiler-accepted inputs; `hinit`
(slot inits `0`) remains a restriction of `sat_of_designClosedBW`.

The audit asserts per parent: the type of `<p>_satC` is `Expr`-equal (`==`) to that of `<p>_sat`;
standard axioms; the proof mentions none of `<p>_gate`, `<p>_oi`, `<p>_inputWires`, `<p>_kidsSat`,
`<p>_kidNoRegs`, `<p>_names`, `<p>_entry`, `<p>_outChars`, `fakeSrc_width`, `fakeN_width`; it does
mention `satOfCert` and the certificate `<p>_cert` (`memGateOk` / `satDataOk` are proved inline).

GLOBAL NAMES added: `Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.<p>_satC` (new namespace;
added by `addSat`). -/

/-! ## The satisfaction theorems, one application of `satOfCert` each -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- binders copied verbatim from `MemNameCollisionSatTest`'s `collMixSame_sat`; body: ONE application of
  -- `satOfCert` (writing-time guess t1: implicit args found by unification with
  -- `collMixSame_designClosedBW`; the two `by` blocks run last, after `d`/`kD`/`bs`/… are assigned)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collMixSame_satC (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingSatCert.satOfCert (cb := false) (aw := 4) (dw := 8)
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_designClosedBW hr entry hR0) hB
      Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machine_body
      Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collMixSame_cert
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      hR0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_old Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_peel Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_wf
      (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame_closesR hR0) entry hB))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- binders copied verbatim from `MemNameCollisionSatTest`'s `collMixDiff_sat`; body: ONE application of
  -- `satOfCert` (writing-time guess t1: implicit args found by unification with
  -- `collMixDiff_designClosedBW`; the two `by` blocks run last, after `d`/`kD`/`bs`/… are assigned)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collMixDiff_satC (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingSatCert.satOfCert (cb := true) (aw := 4) (dw := 8)
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_designClosedBW hr entry hR0) hB
      Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machine_body
      Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collMixDiff_cert
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      hR0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_old Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_peel Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_wf
      (Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collMixDiff_closesR hR0) entry hB))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- binders copied verbatim from `MemNameCollisionSatTest`'s `collMixArgs_sat`; body: ONE application of
  -- `satOfCert` (writing-time guess t1: implicit args found by unification with
  -- `collMixArgs_designClosedBW`; the two `by` blocks run last, after `d`/`kD`/`bs`/… are assigned)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collMixArgs_satC (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingSatCert.satOfCert (cb := false) (aw := 4) (dw := 8)
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_designClosedBW hr entry hR0) hB
      Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machine_body
      Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collMixArgs_cert
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      hR0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_old Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_peel Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_wf
      (Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collMixArgs_closesR hR0) entry hB))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- binders copied verbatim from `MemNameCollisionSatTest`'s `collWidth_sat`; body: ONE application of
  -- `satOfCert` (writing-time guess t1: implicit args found by unification with
  -- `collWidth_designClosedBW`; the two `by` blocks run last, after `d`/`kD`/`bs`/… are assigned)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collWidth_satC (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingSatCert.satOfCert (cb := true) (aw := 4) (dw := 8)
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_designClosedBW hr entry hR0) hB
      Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machine_ok Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machine_body
      Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collWidth_cert
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      hR0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeN.gate_old Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeN.gate_peel Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeN.gate_wf
      (Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest.collWidth_closesR hR0) entry hB))

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  let sn := `Sparkle.Tests.Compiler.MemNameCollisionSatTest
  let kn := `Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest
  let gn := `Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
  let sc := `Sparkle.Tests.Compiler.MemNameCollisionSatCertTest
  for n in [``Tools.ShippingSatCert.satData_of_ok, ``Tools.ShippingSatCert.memGate_kidNoRegsS,
      ``Tools.ShippingSatCert.satOfCert] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  for p in [`collMixSame, `collMixDiff, `collMixArgs, `collWidth] do
    let fin := sc ++ p.appendAfter "_satC"
    let old := sn ++ p.appendAfter "_sat"
    Tests.Compiler.NoPortsTest.stdAxioms fin
    let some (.thmInfo fi) := (← Lean.getEnv).find? fin | throwError "{fin}: not a theorem"
    let finT ← Lean.instantiateMVars fi.type
    let oldT ← Lean.instantiateMVars (← Lean.getConstInfo old).type
    -- (a) the same statement, as an `Expr`
    unless finT == oldT do
      throwError "{fin}: its type is not Expr-equal to {old}'s"
    -- (b) no hand-written per-parent run fact in the proof (any namespace they could live in)
    let mut forbidden : List Lean.Name :=
      [sn ++ p.appendAfter "_gate", sn ++ p.appendAfter "_oi", sn ++ p.appendAfter "_inputWires",
       kn ++ p.appendAfter "_kidsSat", kn ++ p.appendAfter "_kidNoRegs",
       bn ++ p.appendAfter "_names", cn ++ `fakeSrc_width, an ++ `fakeN_width]
    for hN in [ns, cn, an] do
      forbidden := forbidden ++ [hN ++ p.appendAfter "_entry", hN ++ p.appendAfter "_outChars"]
    for k in forbidden do
      if (fi.value.find? (·.isConstOf k)).isSome then
        throwError "{fin}: the proof uses the hand-written {k}"
    -- (c) the generic route is the one used
    -- (`memGateOk` / `satDataOk` are not required to appear: `decide +kernel` may close them by an
    -- auxiliary lemma)
    for k in [``Tools.ShippingSatCert.satOfCert, gn ++ p.appendAfter "_cert"] do
      unless (fi.value.find? (·.isConstOf k)).isSome do
        throwError "{fin}: the proof does not use {k}"
    Lean.logInfo m!"SATCERT AUDIT {fin}: type Expr-equal to {old}; standard axioms; no hand-written gate/oi/inputWires/kidsSat/kidNoRegs/names/entry/outChars in the proof; one satOfCert application"

#print axioms Tools.ShippingSatCert.satOfCert
#print axioms Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collMixSame_satC
#print axioms Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collMixDiff_satC
#print axioms Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collMixArgs_satC
#print axioms Sparkle.Tests.Compiler.MemNameCollisionSatCertTest.collWidth_satC
