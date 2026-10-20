import Tests.Compiler.NonzeroInitParentTest
import Tools.ShippingSatCertS
import Tools.ShippingSatCertSCommand
-- BUILT by the integrator: cs3 exit 0 (685 jobs; audit passed, axioms standard); writing-time guesses accepted; (round par/certs, base aa35e8a6).
-- Registered in Tests.AllTests (all7, 1451 jobs).
-- Writing-time guesses:
--   (t1) `collMixSame5_cert` by `decide` as `MemNameCollisionGateCertGenTest`'s `collMixSame_cert`
--        (same tables `outsG` / `insG`; the data differ only in the slot inits);
--   (t2) `generateCert2STop` succeeds on `collMixSame5` with `collMixSame`'s table row
--        (`MemNameCollisionSatCert2Test`), the closing `collMixSame5_closesR` (same binder shape
--        as `collMixSame_closesR`: implicit context, then `hR0`), and reuses
--        `collMixSame5.machine_composedTRGAW` (created by `NonzeroInitParentTest`'s `generateTopW`);
--   (t3) `collMixSame5_designClosedCS`'s type is `Expr`-equal to `collMixSame5_designClosedBS`'s
--        (same head, same arguments up to the discharged run hypotheses, same boundary merge, as
--        `designClosedCW` vs `designClosedBW`, built sc2);
--   (t4) the `satOfCertS` application elaborates as `satOfCert`'s in
--        `MemNameCollisionSatCert2Test` (built sc2); `outsF` / `insF` are given explicitly; the
--        four table equations are `rfl` (the generator uses `Eq.refl` for them); the `by` blocks
--        (`memGateOk`, `satDataOkS`) run after `d` / `kD` / `bs` / … are assigned;
--   (t5) `collMixSame5_satCS`'s type is `Expr`-equal to `collMixSame5_satS`'s (both are
--        `sat_of_designClosedBS`'s conclusion at the same `d`, `kD`, `src`, `ext`, `extB`, binders
--        copied verbatim).

/-! # The nonzero-init parent `collMixSame5` from DATA ONLY (round par/certs)

`collMixSame5_satS` (`NonzeroInitParentTest`) applies `sat_of_designClosedBS` to ~17 hand-written
per-parent lemmas (`_runFacts`, `_outsG0`, `_designP0`, `_typedRun`, `_names`, `_gate`, `_oi`,
`_inputWires`, `_kidsSat`, `_kidNoRegs`, `_kids`, `_kidTyped`, `_entry`, `_outChars`,
`_callWidths`, `_callArgs`) through `collMixSame5_designClosedBS`. Here:

* `collMixSame5_cert` — `gateParentCertOk` (one `decide`);
* `collMixSame5_designClosedCS` — `Tools.ShippingSatCertSCommand.generateCert2STop` (data route,
  head `machine_design_noPortsTBS`); statement asserted `Expr`-equal to `collMixSame5_designClosedBS`'s;
* `collMixSame5_satCS` — ONE application of `Tools.ShippingSatCertS.satOfCertS`; statement asserted
  `Expr`-equal to `collMixSame5_satS`'s.

Per parent the inputs are ONLY: the data (the certificate, `memGateOk` and `satDataOkS` by
`decide`, the reader facts `machine_ok` / `machine_body`, the tables `outsG` / `insG`, the memory
origin `false 4 8`, the gate source's `gate_old` / `gate_peel` / `gate_wf`), the closing
`collMixSame5_closesR`, the value equation `syncGate_value`, and the outer premises `hr`, `entry`,
`hR0`, `hB`. The generator-produced endpoints of `NonzeroInitParentTest` (`#machine_endpoint`,
`#machine_composedTRG`, `#machine_design_svRG0`, `machine_composedTRGAW`) are reused, not re-run.

GLOBAL NAMES added: `Sparkle.Tests.Compiler.NonzeroInitCertTest.collMixSame5_cert`,
`.collMixSame5_designClosedCS`, `.collMixSame5_satCS`. -/

namespace Sparkle.Tests.Compiler.NonzeroInitCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.NonzeroInitParentTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGateCert (gateParentCertOk)

/-! ## The certificate (one `decide`; writing-time guess t1) -/

set_option maxHeartbeats 4000000 in
theorem collMixSame5_cert : gateParentCertOk collMixSame5.machineData 3
    (fun k => outsG (originAt (collMixSame5.machineData).shape k))
    (fun k => insG (originAt (collMixSame5.machineData).shape k)) = true := by
  first | decide | decide +kernel

end Sparkle.Tests.Compiler.NonzeroInitCertTest

/-! ## The TBS-headed endpoint from data (writing-time guesses t2, t3) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let me := `Sparkle.Tests.Compiler.NonzeroInitParentTest
  let s3 := `Sparkle.Tests.Compiler.NonzeroInitCertTest
  let p := `collMixSame5
  let n ← Tools.ShippingSatCertSCommand.generateCert2STop
    { parent := me ++ p, name := s3 ++ p.appendAfter "_designClosedCS",
      childConst := ns ++ `syncName, gateValue := ns ++ `fakeSrc ++ `gateValue,
      valueEq? := some (ns ++ `syncGate_value),
      closesR := me ++ p.appendAfter "_closesR",
      src := ns ++ `fakeSrc, outsF := cn ++ `outsG, insF := cn ++ `insG,
      cb := false, aw := 4, dw := 8, nDecl := 3, cert? := some (s3 ++ p.appendAfter "_cert") }
  Lean.logInfo m!"NZCERT [{n}]: TBS head from data (memory false 4 8, child syncName, source fakeSrc); certificate collMixSame5_cert; closing collMixSame5_closesR"

/-! ## The satisfaction theorem: ONE application of `satOfCertS` (writing-time guess t4) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- binders copied verbatim from `NonzeroInitParentTest`'s `collMixSame5_satS`
  addSat
    `Sparkle.Tests.Compiler.NonzeroInitCertTest.collMixSame5_satCS (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5
        (Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatCertS.satOfCertS (cb := false) (aw := 4) (dw := 8)
      (outsF := Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.outsG)
      (insF := Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.insG)
      (Sparkle.Tests.Compiler.NonzeroInitCertTest.collMixSame5_designClosedCS hr entry hR0) hB
      Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machine_ok
      Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machine_body
      Sparkle.Tests.Compiler.NonzeroInitCertTest.collMixSame5_cert
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      rfl rfl rfl rfl
      hR0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_old
      Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_peel
      Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gate_wf
      (Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5_closesR hR0) entry hB))

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let me := `Sparkle.Tests.Compiler.NonzeroInitParentTest
  let s3 := `Sparkle.Tests.Compiler.NonzeroInitCertTest
  let p := `collMixSame5
  let cs := s3 ++ p.appendAfter "_designClosedCS"
  let sat := s3 ++ p.appendAfter "_satCS"
  Tests.Compiler.NoPortsTest.stdAxioms (s3 ++ p.appendAfter "_cert")
  -- (a) the statements, as `Expr`s (writing-time guesses t3, t5)
  for (fin, old) in [(cs, me ++ p.appendAfter "_designClosedBS"), (sat, me ++ p.appendAfter "_satS")] do
    Tests.Compiler.NoPortsTest.stdAxioms fin
    let finT ← Lean.instantiateMVars (← Lean.getConstInfo fin).type
    let oldT ← Lean.instantiateMVars (← Lean.getConstInfo old).type
    unless finT == oldT do
      throwError "{fin}: its type is not Expr-equal to {old}'s"
  -- (b) no hand-written per-parent lemma in either proof
  let mut forbidden : List Lean.Name :=
    [me ++ p.appendAfter "_designClosedBS", me ++ p.appendAfter "_satS", cn ++ `fakeSrc_width]
  for suf in ["_runFacts", "_outsG0", "_designP0", "_typedRun", "_names", "_gate", "_oi",
      "_inputWires", "_kidsSat", "_kidNoRegs", "_kids", "_kidTyped", "_entry", "_outChars",
      "_callWidths", "_callArgs"] do
    forbidden := (me ++ p.appendAfter suf) :: (ns ++ (`collMixSame).appendAfter suf) :: forbidden
  for fin in [cs, sat] do
    let some (.thmInfo fi) := (← Lean.getEnv).find? fin | throwError "{fin}: not a theorem"
    for k in forbidden do
      if (fi.value.find? (·.isConstOf k)).isSome then
        throwError "{fin}: the proof uses the hand-written {k}"
  -- (c) the routes used
  let some (.thmInfo vc) := (← Lean.getEnv).find? cs | throwError "{cs}: not a theorem"
  for k in [``Tools.ShippingGateCert2.memGate_kidsS, ``Tools.ShippingGateCert2.memGate_kidTypedS,
      ``Tools.ShippingGateCert.gateParent_runFacts, ``Tools.ShippingGateCert.gateParent_outsG0,
      ``Tools.ShippingGateCert.gateParent_designP0, ``Tools.ShippingGateCert.gateParent_typedRun,
      ``Tools.ShippingGateCert.gateParent_names, ``Tools.ShippingNoPortsTyped.machine_design_noPortsTBS,
      s3 ++ p.appendAfter "_cert"] do
    unless (vc.value.find? (·.isConstOf k)).isSome do
      throwError "{cs}: the proof does not use {k}"
  let some (.thmInfo vs) := (← Lean.getEnv).find? sat | throwError "{sat}: not a theorem"
  for k in [``Tools.ShippingSatCertS.satOfCertS, cs, s3 ++ p.appendAfter "_cert"] do
    unless (vs.value.find? (·.isConstOf k)).isSome do
      throwError "{sat}: the proof does not use {k}"
  -- the start state of the conclusion is `stOf b regs slots` (nonzero inits, `collMixSame5_initNZ`)
  let t := (← Lean.getConstInfo sat).type
  unless (t.find? (·.isConstOf ``Tools.ShippingSatAssemblyS.stOf)).isSome do
    throwError "{sat}: the conclusion does not mention stOf"
  Lean.logInfo m!"NZCERT AUDIT: {cs} Expr-equal to collMixSame5_designClosedBS, {sat} Expr-equal to collMixSame5_satS; standard axioms; no hand-written per-parent run/kid/entry lemma and no designClosedBS in either proof"

#print axioms Sparkle.Tests.Compiler.NonzeroInitCertTest.collMixSame5_satCS
