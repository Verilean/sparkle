import Tests.Compiler.MemNameCollisionGateBoundTest
import Tools.ShippingGateCertCommand
-- Round par/cert. BUILT: ce1 (Tools.ShippingGateCert, …CertCommand, exit 0 for both; the test failed on missing `open`s), ce2 (the test, exit 0, 662 jobs; integrator fix: the opens repeated in the second namespace block).

/-! # The four gate-collision parents through the CERTIFICATE (round par/cert)

`<p>_designClosedB` (`MemNameCollisionGateBoundTest`) was generated from FIVE hand-written run
lemmas per parent (`<p>_runFacts`, `_outsG0`, `_designP0`, `_typedRun`, `_names`). Here the same
four statements are re-derived as `<p>_designClosedC` by
`Tools.ShippingGateCertCommand.generateCert`, from

* ONE certificate per parent `<p>_cert : gateParentCertOk <p>.machineData 3 kidOuts kidIns = true`
  (one `decide`; `Tools.ShippingGateCert`), and
* the parent's existing kid facts (`<p>_kids`, `<p>_kidTyped`) and closing (`<p>_closesR`).

The five run lemmas are built inline from `gateParent_runFacts` / `_outsG0` / `_typedRun` /
`_designP0` / `_names`; no per-parent run lemma is used (asserted below on the proof terms).

The audit asserts per parent: the type of `<p>_designClosedC` is definitionally equal to that of
`<p>_designClosedB` (`isDefEq`; exact `Expr` equality is LOGGED), standard axioms only, and the
proof mentions none of the five hand-written run lemmas.

The `example`s at the end check that the generic kid facts `memGate_kids` / `memGate_kidTyped`
reproduce each parent's `<p>_kids` / `<p>_kidTyped` statement (from the decided entry table and
the gate facts), so a new parent of this form needs no hand-written kid proof either.

GLOBAL NAMES added: `Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.<p>_cert` and
`.<p>_designClosedC` for the four parents (new namespace). -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGateCert (gateParentCertOk)

/-! ## The certificates (one `decide` each) -/

set_option maxHeartbeats 4000000 in
theorem collMixSame_cert : gateParentCertOk collMixSame.machineData 3
    (fun k => outsG (originAt (collMixSame.machineData).shape k))
    (fun k => insG (originAt (collMixSame.machineData).shape k)) = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
theorem collMixDiff_cert : gateParentCertOk collMixDiff.machineData 3
    (fun k => outsG (originAt (collMixDiff.machineData).shape k))
    (fun k => insG (originAt (collMixDiff.machineData).shape k)) = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
theorem collMixArgs_cert : gateParentCertOk collMixArgs.machineData 3
    (fun k => outsG (originAt (collMixArgs.machineData).shape k))
    (fun k => insG (originAt (collMixArgs.machineData).shape k)) = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
theorem collWidth_cert : gateParentCertOk collWidth.machineData 3
    (fun k => outsFN (originAt (collWidth.machineData).shape k))
    (fun k => insFN (originAt (collWidth.machineData).shape k)) = true := by
  first | decide | decide +kernel

end Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest

/-! ## The endpoints, by the certificate generator (the kernel checks the results) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let gn := `Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
  -- (parent, child, source, value equation, namespace of _kids, of _kidTyped, of _closesR)
  for (p, cC, src, eqN, kN, tN, rN) in [(`collMixSame, `syncName, `fakeSrc, `syncGate_value, cn, yn, ns),
      (`collMixDiff, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collMixArgs, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collWidth, `comboName, `fakeN, `comboGate_value, an, an, an)] do
    let n ← Tools.ShippingGateCertCommand.generateCertTop
      { parent := ns ++ p, name := gn ++ p.appendAfter "_designClosedC",
        childConst := ns ++ cC, gateValue := ns ++ src ++ `gateValue,
        valueEq? := some (ns ++ eqN),
        cert := gn ++ p.appendAfter "_cert",
        kids := kN ++ p.appendAfter "_kids", kidTyped := tN ++ p.appendAfter "_kidTyped",
        closesR := rN ++ p.appendAfter "_closesR" }
    Lean.logInfo m!"GATECERT [{n}]: head machine_design_noPortsTB; the five run hypotheses from {p}_cert (gateParent_*), {p}_kids, {p}_kidTyped, {p}_closesR"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let gn := `Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
  for n in [``Tools.ShippingGateCert.gateParentFacts_of_ok,
      ``Tools.ShippingGateCert.gateParent_runFacts, ``Tools.ShippingGateCert.gateParent_outsG0,
      ``Tools.ShippingGateCert.gateParent_designP0, ``Tools.ShippingGateCert.gateParent_typedRun,
      ``Tools.ShippingGateCert.gateParent_names, ``Tools.ShippingGateCert.memGate_kids,
      ``Tools.ShippingGateCert.memGate_kidTyped] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (parent, namespace of the hand-written runFacts/outsG0/designP0, of typedRun)
  for (p, fN, tN) in [(`collMixSame, cn, yn), (`collMixDiff, an, an), (`collMixArgs, an, an),
      (`collWidth, an, an)] do
    let fin := gn ++ p.appendAfter "_designClosedC"
    let old := bn ++ p.appendAfter "_designClosedB"
    Tests.Compiler.NoPortsTest.stdAxioms (gn ++ p.appendAfter "_cert")
    Tests.Compiler.NoPortsTest.stdAxioms fin
    let some (.thmInfo fi) := (← Lean.getEnv).find? fin | throwError "{fin}: not a theorem"
    let finT ← Lean.instantiateMVars fi.type
    let oldT ← Lean.instantiateMVars (← Lean.getConstInfo old).type
    -- (a) the same statement
    unless ← Lean.Meta.isDefEq finT oldT do
      throwError "{fin}: its type is not definitionally equal to {old}'s"
    let exact := finT == oldT
    -- (b) the certificate route: no hand-written run lemma in the proof, the certificate is
    for k in [fN ++ p.appendAfter "_runFacts", fN ++ p.appendAfter "_outsG0",
        fN ++ p.appendAfter "_designP0", tN ++ p.appendAfter "_typedRun",
        bn ++ p.appendAfter "_names"] do
      if (fi.value.find? (·.isConstOf k)).isSome then
        throwError "{fin}: the proof uses the hand-written {k}"
    for k in [gn ++ p.appendAfter "_cert", ``Tools.ShippingGateCert.gateParent_runFacts,
        ``Tools.ShippingGateCert.gateParent_outsG0, ``Tools.ShippingGateCert.gateParent_designP0,
        ``Tools.ShippingGateCert.gateParent_typedRun, ``Tools.ShippingGateCert.gateParent_names] do
      unless (fi.value.find? (·.isConstOf k)).isSome do
        throwError "{fin}: the proof does not use {k}"
    Lean.logInfo m!"GATECERT AUDIT {fin}: type defeq to {old} (exact Expr equality: {exact}); standard axioms; no hand-written run lemma in the proof"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collMixSame_designClosedC
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collMixDiff_designClosedC
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collMixArgs_designClosedC
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest.collWidth_designClosedC

/-! ## The generic kid facts reproduce the per-parent ones (`example`s: no new declaration) -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)

-- (writing-time guess, accepted by build ce1/ce2: `type_of%` elaborates `<p>_kids hR0` with its implicit contexts taken
-- from `hR0`; the `rfl`s reduce `outsG`/`insG`/`outsFN`/`insFN` at a constructor; for
-- `collMixSame` the entry table `collMixSame_entry` (name first) is reshaped inline by `Or.imp`,
-- its implicit `cb aw dw c` assigned by unification before `hR0` is elaborated)

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    type_of% (collMixSame_kids hR0) :=
  Tools.ShippingGateCert.memGate_kids (bs := fakeSrc.gateBinders) (srt := fakeSrc.gateSort)
    (cb := false) (aw := 4) (dw := 8) (c := syncName)
    collMixSame.machineData outsG insG rfl rfl rfl rfl
    (fun k hk => (collMixSame_entry k hk).2.imp id
      (fun ho => ⟨ho, (collMixSame_entry k hk).1⟩)) hR0
    fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    type_of% (collMixSame_kidTyped hR0) :=
  Tools.ShippingGateCert.memGate_kidTyped (bs := fakeSrc.gateBinders) (srt := fakeSrc.gateSort)
    (cb := false) (aw := 4) (dw := 8) (c := syncName)
    collMixSame.machineData
    (fun k hk => (collMixSame_entry k hk).2.imp id
      (fun ho => ⟨ho, (collMixSame_entry k hk).1⟩)) hR0
    fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide))

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    type_of% (collMixDiff_kids hR0) :=
  Tools.ShippingGateCert.memGate_kids (bs := fakeSrc.gateBinders) (srt := fakeSrc.gateSort)
    (cb := true) (aw := 4) (dw := 8) (c := syncName)
    collMixDiff.machineData outsG insG rfl rfl rfl rfl collMixDiff_entry hR0
    fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    type_of% (collMixDiff_kidTyped hR0) :=
  Tools.ShippingGateCert.memGate_kidTyped (bs := fakeSrc.gateBinders) (srt := fakeSrc.gateSort)
    (cb := true) (aw := 4) (dw := 8) (c := syncName)
    collMixDiff.machineData collMixDiff_entry hR0
    fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide))

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    type_of% (collMixArgs_kids hR0) :=
  Tools.ShippingGateCert.memGate_kids (bs := fakeSrc.gateBinders) (srt := fakeSrc.gateSort)
    (cb := false) (aw := 4) (dw := 8) (c := syncName)
    collMixArgs.machineData outsG insG rfl rfl rfl rfl collMixArgs_entry hR0
    fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    type_of% (collMixArgs_kidTyped hR0) :=
  Tools.ShippingGateCert.memGate_kidTyped (bs := fakeSrc.gateBinders) (srt := fakeSrc.gateSort)
    (cb := false) (aw := 4) (dw := 8) (c := syncName)
    collMixArgs.machineData collMixArgs_entry hR0
    fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide))

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    type_of% (collWidth_kids hR0) :=
  Tools.ShippingGateCert.memGate_kids (bs := fakeN.gateBinders) (srt := fakeN.gateSort)
    (cb := true) (aw := 4) (dw := 8) (c := comboName)
    collWidth.machineData outsFN insFN rfl rfl rfl rfl collWidth_entry hR0
    fakeN.gate_old fakeN.gate_peel fakeN.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) fakeN_width

example {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    type_of% (collWidth_kidTyped hR0) :=
  Tools.ShippingGateCert.memGate_kidTyped (bs := fakeN.gateBinders) (srt := fakeN.gateSort)
    (cb := true) (aw := 4) (dw := 8) (c := comboName)
    collWidth.machineData collWidth_entry hR0
    fakeN.gate_old fakeN.gate_peel fakeN.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide))

end Sparkle.Tests.Compiler.MemNameCollisionGateCertGenTest
