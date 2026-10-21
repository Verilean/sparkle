-- BUILT (unit SR2g): t1 exit 0 (in-test audit + two conclusion comparisons THROW on failure).
import Tests.Compiler.EntryGateCallerMixTest
import Tools.ShippingMachineComposeRMGCommand

/-! # callerMix's chain with the CHAIN-LINKED entry boundary (unit SR2g)

SR2f's `EntryDefinesRuns` still quantified over `getConstInfo` / `getEnv` / body at unconnected worlds keyed on the
output `(M, D)`.  `EntryDefinesRunsG` (Tools.ShippingEntryReadsLinked) asks the entry constant to be a definition of
value `c.gateValue` only at the chain `w —head→ w1 —getConstInfo→ w2 —getEnv→ w3 —body→ w4 —finally→ w'` of ONE core
run.  Implied by the all-world `EntryDefines` (`EntryDefinesRunsG.of_entry`); implication from SR2f's
`EntryDefinesRuns` NOT proved here.  PREMISES stay: nothing discharged; the env snapshot (`EnvSnapshot`) is OPEN. -/
namespace Tests.Compiler.EntryLinkedCallerMixTest
open Lean Elab Meta Term
open Sparkle.Compiler.Elab Sparkle.Tests.Compiler.ShippingMachineInstTest
open Sparkle.Tests.Compiler.ShippingPremiseEvalTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingEntryReadsLinked

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
  withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
  let n ← Tools.ShippingMachineComposeRMGCommand.generateComposedRMG ``callerMix
  logInfo m!"{n}: {(← getConstInfo n).type}"

section kids
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : RefLawsAOps MkRefd mref cref)

theorem pick_fullAG (hR : EntryDefinesRunsG mref cref ``pick pick.gateValue)
    {y : Tools.ShippingChildInv.Res} (hy : RealChildA O ``pick y) :
    Tools.ShippingGateChildComb.ChildFull ``pick pick.gateBinders y.1 y.2 :=
  childFull_of_realAG O hR pick.gate_old pick.gate_peel pick.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy

theorem pickD_fullAG (hR : EntryDefinesRunsG mref cref ``pickD pickD.gateValue)
    {y : Tools.ShippingChildInv.Res} (hy : RealChildA O ``pickD y) :
    Tools.ShippingGateChildComb.ChildFull ``pickD pickD.gateBinders y.1 y.2 :=
  childFull_of_realAG O hR pickD.gate_old pickD.gate_peel pickD.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy
end kids

set_option maxHeartbeats 0 in
theorem callerMix_closesAG {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : EntryDefinesRunsG mref cref ``pick pick.gateValue)
    (hR1 : EntryDefinesRunsG mref cref ``pickD pickD.gateValue) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``callerMix
      callerMix.machineData.shape :=
  Tools.ShippingCallsGateA.machineClosesAtA_of_gateKids (nDecl := 1) O T hA callerMix.machineData
    callerMix.machine_ok callerMix.machine_body (by decide) (by decide)
    (fun k => List.getD [((pick.gateBinders.filter fun x => x.2 != .domain).length),
      ((pickD.gateBinders.filter fun x => x.2 != .domain).length)] k 0)
    (by decide)
    (by
      intro k hk y hy
      have hk' : k < 2 := hk
      cases k with
      | zero => exact Tools.ShippingCallsGate.ChildFull.iface (pick_fullAG O hR0 hy)
      | succ k =>
        cases k with
        | zero => exact Tools.ShippingCallsGate.ChildFull.iface (pickD_fullAG O hR1 hy)
        | succ k => exact absurd hk' (by omega))
    (by decide)
    (Tools.ShippingNameDischarge.names_inj _) (by decide)
    (Tools.ShippingNameDischarge.parent_ne _ ``callerMix (by decide))
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by decide : ∀ o ∈ callerMix.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) k _)

noncomputable local instance : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys callerMix.machineData.ss)) :=
  ⟨callerMix.machineInits⟩

set_option maxHeartbeats 0 in
/-- callerMix's ONE chain with the two all-world `EntryDefines` replaced by the run-local `EntryDefinesRunsG`. -/
theorem callerMix_entryComposedG
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false) mctx mref cctx cref w (m, design) w')
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix callerMix.machineData.shape)
    (hw : JQ O.quiet 0 w)
    (hR0 : EntryDefinesRunsG mref cref ``pick pick.gateValue)
    (hR1 : EntryDefinesRunsG mref cref ``pickD pickD.gateValue) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) ``callerMix callerMix.machineData 1 m design
      (fun _ => Sparkle.Core.Domain.defaultDomain) callerMix.machineSource
      (fun i bools bits => callerMix.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop callerMix.machineInits (callerMix.machineBody i bools bits))) :=
  callerMix.machine_composedRMG O hA T hr entry (callerMix_closesAG O T hA hR0 hR1) hw hR0 hR1

open Tests.Compiler.ChildVertAuditTest in
def auditG (n : Name) (want : List (Option Name)) : TermElabM Unit := do
  stdAxioms n
  let ty := (← getConstInfo n).type
  let heads : Array (Option Name) ← forallTelescope ty fun xs _ => do
    let mut ps : Array (Option Name) := #[]
    for x in xs do ps := ps.push (← inferType x).getAppFn.constName?
    return ps
  unless heads.toList.drop 8 == want do throwError "{n}: binders {heads}"
  let cl ← depClosure n
  let env ← getEnv
  let bad := cl.toList.filter fun c => match env.find? c with
    | some ci => ci.type.getUsedConstants.contains ``Tools.ShippingInlineSoundness.EntryDefines ||
        ci.type.getUsedConstants.contains ``Tools.ShippingEntrySoundness.EnvDefines
    | none => false
  unless bad.isEmpty do throwError "{n}: all-world EntryDefines/EnvDefines still in the closure: {bad}"
  let bad2 := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingChildInv.InvW,
     `Tools.ShippingMachineComposeR.machine_linked_callsR].any (·.isPrefixOf c)
  unless bad2.isEmpty do throwError "{n}: old boundary in closure: {bad2}"
  for need in [``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_main,
      ``Tools.ShippingMachineComposeRA.machine_linked_callsRA,
      ``Tools.ShippingMachineComposeRM.machine_traceL_of_data_extRM] do
    unless cl.contains need do throwError "{n}: closure lacks {need}"
  logInfo m!"SR2g AUDIT OK: {n}: standard axioms; premise heads {want}; no all-world EntryDefines/EnvDefines in the closure ({cl.size} constants)"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  auditG ``callerMix_entryComposedG [some ``Tools.ShippingChildInvA.RefLawsAOps,
    some ``Tools.ShippingChildInvA.AdmCtx, some ``Tools.ShippingChildInvA.RefLawsATele,
    some ``Tools.ShippingEntrySoundness.RunsTo, some ``Tools.ShippingMachineEntry.MachineDefines,
    some ``Tools.ShippingChildVCA.JQ, some ``Tools.ShippingEntryReadsLinked.EntryDefinesRunsG,
    some ``Tools.ShippingEntryReadsLinked.EntryDefinesRunsG]
  Tests.Compiler.ComposedCallerMixATest.sameConclusionRN ``callerMix.machine_composedRM ``callerMix_entryComposedG
  Tests.Compiler.ComposedCallerMixATest.sameConclusionRN ``callerMix.machine_composedR ``callerMix_entryComposedG

#print axioms callerMix_entryComposedG
end Tests.Compiler.EntryLinkedCallerMixTest
