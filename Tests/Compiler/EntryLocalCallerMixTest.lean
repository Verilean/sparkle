-- BUILT (unit SR2f): t1 exit 0 (in-test audit + two conclusion comparisons THROW on failure).
import Tests.Compiler.EntryGateCallerMixTest
import Tools.ShippingMachineComposeRMLCommand

/-! # callerMix's chain with the RUN-LOCAL entry boundary (unit SR2f)

SR2d/SR2e's endpoint took `EntryDefines c c.gateValue` (resp. `EnvDefines`) for the two gate children: a property of
EVERY pair of `getConstInfo` / `getEnv` runs from every world.  The consumers use it only at the reads of one
successful core run of the child (the run a `RealChildA` / `GateRun` supplies).  Here the endpoint is re-derived with
`EntryDefinesRuns mref cref c c.gateValue` (every successful core run of `c`, in any contexts, reads an entry constant
that is a definition of value `c.gateValue`), and then with `EnvDefinesRun` (the constant the run itself reads).
PREMISES stay: this is a weaker premise, NOT a discharged one. -/
namespace Tests.Compiler.EntryLocalCallerMixTest
open Lean Elab Meta Term
open Sparkle.Compiler.Elab Sparkle.Tests.Compiler.ShippingMachineInstTest
open Sparkle.Tests.Compiler.ShippingPremiseEvalTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingEntryDefinesRun

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
  withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
  let n ← Tools.ShippingMachineComposeRMLCommand.generateComposedRML ``callerMix
  logInfo m!"{n}: {(← getConstInfo n).type}"

section kids
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : RefLawsAOps MkRefd mref cref)

theorem pick_fullAL (hR : EntryDefinesRuns mref cref ``pick pick.gateValue)
    {y : Tools.ShippingChildInv.Res} (hy : RealChildA O ``pick y) :
    Tools.ShippingGateChildComb.ChildFull ``pick pick.gateBinders y.1 y.2 :=
  childFull_of_realAL O hR pick.gate_old pick.gate_peel pick.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy

theorem pickD_fullAL (hR : EntryDefinesRuns mref cref ``pickD pickD.gateValue)
    {y : Tools.ShippingChildInv.Res} (hy : RealChildA O ``pickD y) :
    Tools.ShippingGateChildComb.ChildFull ``pickD pickD.gateBinders y.1 y.2 :=
  childFull_of_realAL O hR pickD.gate_old pickD.gate_peel pickD.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy
end kids

set_option maxHeartbeats 0 in
theorem callerMix_closesAL {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : EntryDefinesRuns mref cref ``pick pick.gateValue)
    (hR1 : EntryDefinesRuns mref cref ``pickD pickD.gateValue) :
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
      | zero => exact Tools.ShippingCallsGate.ChildFull.iface (pick_fullAL O hR0 hy)
      | succ k =>
        cases k with
        | zero => exact Tools.ShippingCallsGate.ChildFull.iface (pickD_fullAL O hR1 hy)
        | succ k => exact absurd hk' (by omega))
    (by decide)
    (Tools.ShippingNameDischarge.names_inj _) (by decide)
    (Tools.ShippingNameDischarge.parent_ne _ ``callerMix (by decide))
    (fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by decide : ∀ o ∈ callerMix.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) k _)

noncomputable local instance : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys callerMix.machineData.ss)) :=
  ⟨callerMix.machineInits⟩

set_option maxHeartbeats 0 in
/-- callerMix's ONE chain with the two all-world `EntryDefines` replaced by the run-local `EntryDefinesRuns`. -/
theorem callerMix_entryComposedL
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false) mctx mref cctx cref w (m, design) w')
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix callerMix.machineData.shape)
    (hw : JQ O.quiet 0 w)
    (hR0 : EntryDefinesRuns mref cref ``pick pick.gateValue)
    (hR1 : EntryDefinesRuns mref cref ``pickD pickD.gateValue) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) ``callerMix callerMix.machineData 1 m design
      (fun _ => Sparkle.Core.Domain.defaultDomain) callerMix.machineSource
      (fun i bools bits => callerMix.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop callerMix.machineInits (callerMix.machineBody i bools bits))) :=
  callerMix.machine_composedRML O hA T hr entry (callerMix_closesAL O T hA hR0 hR1) hw hR0 hR1

open Tests.Compiler.EntryGateCallerMixTest (pick_gate pickD_gate) in
/-- The same with the ENVIRONMENT half only: the constant each successful core run of `pick` / `pickD` reads is a
definition of value `gateValue` (the gate half is decided: `pick_gate`, `pickD_gate`). -/
theorem callerMix_entryComposedL_env
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false) mctx mref cctx cref w (m, design) w')
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix callerMix.machineData.shape)
    (hw : JQ O.quiet 0 w)
    (hE0 : ∀ mctx cctx, EnvDefinesRun mctx mref cctx cref ``pick pick.gateValue)
    (hE1 : ∀ mctx cctx, EnvDefinesRun mctx mref cctx cref ``pickD pickD.gateValue) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) ``callerMix callerMix.machineData 1 m design
      (fun _ => Sparkle.Core.Domain.defaultDomain) callerMix.machineSource
      (fun i bools bits => callerMix.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop callerMix.machineInits (callerMix.machineBody i bools bits))) :=
  callerMix_entryComposedL O hA T hr entry hw (EntryDefinesRuns.of_envRuns hE0 pick_gate)
    (EntryDefinesRuns.of_envRuns hE1 pickD_gate)

open Tests.Compiler.ChildVertAuditTest in
def auditL (n : Name) (want : List (Option Name)) : TermElabM Unit := do
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
  logInfo m!"SR2f AUDIT OK: {n}: standard axioms; premise heads {want}; no all-world EntryDefines/EnvDefines in the closure ({cl.size} constants)"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  auditL ``callerMix_entryComposedL [some ``Tools.ShippingChildInvA.RefLawsAOps,
    some ``Tools.ShippingChildInvA.AdmCtx, some ``Tools.ShippingChildInvA.RefLawsATele,
    some ``Tools.ShippingEntrySoundness.RunsTo, some ``Tools.ShippingMachineEntry.MachineDefines,
    some ``Tools.ShippingChildVCA.JQ, some ``Tools.ShippingEntryDefinesRun.EntryDefinesRuns,
    some ``Tools.ShippingEntryDefinesRun.EntryDefinesRuns]
  Tests.Compiler.ComposedCallerMixATest.sameConclusionRN ``callerMix.machine_composedRM ``callerMix_entryComposedL
  Tests.Compiler.ComposedCallerMixATest.sameConclusionRN ``callerMix.machine_composedR ``callerMix_entryComposedL

#print axioms callerMix_entryComposedL
#print axioms callerMix_entryComposedL_env
end Tests.Compiler.EntryLocalCallerMixTest
