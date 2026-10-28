-- BUILT (unit SR2d, par/u-sr2d): rm4 exit 0 (in-test audit + two conclusion comparisons THROW on failure); co-import co1 exit 0.
import Tests.Compiler.ComposedCallerMixATest
import Tests.Compiler.ParentDesignCheckATest
import Tools.ShippingMachineComposeRMCommand

namespace Tests.Compiler.ComposedCallerMixEntryTest
open Lean Elab Meta Term
open Sparkle.Tests.Compiler.ShippingPremiseEvalTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
  withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
  let n ← Tools.ShippingMachineComposeRMCommand.generateComposedRM ``callerMix
  logInfo m!"{n}: {(← getConstInfo n).type}"

open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingInlineSoundness (EntryDefines)
open Sparkle.Tests.Compiler.ShippingMachineInstTest

/-- the state's `Inhabited` instance, as the generator builds it (`Inhabited.mk` of the initial values) -/
noncomputable local instance : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys callerMix.machineData.ss)) :=
  ⟨callerMix.machineInits⟩

set_option maxHeartbeats 0 in
/-- ONE chain for `callerMix`: the real core run (start world `JQ O.quiet 0`), `MachineDefines`, the closing
`callerMix_closesA` (from the two `EntryDefines`) → the trace (`machine_trace_lets_of_streamBRA_main`) →
`machine_linked_callsRA` (with `hfn`/`hcalls` proved) → `ComposedH`. -/
theorem callerMix_entryComposed
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerMix [] false) mctx mref cctx cref w (m, design) w')
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerMix callerMix.machineData.shape)
    (hw : JQ O.quiet 0 w)
    (hR0 : EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    (hR1 : EntryDefines mctx mref cctx cref ``pickD pickD.gateValue) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) ``callerMix callerMix.machineData 1 m design
      (fun _ => Sparkle.Core.Domain.defaultDomain) callerMix.machineSource
      (fun i bools bits => callerMix.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop callerMix.machineInits (callerMix.machineBody i bools bits))) :=
  callerMix.machine_composedRM O hA T hr entry
    (Tests.Compiler.ParentDesignCheckATest.callerMix_closesA O T hA hR0 hR1) hw hR0 hR1

open Tests.Compiler.ChildVertAuditTest in
/-- AUDIT (THROWS): standard axioms; exactly one `O : RefLawsAOps MkRefd`, one `T : RefLawsATele` (data/assumption
family, recorded); the Prop premises are exactly AdmCtx, RunsTo, MachineDefines, JQ, EntryDefines ×2 — NO trace
(`MachineTraceLBX`), NO `MachineClosesAtA`, NO `hfn`/`hcalls`/`ChildBnd`; the closure contains the trace lemma,
`callerMix_closesA`, `machine_linked_callsRA`, and none of the old boundary. -/
def auditEntry (n : Name) : TermElabM Unit := do
  stdAxioms n
  let ty := (← getConstInfo n).type
  let heads : Array (Option Name) ← forallTelescope ty fun xs _ => do
    let mut ps : Array (Option Name) := #[]
    for x in xs do
      let t ← inferType x
      ps := ps.push t.getAppFn.constName?
    return ps
  let want : List (Option Name) := [some ``Tools.ShippingChildInvA.RefLawsAOps,
    some ``Tools.ShippingChildInvA.AdmCtx, some ``Tools.ShippingChildInvA.RefLawsATele,
    some ``Tools.ShippingEntrySoundness.RunsTo, some ``Tools.ShippingMachineEntry.MachineDefines,
    some ``Tools.ShippingChildVCA.JQ, some ``Tools.ShippingInlineSoundness.EntryDefines,
    some ``Tools.ShippingInlineSoundness.EntryDefines]
  unless heads.toList.drop 8 == want do throwError "{n}: binders {heads}"
  let cl ← depClosure n
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingChildInv.InvW,
     `Tools.ShippingMachineComposeR.machine_linked_callsR].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{n}: old boundary in closure: {bad}"
  for need in [``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_main,
      ``Tests.Compiler.ParentDesignCheckATest.callerMix_closesA,
      ``Tools.ShippingMachineComposeRA.machine_linked_callsRA,
      ``Tools.ShippingMachineComposeRM.machine_traceL_of_data_extRM] do
    unless cl.contains need do throwError "{n}: closure lacks {need}"
  let (axs, ops, exts, impls) ← boundary cl
  logInfo m!"ENTRY AUDIT OK: {n}: standard axioms; premises = O, hA, T, core run, MachineDefines, JQ O.quiet 0 w, EntryDefines pick, EntryDefines pickD (no trace premise, no closes premise, no hfn/hcalls); closure {cl.size} constants, none of RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV/InvW/machine_linked_callsR; boundary (structural): {axs.length} axioms, {ops.length} opaque, {exts.length} extern, {impls.length} implemented_by"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  auditEntry ``callerMix_entryComposed
  Tests.Compiler.ComposedCallerMixATest.sameConclusionRN ``callerMix.machine_composedR ``callerMix_entryComposed
  Tests.Compiler.ComposedCallerMixATest.sameConclusionRN ``callerMix.machine_composedRN ``callerMix_entryComposed

#print axioms callerMix_entryComposed

end Tests.Compiler.ComposedCallerMixEntryTest
