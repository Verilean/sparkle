import Tests.Compiler.TopShareReturnedTest
import Tests.Compiler.QuadLeafGenericTest
import Tools.ShippingQuadReturned
-- BUILT (unit SR14): r4 exit 0 (dev run, both statement audits pass); the final-SHA rebuild is in REPORT-SR14.md.
-- SCOPE (binding, ledger L8at): the `topshare` instances of the GENERIC `Tools.ShippingQuadReturned.quad_returned` / `quad_wired`.  For the real declarations
-- (`topshare`; callees `wrap`, `wrap3`; shared leaf `acc`) the new theorems `topshare_returned'` / `topshare_wired'` are `generic theorem + decided data facts
-- (QuadLeafGenericTest) + the per-callee blocks of TopShareComposedTest (`ts_soundLA`, `ts_composedA`, `ts_houtTy`, `ts_runFacts`, `ts_outsCheck`,
-- `ts_kidsMasked`, `ts_designCheck`)`; the statement of each is INFERRED from the generic theorem and checked by `isDefEq` (same binders) against the OLD
-- hand-written `Tests.Compiler.TopShareReturnedTest.topshare_returned` / `Tests.Compiler.TopShareComposedTest.topshare_wired` (old theorems untouched).
-- PREMISES stay premises (named): `O`, `T`, `hA`, `MachineDefines` (parent, callees, leaf), `JQC O 0 w`, the run `h`; the `ts_*` blocks are instance lemmas
-- (their generic derivation is OPEN).  `RealChildA` / `JQC` are histories, not freshness or semantic correctness in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`.
open Tests.Compiler.SeqDeepGenDiffTest Tests.Compiler.SeqDeepGenInstTest
section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingTopShareRun
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned Tests.Compiler.QuadLeafGenericTest
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Tests.Compiler.QuadReturnedTest

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare) mctx mref cctx cref w y w') =>
    @Tools.ShippingQuadReturned.quad_returned _ _ _ _ topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData wrap3.machineData
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc 3 3 3 2 3 Unit (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineInits
        topshare.machineBody topshare.machineExt topshare.machineExtB)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_soundLA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_composedA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
      Tests.Compiler.TopShareComposedTest.ts_houtTy
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_runFacts O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      (fun hcore hpost entry _ hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_outsCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_kidsMasked O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_designCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryT entryW entryW3 hR0
      (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) w w' y hw h)
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the instance term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.QuadReturnedTest.topshare_returned', levelParams := [], type := ty, value := e }
  -- statement audit: the instance's statement is `isDefEq` (same binders) to the OLD hand-written theorem
  let tb := (← getConstInfo ``Tests.Compiler.TopShareReturnedTest.topshare_returned).type
  forallTelescope ty fun xs ca => do
    let cb ← instantiateForall tb xs
    unless (← isDefEq ca cb) do throwError "SR14 statement audit: Tests.Compiler.QuadReturnedTest.topshare_returned' differs from Tests.Compiler.TopShareReturnedTest.topshare_returned"
    logInfo m!"SR14: statement of Tests.Compiler.QuadReturnedTest.topshare_returned' ≡ statement of Tests.Compiler.TopShareReturnedTest.topshare_returned ({xs.size} binders)"
#print axioms Tests.Compiler.QuadReturnedTest.topshare_returned'

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare) mctx mref cctx cref w y w') =>
    @Tools.ShippingQuadReturned.quad_wired _ _ _ _ topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData wrap3.machineData
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc 3 3 3 2 3 Unit (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineInits
        topshare.machineBody topshare.machineExt topshare.machineExtB)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_soundLA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_composedA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
      Tests.Compiler.TopShareComposedTest.ts_houtTy
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_runFacts O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      (fun hcore hpost entry _ hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_outsCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_kidsMasked O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact Tests.Compiler.TopShareComposedTest.ts_designCheck O T 1 hA hM0 hR0 hM1 hR1 hcore hpost entry hw)
      O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryT entryW entryW3 hR0
      (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) w w' y hw h)
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the instance term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.QuadReturnedTest.topshare_wired', levelParams := [], type := ty, value := e }
  -- statement audit: the instance's statement is `isDefEq` (same binders) to the OLD hand-written theorem
  let tb := (← getConstInfo ``Tests.Compiler.TopShareComposedTest.topshare_wired).type
  forallTelescope ty fun xs ca => do
    let cb ← instantiateForall tb xs
    unless (← isDefEq ca cb) do throwError "SR14 statement audit: Tests.Compiler.QuadReturnedTest.topshare_wired' differs from Tests.Compiler.TopShareComposedTest.topshare_wired"
    logInfo m!"SR14: statement of Tests.Compiler.QuadReturnedTest.topshare_wired' ≡ statement of Tests.Compiler.TopShareComposedTest.topshare_wired ({xs.size} binders)"
#print axioms Tests.Compiler.QuadReturnedTest.topshare_wired'

end Tests.Compiler.QuadReturnedTest
end
