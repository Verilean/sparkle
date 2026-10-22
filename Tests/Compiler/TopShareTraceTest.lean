import Tests.Compiler.TopShareRetInstTest
-- BUILT (unit SR10): r2/r3 exit 0 (dev runs); see REPORT-SR10.md for the final-SHA rebuild.
-- SCOPE: `topshare_traceXA`: the served-real TRACE (`MachineTraceLBX`) of `topshare` from ONE core run of `topshare` at depth 0, where the
-- parent's no-fallback premise is DERIVED (`topshare_closes0` = `machineSynth_ne_none4` at the real declarations).  This is the `soundL`
-- piece of the endpoint `machine_design_noShips_noBd_dc`; NOT the semantic endpoint (composed, houtTy and the four design checks are not
-- proved for the shared-leaf `topshare`).  `RealChildA` is a history of past synthesis results; `T` is an ADDED boundary.
namespace Tests.Compiler.TopShareTraceTest
open Tests.Compiler.TopShareInstTest Tests.Compiler.TopShareRetInstTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA
open Tools.ShippingMachineEntry Tools.ShippingTopShareRun Tools.ShippingEntrySoundness
open Tools.ShippingServedRealA Tools.ShippingChildDepthC Tools.ShippingChildTranslateA Tools.ShippingChildComposeC Tools.ShippingChildRunAMain
open Tests.Compiler.SeqDeepGenDiffTest
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit

local instance topshareInhabHL : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys topshare.machineData.ss)) :=
  inferInstanceAs (Inhabited (Sparkle.Core.HList [BitVec 8]))

/-- The parent's no-fallback premise at the entry's start world, DERIVED for `topshare` (the proof of `topshare_entry_run_inst'`, extracted). -/
theorem topshare_closes0 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape := by
  obtain ⟨o₁, o₁', o₂, o₂', h1, h1', h2, h2', hP⟩ := topshare_instTagged_shape
  intro tenv b w9 r w10 hj hcv hr
  exact machineSynth_ne_none4 O hA (by decide) h1 h1' h2 h2' topshare.machineData topshare.machine_ok
      topshare.machine_body topshare_halias topshare_hC topshare_hslots topshare_hdomB
      (by first | decide | decide +kernel) (by first | decide | decide +kernel) hP topshare_hlen4 topshare_hmk
      _ _ (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0) topshare_calleeOKs_ne
      nameK nkK outsK namesK
      (fun y hy k hk => by
        have := topdiff2.epD2M0_C_ifaceP O T entryW hR0 hy
        simpa [nameK, nkK, outsK, namesK, if_pos hk] using this)
      (fun y hy k hk2 hk4 => by
        have := wrap3_ifaceP O T hA entryW3 hR0 hy
        simpa [nameK, nkK, outsK, namesK, if_neg (Nat.not_lt.mpr hk2)] using this)
      topshare_hargsN topshare_hfieldOut topshare_hfieldsNd topshare_hsep topshare_hparent topshare_hfresh
      topshare_hparentD hj hcv hr

/-- `MachineRunJQC` of `topshare` at depth `1` from ONE core run at depth `0` (the machine run behind the trace). -/
theorem topshare_machineRun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (m, design) w') :
    MachineRunJQC O mctx cctx 1 ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape m design := by
  obtain ⟨tenv, b, w9, w10, hmach, hw9, -, -⟩ :=
    core_run_tracked0' O hA entryT (topshare_closes0 O T hA entryW entryW3 hR0) hw hcore
  exact ⟨tenv, b, w9, w10, hmach, hw9⟩

theorem topshare_traceXA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref wrapN Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref accN
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
      mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape m design)
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
        topshare.machineInits topshare.machineBody topshare.machineExt topshare.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA topshare.machineData
    (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineInits topshare.machineBody topshare.machineResult
    topshare.machineExt topshare.machineExtB topshare.machineSource topshare.machine_ok topshare.machine_body
    topshare.machine_inits topshare.machine_writes topshare.machine_result topshare.machine_source
    (fun i bools bits S S' t h =>
      topshare.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
        (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h))
    O (bodyStepC_of_tele O T) hA (n := 0 + 1) (htr_of_tele O hA T 0) (m := m) (design := design)
    (topshare_machineRun O T hA entryT entryW entryW3 hR0 hw hcore)

end Tests.Compiler.TopShareTraceTest

#print axioms Tests.Compiler.TopShareTraceTest.topshare_closes0
#print axioms Tests.Compiler.TopShareTraceTest.topshare_traceXA
