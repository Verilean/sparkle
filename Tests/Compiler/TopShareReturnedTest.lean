import Tests.Compiler.TopShareComposedTest
import Tools.ShippingTopShareNoParent
-- BUILT (unit SR12): n5 exit 0 (Tests.Compiler.TopShareReturnedTest, with the in-file statement and closure audits); see REPORT-SR12.md for the final-SHA rebuild.
-- SCOPE (binding, ledger L8ar): the semantic conclusion of the `topshare` endpoint (SR11 `topshare_wired`) transported to the RETURNED design `y.2`.
-- DERIVED (not assumed): no module of the core run's design `Dg` is named like the entry (`M.name`), from the real run's cache facts
-- (`Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np`: CacheClosed + KeyTop + the key growth of the child runs + `ofDecl` injectivity + the harness design
-- has no module), so the entry's clean-up `topMap` is the identity on `Dg` (`topMap_id`) and `y.2 = Dg`.  The data facts that instance supplies (parent `callsOk` / slots /
-- binders, `topshare ≠ wrap, wrap3`, the callees' calls are all `acc`) are decided on the real machine data.  The SAME `w`, `w'`, `y`, `M`, `Dg` as the ret theorem and
-- `topshare_wired` (this theorem does not use `topshare_entry_run_inst_ret`; it uses its `_np` variant with the same proof text and one more conjunct).
-- WHAT THE CONCLUSION IS (exact): `DesignSemConcl 2 topshare … y.1 M y.2`: `checkedOptimize` of the RETURNED module `y.1` (the clean-up of the raw `M`; `M` enters only
-- `ResetNk`) judged with the children (`childMap …modules`) of the RETURNED design `y.2`, which equals the core run's `Dg`; inputs / reset / bounds remain inside `DesignSemConcl`.
-- It does not say anything about modules of other designs, nor that `RealChildA`/`JQC` histories are fresh/semantically correct in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`.  `topshare` stays REFUSED by the generator.
open Tests.Compiler.SeqDeepGenDiffTest Tests.Compiler.SeqDeepGenInstTest
section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingSeqParentLemmas
set_option Elab.async false
set_option linter.unusedSimpArgs false

open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA Tools.ShippingChildDepthC
open Tools.ShippingChildTranslateA Tools.ShippingParentRanA Tools.ShippingChildComposeC Tools.ShippingChildRunAMain
open Tools.ShippingParentSeqComposedA
open Tools.ShippingChildInv Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingTopShareRun
set_option maxHeartbeats 4000000

open Tests.Compiler.TopShareInstTest in
/-- **The semantic conclusion for the RETURNED design `y.2` (unit SR12, L8ar).**  Same premises as `topshare_wired`; the SAME `M`, `Dg` carry the ret conjuncts, the RAW
`ComposedG`, the fact that NO module of `Dg` is named `M.name`, `y.2 = Dg`, and the endpoint's conclusion `DesignSemConcl … y.1 M y.2` (children of the returned `y.2`). -/
theorem Tests.Compiler.TopShareReturnedTest.topshare_returned
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂]
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenInstTest.wrap = some y₁ ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
        mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) ∧ y.2 = Dg ∧
      ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``Tests.Compiler.SeqDeepGenDiffTest.topshare
        topshare.machineData 3 M Dg (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits))) ∧
      Tools.ShippingSeqParentAt.DesignSemConcl 2 ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData 3
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        y.1 M y.2 := by
  obtain ⟨o₁, o₁', o₂, o₂', h1, h1', h2, h2', hP⟩ := topshare_instTagged_shape
  have closes0 : MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape :=
    Tests.Compiler.TopShareTraceTest.topshare_closes0 O T hA entryW entryW3 hR0
  obtain ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl, hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost, hno⟩ :=
    Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np O hA (by decide) h1 h1' h2 h2' topshare.machineData
      topshare.machine_ok topshare.machine_body (by first | decide | decide +kernel) (by first | decide | decide +kernel)
      topshare_hC topshare_hslots topshare_hdomB hP entryT closes0 _ _
      (wrap_calleeOK O T hA entryW hR0) (wrap3_calleeOK O T hA entryW3 hR0) topshare_calleeOKs_ne
      (by decide) (by decide)
      (fun k hk => by rw [wrap_insts_acc k hk]; decide)
      (fun k hk => by rw [wrap3_insts_acc k hk]; decide) hw h
  have hpostb : y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    hpost.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hy2 : y.2 = Dg := Tools.ShippingTopShareNoParent.returned_design_eq hno
    (hpost.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl, hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost, hno, hy2,
    Tests.Compiler.TopShareComposedTest.ts_composedA O T hA entryW hR0 entryW3 hR0 hw hcore entryT, ?_⟩
  rw [hy2]
  exact Tools.ShippingSeqParentAt.machine_design_noShips_noBd_dc_at 2
    Tests.Compiler.TopShareComposedTest.ts_Bnd (fun _ _ _ _ => True)
    topshare.machineData
    (kD := 3) (ι := Unit) (dom := fun _ => Sparkle.Core.Domain.defaultDomain)
    (fun hcore entry _ hB => by
      obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
      exact Tests.Compiler.TopShareComposedTest.ts_soundLA O T hA hM0 hR0 hM1 hR1 hw hcore entry)
    (fun hcore entry _ hB _ => by
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
    hcore hpostb entryT trivial ⟨O, T, hA, entryW, hR0, entryW3, hR0, hw⟩

#print axioms Tests.Compiler.TopShareReturnedTest.topshare_returned

def Tests.Compiler.TopShareReturnedTest.TopShareReturnedFull (v : Nat) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare
      topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O (if v = 16 then 1 else 0) w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare)
      mctx mref cctx cref w y w'),
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Sparkle.IR.Machine.closeLets topshare.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare.machineData.shape)
        topshare.machineData.shape.insts.length topshare.machineData.shape.layout.slots.length
        (t.inputs.map (·.name)) (topshare.machineData.shape.insts.map (·.2.1))
        topshare.machineData.shape.instFields [y₁, y₁, y₂, y₂]
        (Sparkle.IR.Machine.closeMachine topshare.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenInstTest.wrap = some y₁ ∧
      (cv w10).get? ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts.length)
        k₂ (hk₂ : k₂ < wrap3.machineData.shape.insts.length),
        (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 =
          (wrap3.machineData.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape.insts[k₁]).1 = some e ∧
          e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Tests.Compiler.SeqDeepGenDiffTest.topshare [] false)
        mctx mref cctx cref (if v = 10 then w' else w) (M, Dg) wc ∧ cv wc = cv w10 ∧
      (let A := (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg)
       let B := (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (Tools.ShippingSharedLeafNL.topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))
       if v = 15 then A else (A ∨ B)) ∧
      (∀ x ∈ (if v = 6 then y₁.2 else Dg).modules, if v = 17 then True else x.name ≠ (if v = 7 then t' else M).name) ∧
      y.2 = (if v = 5 then y₁.2 else Dg) ∧
      ComposedG (fun D => KSn (childMap D.modules) (if v = 18 then 1 else 2)) (ResetNk (if v = 18 then 1 else 2)) ``Tests.Compiler.SeqDeepGenDiffTest.topshare
        topshare.machineData 3 (if v = 13 then t' else M) (if v = 14 then y₁.2 else Dg) (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits))) ∧
      Tools.ShippingSeqParentAt.DesignSemConcl (if v = 8 then 1 else 2) (if v = 12 then ``Tests.Compiler.SeqDeepGenInstTest.wrap else ``Tests.Compiler.SeqDeepGenDiffTest.topshare) (if v = 11 then Tests.Compiler.SeqDeepGenInstTest.wrap.machineData else topshare.machineData) (if v = 9 then 2 else 3)
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineSource
        (fun i bools bits => topshare.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (fun i bools bits => topshare.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
        (if v = 3 then M else y.1) (if v = 4 then y.1 else M) (if v = 1 then Dg else if v = 2 then y₁.2 else y.2)

end

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let thm := ``Tests.Compiler.TopShareReturnedTest.topshare_returned
  let ty := (← getConstInfo thm).type
  forallTelescope ty fun xs _ => do
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "O", "T", "hA", "entryT", "entryW", "entryW3", "hR0", "w", "w'", "y", "hw", "h"] do
      throwError "SR12 AUDIT FAILED: premises of {thm} are {names}"
  if ty.hasMVar then throwError "SR12 AUDIT FAILED: metavariables in the statement"
  Meta.check ty
  let full (v : Nat) : MetaM Lean.Expr := do
    let some b ← unfoldDefinition? (mkApp (mkConst ``Tests.Compiler.TopShareReturnedTest.TopShareReturnedFull) (mkNatLit v))
      | throwError "SR12 AUDIT FAILED: cannot unfold TopShareReturnedFull"
    evalIteSR11 (← instantiateMVars b)
  unless ← withReducible (isDefEq ty (← full 0)) do throwError "SR12 AUDIT FAILED: the statement of {thm} differs from the hand-written expected statement"
  let mut rejected : List Nat := []
  for v in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] do
    if ← withReducible (isDefEq ty (← full v)) then throwError "SR12 AUDIT FAILED: the mutation {v} of the expected statement was ACCEPTED"
    rejected := v :: rejected
  let concl ← forallTelescope ty fun xs b => pure (b.containsFVar xs[13]!.fvarId!)
  unless concl do throwError "SR12 AUDIT FAILED: the conclusion does not mention y"
  logInfo m!"SR12 STATEMENT AUDIT: {thm} equals the hand-written TopShareReturnedFull 0 (isDefEq under reducible transparency after evaluating the switches, no mvars, Meta.check); the conclusion mentions y; mutations rejected: {rejected.reverse}"

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR12 AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let oldGen : List Name := [`Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2, `Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_design_svNR2,
    `Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_composedNR1, `Tests.Compiler.SeqDeepGenDiffTest.wrap3.seq_child_runN_ofR1,
    `Tests.Compiler.SeqDeepGenInstTest.wrap.machine_composedNR1, `Tests.Compiler.SeqDeepGenInstTest.wrap.seq_child_runN_ofR1]
  for f in oldGen do
    unless (← getEnv).contains f do throwError "SR12 AUDIT FAILED: the old generated name {f} does not exist (the audit would check nothing)"
  let new := ``Tests.Compiler.TopShareReturnedTest.topshare_returned
  stdAxioms new
  let cl ← depClosure new
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR12 AUDIT FAILED: {new}: old boundary / old child predicate in closure: {bad}"
  for old in oldGen do
    if cl.contains old then throwError "SR12 AUDIT FAILED: the old generated theorem {old} is in the closure of {new}"
  for must in [``Tests.Compiler.TopShareComposedTest.ts_composedA, ``Tests.Compiler.TopShareComposedTest.ts_soundLA,
      ``Tests.Compiler.TopShareComposedTest.ts_runFacts, ``Tests.Compiler.TopShareComposedTest.ts_outsCheck,
      ``Tests.Compiler.TopShareComposedTest.ts_kidsMasked, ``Tests.Compiler.TopShareComposedTest.ts_designCheck,
      ``Tests.Compiler.TopShareTraceTest.topshare_closes0, ``Tools.ShippingTopShareRan.machineRanA_start0,
      ``Tools.ShippingSeqParentAt.machine_design_noShips_noBd_dc_at,
      -- the derivation of `y.2 = Dg`
      ``Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np, ``Tools.ShippingTopShareNoParent.topshare_closing4_keys,
      ``Tools.ShippingTopShareNoParent.topshare_quad_keys, ``Tools.ShippingTopShareNoParent.noParent_of_cache,
      ``Tools.ShippingTopShareNoParent.closeInstsG_name_design, ``Tools.ShippingTopShareNoParent.returned_design_eq,
      ``Tools.ShippingSharedLeafNL.topMap_id, ``Tools.ShippingModuleName.ofDecl_injective,
      ``Tools.ShippingClosedKinds.closedBody_kinds_of_run, ``Tools.ShippingSharedLeafExt.mem_designWith] do
    unless cl.contains must do throwError "SR12 AUDIT FAILED: {must} not in the closure of {new}"
  -- the lookup-agreement-only route (SR11) is NOT what this theorem uses
  if cl.contains ``Tools.ShippingSeqParentAt.moduleByName_post_other then throwError "SR12 AUDIT FAILED: moduleByName_post_other in the closure"
  logInfo m!"SR12 CLOSURE AUDIT: {new}: standard axioms; closure {cl.size} constants; none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC, no RefLaws/RefLawsCore/toAOps/toA; the old generated composed theorems are not in it; the no-parent derivation (closing keys, noParent_of_cache, topMap_id, ofDecl_injective, closedBody_kinds_of_run) is"
