import Tools.ShippingKaryComposed
-- BUILT (unit SR22): r1 exit 0 (dev run; 823 jobs); the final-SHA rebuild is in REPORT-SR22.md.
-- SCOPE (binding, ledger L8bb): the RETURNED-design theorem (`y.2 = Dg`) and the one-witness WIRED theorem of the K-callee shared-leaf class, over the callee list `cs : List KCal`
-- (K-ary generalisation of `Tools.ShippingQuadReturned.quad_returned` / `quad_wired`; K = 2 audit in `Tests/Compiler/KaryReturnedAuditTest.lean`).  PROVED here: the parent's run with the
-- returned value linked and NO module of `Dg` named like the entry (`kary_entry_run`), hence `y.2 = Dg` (`returned_design_eq`), and the transport of the endpoint's conclusion to the returned
-- design: the SAME `M`, `Dg` carry the run conjuncts, `ComposedG`, `DesignSemConcl … y.1 M y.2`.
-- PREMISES (named, one per block, as in `quad_returned`): `soundL` (the machine trace of the parent), `composed`, `houtTy`, `hFacts` (RunFacts), `hOuts` (outsCheck), `hBdRun` (kidsMasked),
-- `hdc` (designCheck), quantified over the class boundary `KaryBnd cs G dG`; an instance supplies them (for the endpoint: `kary_soundLA`, `kary_composed_split`, `kary_runFacts`, …).  Also premises:
-- `O`, `T`, `hA`, `MachineDefines` of parent / callees / leaf, `MachineCloses` of the leaf, `JQC O 0 w`, the decidable data facts.  `RealChildA` / `ServedRealA` / `JQC` are histories of past
-- synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field; no existing statement changed.
namespace Tools.ShippingKaryReturned
open Tools.ShippingKaryRun Tools.ShippingKaryEntry Tools.ShippingKaryLeafGeneric Tools.ShippingKaryComposed
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned
open Tools.ShippingTopShareRun
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses
open Tools.ShippingMachineAuto
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSharedLeafNL
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingMachineShipping
open Tools.ShippingSeqParentAt
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.IR.Semantics
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA
open Tools.ShippingChildTranslateA Tools.ShippingParentRanA Tools.ShippingChildComposeC Tools.ShippingChildRunAMain
open Tools.ShippingParentSeqComposedA
open Tools.ShippingSeqParentLemmas
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineCallsLinkedT
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingPortWidthsPure (nonDom declWidths declN)
open Tools.ShippingQuadComposed Tools.ShippingQuadCalls

section
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {dP dG : MachineData} {cs : List KCal} {c G : Name} {nP : Nat}
  {n kD : Nat} {ι : Type} {dom : ι → DomainConfig}
  {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
  {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
  {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
  {lsrc srcL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
  {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
  {extBL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
  (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref c dP.shape →
      KaryBnd cs G dG mctx mref cctx cref w m design →
      MachineTraceLB c dP m design dom srcL extL extBL lsrc)
  (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref c dP.shape →
      KaryBnd cs G dG mctx mref cctx cref w m design →
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) c dP kD m design dom src ext extB)
  (houtTy : ∀ o ∈ dP.shape.layout.outs, o.ty.bitWidth = o.width)
  (hFacts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      KaryBnd cs G dG mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b)
  (hOuts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      hierGate b = true → KaryBnd cs G dG mctx mref cctx cref w raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true)
  (hBdRun : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      KaryBnd cs G dG mctx mref cctx cref w raw D →
      kidsMaskedN D.modules b.body = true)
  (hdc : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      KaryBnd cs G dG mctx mref cctx cref w raw D →
      designCheck (childMap D.modules) n (checkedOptimize b) = true)


include soundL composed houtTy hFacts hOuts hBdRun hdc

/-- **The semantic conclusion for the RETURNED design `y.2`, generic over the K-callee data bundles (unit SR22, L8bb).**  K-ary form of `quad_returned`: from the outer run `h` of
`synthesizeCombinational c` returning `y` (start world `JQC O 0 w`) the SAME `M`, `Dg` carry the run conjuncts, the fact that NO module of `Dg` is named `M.name`, `y.2 = Dg`, the RAW
`ComposedG`, and `DesignSemConcl … y.1 M y.2`. -/
theorem kary_returned (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hP : KaryParentData dP cs c G nP)
    (hG : LeafData dG) (hC : KaryCallees cs dG G) (hent : KaryEntries mctx mref cctx cref cs)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = cs.length ∧
      closeLets dP.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dP.shape) dP.shape.insts.length
        dP.shape.layout.slots.length (t.inputs.map (·.name)) (dP.shape.insts.map (·.2.1))
        dP.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine dP.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) ∧ y.2 = Dg ∧
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) c dP kD M Dg dom src ext extB ∧
      DesignSemConcl n c dP kD dom src ext extB y.1 M y.2 := by
  obtain ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg, hcross, hshared, hcore,
    hcvwc, hpost, hno⟩ := kary_entry_run O T hA hP hG hC hent entryP hR0 hcl hw h
  have hpostb : y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    hpost.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hy2 : y.2 = Dg := Tools.ShippingTopShareNoParent.returned_design_eq hno
    (hpost.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  have hB : KaryBnd cs G dG mctx mref cctx cref w M Dg := ⟨O, T, hA, forall_kandk hent ⟨hR0, hw⟩⟩
  refine ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg, hcross, hshared, hcore,
    hcvwc, hpost, hno, hy2, ?_, ?_⟩
  · exact composed hcore entryP hB
  · rw [hy2]
    exact machine_design_noShips_noBd_dc_at n (KaryBnd cs G dG) (fun _ _ _ _ => True) dP
      (kD := kD) (ι := ι) (dom := dom)
      (fun hcore entry _ hB => soundL hcore entry hB)
      (fun hcore entry _ hB _ => composed hcore entry hB)
      houtTy
      (fun hcore hpost entry hB => hFacts hcore hpost entry hB)
      (fun hcore hpost entry hg hB => hOuts hcore hpost entry hg hB)
      (fun hcore hpost entry hB => hBdRun hcore hpost entry hB)
      (fun hcore hpost entry hB => hdc hcore hpost entry hB)
      hcore hpostb entryP trivial hB

/-- **The one-witness WIRED theorem, generic over the K-callee data bundles (unit SR22, L8bb).**  K-ary form of `quad_wired`: the SAME `M`, `Dg` carry the run conjuncts, `ComposedG` of the raw
`(M, Dg)`, `DesignSemConcl … y.1 M Dg` (children of the CORE run's design `Dg`) and the lookup agreement of `y.2` with `Dg` for every module not named like `M`. -/
theorem kary_wired (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hP : KaryParentData dP cs c G nP)
    (hG : LeafData dG) (hC : KaryCallees cs dG G) (hent : KaryEntries mctx mref cctx cref cs)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = cs.length ∧
      closeLets dP.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dP.shape) dP.shape.insts.length
        dP.shape.layout.slots.length (t.inputs.map (·.name)) (dP.shape.insts.map (·.2.1))
        dP.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine dP.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) c dP kD M Dg dom src ext extB ∧
      DesignSemConcl n c dP kD dom src ext extB y.1 M Dg ∧
      (∀ mn : String, mn ≠ M.name →
        Sparkle.IR.Machine.moduleByName y.2.modules mn = Sparkle.IR.Machine.moduleByName Dg.modules mn) := by
  obtain ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg, hcross, hshared, hcore,
    hcvwc, hpost, hno, hy2, hcomp, hsem⟩ :=
    kary_returned soundL composed houtTy hFacts hOuts hBdRun hdc O T hA hP hG hC hent entryP hR0 hcl hw h
  rw [hy2] at hsem
  refine ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg, hcross, hshared, hcore,
    hcvwc, hpost, hcomp, hsem, ?_⟩
  intro mn _
  rw [hy2]

end

end Tools.ShippingKaryReturned

#print axioms Tools.ShippingKaryReturned.kary_returned
#print axioms Tools.ShippingKaryReturned.kary_wired
