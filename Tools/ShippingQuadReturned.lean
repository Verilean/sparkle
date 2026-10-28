import Tools.ShippingQuadLeafGeneric
import Tools.ShippingSeqParentAt
-- BUILT (unit SR14): r1 exit 0 (this module, dev run); the final-SHA rebuild is in REPORT-SR14.md.
-- SCOPE (binding, ledger L8at): the RETURNED-design theorem (`y.2 = Dg`) and the one-witness WIRED theorem of the shared-leaf class QUAD, generic over the
-- data bundles `QuadParentData` / `LeafCalleeData` / `LeafData` (no `topshare` / `wrap` / `wrap3` / `acc` in any statement).  Generic forms of SR11
-- `Tests.Compiler.TopShareComposedTest.topshare_wired` and SR12 `Tests.Compiler.TopShareReturnedTest.topshare_returned`.
-- PROVED here: the parent's run with the returned value linked and NO module of `Dg` named like the entry (`quad_entry_run_ret_np`), hence `y.2 = Dg`
-- (`returned_design_eq`), and the transport of the endpoint's conclusion to the returned design: the SAME `M`, `Dg` carry the run conjuncts, `ComposedG`,
-- `DesignSemConcl … y.1 M y.2`.
-- PREMISES (named, one per block): `soundL` (the machine trace of the parent), `composed`, `houtTy`, `hFacts` (RunFacts), `hOuts` (outsCheck), `hBdRun`
-- (kidsMasked), `hdc` (designCheck) — exactly the block arguments of `machine_design_noShips_noBd_dc_at`, quantified over the class boundary `QuadBnd`
-- (the callees' and the leaf's `MachineDefines` + `JQC O 0 w`).  These per-callee composed / trace / kidFacts blocks are NOT derived generically here (OPEN:
-- an instance supplies them; for `topshare` the `ts_*` lemmas).  Also premises: `O`, `T`, `hA`, `MachineDefines` of parent / callees / leaf, `MachineCloses` of
-- the leaf, `JQC O 0 w`, the decidable data facts.  `RealChildA` / `ServedRealA` / `JQC` are histories, not freshness or semantic correctness in the current
-- environment.  The conclusion is `checkedOptimize` of the RETURNED module `y.1` judged with the children of the returned design `y.2 = Dg`.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field; no existing statement changed.
namespace Tools.ShippingQuadReturned
open Tools.ShippingQuadLeafGeneric
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

/-- The class boundary of the QUAD endpoint: the callees' and the leaf's `MachineDefines` (the leaf twice, as in the one-chain boundary of the
hand-written `ts_Bnd`) and the start world `JQC O 0 w`. -/
def QuadBnd (c₁ c₂ G : Name) (d₁ d₂ dG : MachineData) : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref c₁ d₁.shape ∧ MachineDefines mctx mref cctx cref G dG.shape ∧
    MachineDefines mctx mref cctx cref c₂ d₂.shape ∧ MachineDefines mctx mref cctx cref G dG.shape ∧
    JQC O 0 w

section
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
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
      QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w m design →
      MachineTraceLB c dP m design dom srcL extL extBL lsrc)
  (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref c dP.shape →
      QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w m design →
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) c dP kD m design dom src ext extB)
  (houtTy : ∀ o ∈ dP.shape.layout.outs, o.ty.bitWidth = o.width)
  (hFacts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b)
  (hOuts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      hierGate b = true → QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true)
  (hBdRun : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w raw D →
      kidsMaskedN D.modules b.body = true)
  (hdc : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
      {raw b : Sparkle.IR.AST.Module} {D : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref c dP.shape →
      QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w raw D →
      designCheck (childMap D.modules) n (checkedOptimize b) = true)

include soundL composed houtTy hFacts hOuts hBdRun hdc

/-- **The semantic conclusion for the RETURNED design `y.2`, generic over the QUAD data bundles (unit SR14, L8at).**  Generic form of
`Tests.Compiler.TopShareReturnedTest.topshare_returned`: from the outer run `h` of `synthesizeCombinational c` returning `y` (start world `JQC O 0 w`) the SAME
`M`, `Dg` carry the run conjuncts, the fact that NO module of `Dg` is named `M.name`, `y.2 = Dg`, the RAW `ComposedG`, and `DesignSemConcl … y.1 M y.2`. -/
theorem quad_returned (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP)
    (hG : LeafData dG) (h₁ : LeafCalleeData d₁ dG c₁ G n₁) (h₂ : LeafCalleeData d₂ dG c₂ G n₂)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      closeLets dP.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dP.shape) dP.shape.insts.length
        dP.shape.layout.slots.length (t.inputs.map (·.name)) (dP.shape.insts.map (·.2.1))
        dP.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dP.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) ∧ y.2 = Dg ∧
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) c dP kD M Dg dom src ext extB ∧
      DesignSemConcl n c dP kD dom src ext extB y.1 M y.2 := by
  obtain ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost, hno⟩ := quad_entry_run_ret_np O T hA hP hG h₁ h₂ entryP entry₁ entry₂ hR0 hcl hw h
  have hpostb : y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    hpost.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hy2 : y.2 = Dg := Tools.ShippingTopShareNoParent.returned_design_eq hno
    (hpost.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  have hB : QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w M Dg := ⟨O, T, hA, entry₁, hR0, entry₂, hR0, hw⟩
  refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost, hno, hy2, ?_, ?_⟩
  · exact composed hcore entryP hB
  · rw [hy2]
    exact machine_design_noShips_noBd_dc_at n (QuadBnd c₁ c₂ G d₁ d₂ dG) (fun _ _ _ _ => True) dP
      (kD := kD) (ι := ι) (dom := dom)
      (fun hcore entry _ hB => soundL hcore entry hB)
      (fun hcore entry _ hB _ => composed hcore entry hB)
      houtTy
      (fun hcore hpost entry hB => hFacts hcore hpost entry hB)
      (fun hcore hpost entry hg hB => hOuts hcore hpost entry hg hB)
      (fun hcore hpost entry hB => hBdRun hcore hpost entry hB)
      (fun hcore hpost entry hB => hdc hcore hpost entry hB)
      hcore hpostb entryP trivial hB

/-- **The one-witness WIRED theorem, generic over the QUAD data bundles (unit SR14, L8at).**  Generic form of
`Tests.Compiler.TopShareComposedTest.topshare_wired`: the SAME `M`, `Dg` carry the run conjuncts, `ComposedG` of the raw `(M, Dg)`, `DesignSemConcl … y.1 M Dg`
(children of the CORE run's design `Dg`) and the lookup agreement of `y.2` with `Dg` for every module not named like `M`.  (It is the
`quad_returned` proof with the transport `y.2 = Dg` replaced by the lookup lemma.) -/
theorem quad_wired (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP)
    (hG : LeafData dG) (h₁ : LeafCalleeData d₁ dG c₁ G n₁) (h₂ : LeafCalleeData d₂ dG c₂ G n₂)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      closeLets dP.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dP.shape) dP.shape.insts.length
        dP.shape.layout.slots.length (t.inputs.map (·.name)) (dP.shape.insts.map (·.2.1))
        dP.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dP.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
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
  obtain ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost, hno, hy2, hcomp, hsem⟩ :=
    quad_returned soundL composed houtTy hFacts hOuts hBdRun hdc O T hA hP hG h₁ h₂ entryP entry₁ entry₂ hR0 hcl hw h
  rw [hy2] at hsem
  refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hcl', hj, hcv, hcc, hkt, hcoh, hg1, hg2, hcross, hshared, hcore,
    hcvwc, hpost, hcomp, hsem, ?_⟩
  intro mn _
  rw [hy2]

end

end Tools.ShippingQuadReturned
