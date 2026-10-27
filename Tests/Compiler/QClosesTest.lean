import Tests.Compiler.QDefTest
-- C5 Q-DERIVE-HCL / Q-KID / Q-CLOSES / Q-RAN / Q-RUN (issue sparkle-gen-c5-closes): generic over `P : QSharedLeafParent`.
-- Binders are the C4 contract binders only (O T hA entryL entryW entry hw hcore); `MachineCloses` of the plain leaf is DERIVED from `P.leafLetsOk`.
-- No new premise, no sorry / axiom / native_decide.  QDefTest and the spec are not edited.
set_option autoImplicit false
set_option Elab.async false
namespace Tests.Compiler.QCloses
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tests.Compiler.CDef Tests.Compiler.QDef
open Tools.ShippingMachineSource Tools.ShippingTopShareRun Tests.Compiler.Srm9ComposedTest
open Tools.ShippingMemLeafRun Tools.ShippingNmGroup Tools.ShippingNmEntry
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingMemCloses Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingQuadComposed (genTrace)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **Q-DERIVE-HCL**: `MachineCloses` of the plain leaf, from `leafData` and `leafLetsOk` -/
theorem hcl_of_class (P : QSharedLeafParent) :
    ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref P.leaf.decl P.leaf.d.shape :=
  fun mc cc => Tools.ShippingMachineClosesData.closes_of_data (declName := P.leaf.decl) P.leaf.d
    P.leafData.ok P.leafData.body P.leafLetsOk mc mref cc cref

/-- `ChildIfaceP` of a `RealChildA` of the plain leaf -/
theorem leaf_ifaceP_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) {y : Res} (h : RealChildA O P.leaf.decl y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl P.leaf.decl) (Tools.ShippingQuadLeafGeneric.leafNk P.leaf.d)
      (P.leaf.d.shape.layout.outs.map (·.name)) [] y.1 y.2 :=
  leafKid_ifaceP O P.leafData entryL (hcl_of_class P) h

/-- the interface of an ORDINARY call's result of a wrapper, in the wrapper's per-call tables -/
theorem wrapper_ordIface (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) (w : QWrapper P.leaf)
    (k : Nat) (hk : k < w.d.shape.insts.length) (hn : (originAt w.d.shape k).child? = none) {y : Res}
    (hre : RealChildA O (w.d.shape.insts[k]).1 y) :
    ChildIfaceP (w.dat.nameK k) (w.dat.nk k) (w.dat.outsK k) (w.dat.namesK k) y.1 y.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := w.dat.ordT k hk hn
  rw [w.dat.ordKid k hk hn] at hre
  rw [h1, h2, h3, h4]
  exact leaf_ifaceP_of_class P O entryL hre

/-- `ChildIfaceP` of a `RealChildA` of a wrapper -/
theorem wrapper_ifaceP_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : QWrapper P.leaf) (entry : MachineDefines mctx mref cctx cref w.decl w.d.shape) {y : Res} (h : RealChildA O w.decl y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl w.decl) (machNIn w.d.shape)
      (w.d.shape.layout.outs.map (·.name)) w.dat.names y.1 y.2 :=
  memCallee_ifaceP O T w.dat.mem (fun m' c' _ k hk y hn hre =>
    wrapper_ordIface P O (mctx := m') (cctx := c') (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) w k hk hn hre) entry h

/-- `MachineClosesAtA` of a wrapper -/
theorem wrapper_closesA_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) (w : QWrapper P.leaf) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx w.decl w.d.shape :=
  memCallee_closesA O T hA w.dat.mem (fun k hk y hn hre => wrapper_ordIface P O entryL w k hk hn hre)

/-- the plain leaf's step contract -/
theorem leaf_step_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D P.leaf.decl [] :=
  leafKid_step_nm O hA (Tools.ShippingQuadLeafGeneric.leafOK_of_data P.leafData entryL (hcl_of_class P))

/-- `CalleeNM` of a wrapper (Gs = [], the wrapper's own `names`) -/
theorem wrapper_calleeNM_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : QWrapper P.leaf) (entry : MachineDefines mctx mref cctx cref w.decl w.d.shape) :
    CalleeNM O mctx cctx (⟨w.decl, w.d, [], w.dat.names⟩ : NCal) :=
  ⟨w.dat.mem.ok, w.dat.mem.body, ⟨w.dat.arity, w.dat.mem.callsOk, w.dat.mem.domB⟩, w.dat.mem.slots,
    w.dat.mem.insts_ne, w.dat.mem.fne,
    fun D' hD' x hx => by
      show (∃ md, x.2.child? = some md ∧ Tools.ShippingMemLeafCache.MemKid md) ∨
        (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx D' x.1 [])
      change x ∈ w.d.shape.instTagged at hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      have hk' : k < w.d.shape.insts.length := by
        rw [← Tools.ShippingInstTagged.instTagged_length]; exact hk
      rw [Tools.ShippingInstTagged.instTagged_getElem_fst, Tools.ShippingInstTagged.instTagged_getElem_snd]
      cases hc : (originAt w.d.shape k).child? with
      | some md =>
        obtain ⟨cb, aw, dw, -, hmd⟩ := Tools.ShippingSrm3Iface.origin_mem_of_child hc
        exact Or.inl ⟨md, rfl, cb, aw, dw, hmd⟩
      | none =>
        refine Or.inr ⟨rfl, ?_⟩
        rw [w.dat.ordKid k hk' hc]
        exact leaf_step_of_class P O hA entryL D' hD',
    fun k hk => Tools.ShippingInstTagged.agree_at w.dat.agree hk, w.dat.cne, List.not_mem_nil, entry,
    wrapper_closesA_of_class P O T hA entryL w⟩

theorem callees_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    NmCallees O mctx cctx P.top.decl P.cs :=
  ⟨fun e he => by
    rw [P.tieCs] at he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
    exact wrapper_calleeNM_of_class P O T hA entryL w (entryW w hw), P.csNc, P.csCd⟩

theorem iface_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    CalleeIface O P.cs := by
  intro e he y hy
  rw [P.tieCs] at he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
  exact wrapper_ifaceP_of_class P O T entryL w (entryW w hw) hy

/-! ## Q-KID -/

/-- `KidFactsNC` of a wrapper (the per-call kind dispatch: ordinary ⇒ the plain leaf's `KidFactsA`, memory ⇒ the memory tables) -/
theorem wrapper_kidFactsNC_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : QWrapper P.leaf) (entryW : MachineDefines mctx mref cctx cref w.decl w.d.shape) :
    KidFactsNC O w.decl w.d.shape.layout.outs (argWidths w.d w.dat.arity) :=
  memCallee_kidFactsNC O T w.dat.mem
    (fun m' c' _ k hk y hn hre =>
      wrapper_ordIface P O (mctx := m') (cctx := c') (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) w k hk hn hre)
    w.dat.kidOuts w.dat.kidIns w.dat.kidMemT
    (fun k hk hn => by
      rw [w.dat.ordKid k hk hn, (w.dat.kidOrdT k hk hn).1, (w.dat.kidOrdT k hk hn).2]
      exact Tools.ShippingSrm4Kid.KidFactsA.toNC
        (Tools.ShippingQuadComposed.leaf_kidFactsA O P.leafData P.leafKidData entryL (hcl_of_class P) 0))
    w.dat.cw (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (w.dat.outsClean o ho)) w.dat.scalar entryW

/-- **Q-KID**: `KidFactsNC` of every call entry of the top -/
theorem q_hkid (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    ∀ (k : Nat) (hk : k < P.top.d.shape.insts.length), KidFactsNC O (P.top.d.shape.insts[k]).1 (P.outsOf k) (P.insOf k) := by
  intro k hk
  obtain ⟨hlt, hc⟩ := P.tieCallee k hk
  have ho := P.tieOuts k hk
  have hi := P.tieIns k hk
  have hmem : P.wrappers[P.wOf k] ∈ P.wrappers := List.getElem_mem hlt
  have hcallee : (P.top.d.shape.insts[k]).1 = P.wrappers[P.wOf k].decl := by
    have h1 : (P.top.d.shape.insts.map (·.1))[k]? = some (P.top.d.shape.insts[k]).1 := by simp [hk]
    rw [h1] at hc
    have h2 : (P.wrappers.map (·.pkg.decl))[P.wOf k]? = some P.wrappers[P.wOf k].decl := by simp [hlt]
    rw [h2] at hc
    exact Option.some.inj hc
  have ho' : P.outsOf k = P.wrappers[P.wOf k].d.shape.layout.outs := by
    rw [ho]; simp [List.getD_eq_getElem?_getD, hlt]
  have hi' : P.insOf k = argWidths P.wrappers[P.wOf k].d P.wrappers[P.wOf k].dat.arity := by
    rw [hi]; simp [List.getD_eq_getElem?_getD, hlt]
  rw [hcallee, ho', hi']
  exact wrapper_kidFactsNC_of_class P O T entryL _ (entryW _ hmem)

/-! ## Q-CLOSES / Q-RAN / Q-RUN -/

/-- **Q-CLOSES**: `MachineClosesAtStart0` of the class's top -/
theorem closes0_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx P.top.decl P.top.d.shape :=
  nm_closes0 O hA P.pdata (callees_of_class P O T hA entryL entryW) (iface_of_class P O T entryL entryW)

/-- **Q-RAN** -/
theorem ranA_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx P.top.decl P.top.d.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (closes0_of_class P O T hA entryL entryW) hw

/-- **Q-RUN** -/
theorem machineRun_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 P.top.decl P.top.d.shape m design :=
  nm_machineRun O hA P.pdata (callees_of_class P O T hA entryL entryW) (iface_of_class P O T entryL entryW) entry hw hcore

/-- **soundLA for the class** -/
theorem soundLA_of_class (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineAuto.MachineTraceLB P.top.decl P.top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      P.top.src P.top.extS P.top.extBS P.top.lsrc := by
  letI := P.top.inh
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    genTrace O T hA P.top.d (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) P.top.gen (D₀ := 0)
      (machineRun_of_class P O T hA entryL entryW entry hw hcore)
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

/-! ## corollaries for `P_Q` (statements of the `topshareQ_*` theorems, `hcl` dropped: it is derived) -/
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidEntryTest Tests.Compiler.SharedLeafMemKidIfaceTest

theorem P_Q_entryW (hgrp : TqGrp)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) :
    ∀ wp ∈ (P_Q hgrp).wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape := by
  intro wp hwp
  change wp ∈ [(⟨wrapPPkg, wrapPDat⟩ : QWrapper qLeafP), ⟨wrapQPkg, wrapQDat⟩] at hwp
  rcases List.mem_cons.mp hwp with rfl | h
  · exact entry₁
  · rcases List.mem_cons.mp h with rfl | h
    · exact entry₂
    · exact absurd h List.not_mem_nil

theorem topshareQ_hkid_of_class (hgrp : TqGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) :
    ∀ (k : Nat) (hk : k < topshareQ.machineData.shape.insts.length),
      KidFactsNC O (topshareQ.machineData.shape.insts[k]).1 (tqOuts k) (tqIns k) :=
  q_hkid (P_Q hgrp) O T hR0 (P_Q_entryW hgrp entry₁ entry₂)

theorem topshareQ_closes0_of_class (hgrp : TqGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape :=
  closes0_of_class (P_Q hgrp) O T hA hR0 (P_Q_entryW hgrp entry₁ entry₂)

theorem topshareQ_ranA_of_class (hgrp : TqGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``topshareQ topshareQ.machineData.shape raw D :=
  ranA_of_class (P_Q hgrp) O T hA hR0 (P_Q_entryW hgrp entry₁ entry₂) entry hcore hw

theorem topshareQ_machineRun_of_class (hgrp : TqGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design :=
  machineRun_of_class (P_Q hgrp) O T hA hR0 (P_Q_entryW hgrp entry₁ entry₂) entryP hw hcore

theorem topshareQ_soundLA_of_class (hgrp : TqGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineAuto.MachineTraceLB ``topshareQ topshareQ.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineSource
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareQ.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareQ.machineInits
        topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB) :=
  soundLA_of_class (P_Q hgrp) O T hA hR0 (P_Q_entryW hgrp entry₁ entry₂) entryP hw hcore

/-! ## audits -/

-- (1) isDefEq type check of each generic theorem against its stated form
open Lean Meta Elab Term in
run_cmd Lean.Elab.Command.liftTermElabM do
  let chk (n : Name) (stx : TermElabM Syntax) : TermElabM Unit := do
    let ci ← getConstInfo n
    let e ← elabTerm (← stx) none
    synthesizeSyntheticMVarsNoPostponing
    unless ← isDefEq ci.type (← instantiateMVars e) do throwError "QCLOSES AUDIT FAILED: {n} type differs from the stated theorem"
  chk ``hcl_of_class `(∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State} (P : QSharedLeafParent),
    ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref P.leaf.decl P.leaf.d.shape)
  chk ``q_hkid `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
      (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
      (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape),
      ∀ (k : Nat) (hk : k < P.top.d.shape.insts.length), KidFactsNC O (P.top.d.shape.insts[k]).1 (P.outsOf k) (P.insOf k))
  chk ``closes0_of_class `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
      (hA : AdmCtx O.quiet mctx cctx)
      (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
      (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape),
      MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx P.top.decl P.top.d.shape)
  chk ``ranA_of_class `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
      (hA : AdmCtx O.quiet mctx cctx)
      (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
      (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
      (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
      {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
      (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w),
      Tools.ShippingParentRanA.MachineRanA O mctx cctx P.top.decl P.top.d.shape raw D)
  chk ``machineRun_of_class `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
      (hA : AdmCtx O.quiet mctx cctx)
      (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
      (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
      (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
      {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hw : JQC O 0 w)
      (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w'),
      Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 P.top.decl P.top.d.shape m design)
  chk ``soundLA_of_class `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
      (hA : AdmCtx O.quiet mctx cctx)
      (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
      (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
      (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
      {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hw : JQC O 0 w)
      (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w'),
      Tools.ShippingMachineAuto.MachineTraceLB P.top.decl P.top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
        P.top.src P.top.extS P.top.extBS P.top.lsrc)
  logInfo m!"QCLOSES|ok|isDefEq type check of the 7 generic theorems"

-- (2) binder lists of the generic roots
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let spec : List (Name × List (String × Bool)) :=
    [(``hcl_of_class, [("mref", true), ("cref", true), ("P", false), ("mc", false), ("cc", false)]),
     (``q_hkid, [("mctx", true), ("mref", true), ("cctx", true), ("cref", true), ("P", false), ("O", false), ("T", false),
        ("entryL", false), ("entryW", false), ("k", false), ("hk", false)]),
     (``closes0_of_class, [("mctx", true), ("mref", true), ("cctx", true), ("cref", true), ("P", false), ("O", false), ("T", false),
        ("hA", false), ("entryL", false), ("entryW", false)]),
     (``ranA_of_class, [("mctx", true), ("mref", true), ("cctx", true), ("cref", true), ("P", false), ("O", false), ("T", false),
        ("hA", false), ("entryL", false), ("entryW", false), ("entry", false), ("w", true), ("w1", true), ("raw", true), ("D", true),
        ("hcore", false), ("hw", false)]),
     (``machineRun_of_class, [("mctx", true), ("mref", true), ("cctx", true), ("cref", true), ("P", false), ("O", false), ("T", false),
        ("hA", false), ("entryL", false), ("entryW", false), ("entry", false), ("w", true), ("w'", true), ("m", true), ("design", true),
        ("hw", false), ("hcore", false)]),
     (``soundLA_of_class, [("mctx", true), ("mref", true), ("cctx", true), ("cref", true), ("P", false), ("O", false), ("T", false),
        ("hA", false), ("entryL", false), ("entryW", false), ("entry", false), ("w", true), ("w'", true), ("m", true), ("design", true),
        ("hw", false), ("hcore", false)])]
  for (n, exp) in spec do
    let ci ← getConstInfo n
    forallTelescope ci.type fun xs _ => do
      let mut got : List (String × Bool) := []
      for x in xs do
        got := got ++ [((← x.fvarId!.getUserName).toString, (← x.fvarId!.getBinderInfo) == .implicit)]
      unless got == exp do throwError "QCLOSES AUDIT FAILED: binders of {n} are {got}, expected {exp}"
      -- no hcl / hR0 / premise-like binder beyond the contract
      for (nm, _) in got do
        if ["hcl", "hR0", "hcomposed", "hkid", "hF", "hcalls"].contains nm then
          throwError "QCLOSES AUDIT FAILED: {n} has the extra binder {nm}"
  logInfo m!"QCLOSES|ok|binder lists of the 6 generic roots are the C4 contract binders (no hcl)"

-- (3) the corollaries' types are the `topshareQ_*` statements with the group binder and the (now derived) `hcl` dropped
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let pairs : List (Name × Name) :=
    [(``topshareQ_closes0_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_closes0_derived),
     (``topshareQ_machineRun_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_machineRun_derived),
     (``topshareQ_ranA_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_ranA),
     (``topshareQ_soundLA_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_soundLA),
     (``topshareQ_hkid_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hkid)]
  for (n, o) in pairs do
    let ci ← getConstInfo n
    let oi ← getConstInfo o
    let isHcl := fun (t : Expr) => t.isForall && (t.bindingBody!.isForall) &&
      (t.bindingBody!.bindingBody!.getAppFn.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)
    -- drop the group binder from the corollary
    let ok1 ← forallTelescope ci.type fun xs body => do
      let mut keep := #[]
      let mut dropped : Nat := 0
      for x in xs do
        let t ← inferType x
        if t.isConstOf ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp then dropped := dropped + 1 else keep := keep.push x
      unless dropped == 1 do throwError "QCLOSES AUDIT FAILED: {n} has {dropped} TqGrp binders"
      -- drop `hcl` from the original
      let ok ← forallTelescope oi.type fun ys obody => do
        let mut keepO := #[]
        let mut droppedO : Nat := 0
        for y in ys do
          let t ← inferType y
          if isHcl t then droppedO := droppedO + 1 else keepO := keepO.push y
        unless droppedO == 1 do throwError "QCLOSES AUDIT FAILED: {o} has {droppedO} hcl binders"
        isDefEq (← mkForallFVars keep body) (← mkForallFVars keepO obody)
      pure ok
    unless ok1 do throwError "QCLOSES AUDIT FAILED: {n} vs {o} (hcl dropped)"
  logInfo m!"QCLOSES|ok|5 corollary types defeq to the topshareQ_* statements with hcl (derived) and the group binder dropped"

-- (4) closure walks: every `Tests.*` constant reached from a generic root is a class (`QDef` / `CDef`) or generic-helper constant
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``hcl_of_class, ``q_hkid, ``closes0_of_class, ``ranA_of_class, ``machineRun_of_class, ``soundLA_of_class]
  let generic := [``leaf_ifaceP_of_class, ``wrapper_ordIface, ``wrapper_ifaceP_of_class, ``wrapper_closesA_of_class, ``leaf_step_of_class,
    ``wrapper_calleeNM_of_class, ``callees_of_class, ``iface_of_class, ``wrapper_kidFactsNC_of_class] ++ roots
  for r in roots do
    let mut seen : NameSet := {}
    let mut work : List Name := [r]
    let mut reached : Array Name := #[]
    while !work.isEmpty do
      let n := work.head!
      work := work.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "QCLOSES CLOSURE FAILED: {n} not found"
      -- bodies read from thmInfo / defnInfo (`value?` does not return theorem bodies here)
      let body? : Option Lean.Expr := match ci with
        | .thmInfo t => some t.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      let cs := ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[]
      for c in cs do
        if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c then
          reached := reached.push c
          work := c :: work
    for c in reached do
      let cls := (c.toString.splitOn "Tests.Compiler.QDef.").length > 1 || (c.toString.splitOn "Tests.Compiler.CDef.").length > 1
      let own := (c.toString.splitOn "Tests.Compiler.QCloses.").length > 1
      unless cls || own do throwError "QCLOSES CLOSURE FAILED: {r} reaches {c} (outside the class definition and this file)"
      if own then
        unless generic.any (fun g => (c.toString.splitOn g.toString).length > 1) do
          throwError "QCLOSES CLOSURE FAILED: {r} reaches the non-generic own constant {c}"
      for comp in c.components.map (·.toString) do
        if ["P_Q", "P_M", "TqGrp", "TmGrp", "wrapP", "wrapQ", "wrapM", "wrapM3", "leafP", "leafM", "csQ", "csM", "namesP", "namesQ",
            "wrapPDat", "wrapQDat", "wrapPPkg", "wrapQPkg", "qLeafP", "tqOuts", "tqIns", "tqBsC", "tqOutsC", "tqSrcC"].contains comp
            || comp.startsWith "topshare" || comp.startsWith "Tq" || comp.startsWith "tq" || comp.startsWith "wp" || comp.startsWith "wq" then
          throwError "QCLOSES CLOSURE FAILED: {r} reaches {c} (instance component {comp})"
    logInfo m!"QCLOSES|closure ok|{r}: {reached.size} Tests constants, all class / generic-helper constants"

-- (5) axioms
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let all := [``hcl_of_class, ``leaf_ifaceP_of_class, ``wrapper_ordIface, ``wrapper_ifaceP_of_class, ``wrapper_closesA_of_class,
    ``leaf_step_of_class, ``wrapper_calleeNM_of_class, ``callees_of_class, ``iface_of_class, ``wrapper_kidFactsNC_of_class, ``q_hkid,
    ``closes0_of_class, ``ranA_of_class, ``machineRun_of_class, ``soundLA_of_class, ``P_Q_entryW, ``topshareQ_hkid_of_class,
    ``topshareQ_closes0_of_class, ``topshareQ_ranA_of_class, ``topshareQ_machineRun_of_class, ``topshareQ_soundLA_of_class]
  for a in all do
    let axs ← Lean.collectAxioms a
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "QCLOSES AUDIT FAILED: non-standard axiom {x} in {a}"
  logInfo m!"QCLOSES|ok|{all.length} constants with standard axioms only"

end Tests.Compiler.QCloses

open Tests.Compiler.QCloses in
#print axioms hcl_of_class
open Tests.Compiler.QCloses in
#print axioms q_hkid
open Tests.Compiler.QCloses in
#print axioms closes0_of_class
open Tests.Compiler.QCloses in
#print axioms ranA_of_class
open Tests.Compiler.QCloses in
#print axioms machineRun_of_class
open Tests.Compiler.QCloses in
#print axioms soundLA_of_class
