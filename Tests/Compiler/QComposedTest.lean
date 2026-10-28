import Tests.Compiler.QShipsTest
import Tools.ShippingSrm28Regs
import Tools.ShippingSrm32Width
set_option autoImplicit false
set_option Elab.async false
-- C5 Q-COMPOSED (issue sparkle-gen-c5-composed): `hcomposedQ_of_class : HComposedQ P` for any `P : QSharedLeafParent`, from the ONE staged
-- hypothesis `QHCallsStmt P` (= Q-HCALLS, proved in parallel as hcalls_of_classQ); `qSharedLeaf_ships_of_hcalls` = the frozen C5 statement with it.
namespace Tests.Compiler.QComposed
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Callee Tools.ShippingSrm4Run
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingQuadComposed (GenFacts genTrace bsIn_drop_nodomain callsOk_args QuadGroupFacts)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineDepthRunRA Tools.ShippingMachineDepth
open Tools.ShippingSeqParentLemmas (HCallsOf)
open Tools.ShippingMachineCausal (letObsB)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMachineCallsLinkedT
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingNmGroup (NCal)
open Tools.ShippingMemCloses (ChildIfaceP)
open Sparkle.IR.RegDedup (declWidth)
open Tests.Compiler.CDef
open Sparkle.IR.OptCheck Sparkle.IR.HierCheck Sparkle.IR.Semantics
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMixedSourceBridge
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingMachineAuto
open Tests.Compiler.QDef
open Tests.Compiler.QShips (HComposedQ QBnd)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the STAGED named hypothesis (Q-HCALLS): the per-wrapper `HCallsOf 1` of the ordinary-call route -/
def QHCallsStmt (P : QSharedLeafParent) : Prop :=
  ∀ (w : QWrapper P.leaf), w ∈ P.wrappers → ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
    HCallsOf 1 w.pkg.d design m (dom := fun i : DomainConfig => i) w.pkg.lsrc w.pkg.extS w.pkg.extBS w.dat.arity
      (Tools.ShippingSrm4Mixed.genBsC P.leaf.decl P.leaf.d.bsIn) (Tools.ShippingSrm4Mixed.genOutsC P.leaf.decl P.leaf.d.shape.layout.outs)
      (Tools.ShippingSrm4Mixed.genSrcC P.leaf.decl P.leaf.d.bsIn P.leaf.src)
      (Tools.ShippingSrm4Mixed.genPC (fun mc => Tools.ShippingGateChild.MachineRun P.leaf.decl P.leaf.d.shape mc))

/-- what a served run of a wrapper must establish, indexed by `P.wrappers` -/
def qPC (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) :
    Lean.Name → Sparkle.IR.AST.Module → Prop := fun n mc =>
  ∀ w ∈ P.wrappers, w.decl = n →
    MachineRunNCA O w.decl w.d.shape (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape) mc design

theorem q_map_getElem? {α β : Type} (f : α → β) {l : List α} {k : Nat} (hk : k < l.length) : (l.map f)[k]? = some (f l[k]) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl

/-! ## the wrappers' depth-2 runs and served runs -/

theorem q_callRun (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : QWrapper P.leaf) (hH : QHCallsStmt P) (hw : w ∈ P.wrappers) (design : Sparkle.IR.AST.Design)
    {mc : Sparkle.IR.AST.Module}
    (hmc : MachineRunNCA O w.decl w.d.shape (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape) mc design) :
    SeqChildRunN (childMap design.modules) design 2 mc (List.take w.dat.arity w.d.bsIn) w.d.shape.layout.outs
      (fun vals => w.pkg.src defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take w.dat.arity w.d.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take w.dat.arity w.d.bsIn) vals)) := by
  letI := w.pkg.inh
  exact Tools.ShippingSrm4Mixed.callee_seqChildRunN2 (srcG := P.leaf.src) (bsG := P.leaf.d.bsIn)
    (outsG := P.leaf.d.shape.layout.outs) (PCs := fun _ mc => Tools.ShippingGateChild.MachineRun P.leaf.decl P.leaf.d.shape mc)
    O T w.dat.mem w.dat.outOk w.pkg.gen (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape)
    (fun {m c w' mm dd} hB k c' hc hnone mctx' cctx' mc' Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < w.d.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
      have hck : c' = P.leaf.decl := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc
        rw [← Option.some.inj hc]
        exact w.dat.ordKid k hk hnone
      subst hck
      exact ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hB,
        Tests.Compiler.QCloses.hcl_of_class P mctx' cctx'⟩)
    (fun m design => hH w hw m design) w.dat.hextB w.dat.hext defaultDomain hmc
    (fun m c hA => Tests.Compiler.QCloses.wrapper_closesA_of_class (mctx := m) (cctx := c) P O T hA (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) w)

theorem q_runWrap (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : QWrapper P.leaf) (entryW : MachineDefines mctx mref cctx cref w.decl w.d.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design} (hreal : RealChildA O w.decl (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    MachineRunNCA O w.decl w.d.shape (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape) mc design :=
  machineRunNCA_of_real_main O T (BndA := fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape)
    hreal hcons entryW (fun _ _ _ _ _ _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx entryL)
    (fun m c _ _ _ hch _ => by
      obtain ⟨_, _, _, hadm', _⟩ := hch
      exact Tests.Compiler.QCloses.wrapper_closesA_of_class (mctx := m) (cctx := c) P O T hadm'
        (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) w)
    w.dat.mem.insts_ne

/-! ## the parent's side facts, from `P.pdata` -/

theorem q_callsOk_nIn (d : MachineData) (n : Nat) (h : d.callsOk n = true) : n + d.shape.insts.length = d.nIn := by
  unfold Tools.ShippingMachineAuto.MachineData.callsOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

theorem q_ok_slotLet (d : MachineData) (h : d.ok = true) :
    (∀ b ∈ d.slotBs, b.2 ≠ .domain) ∧ (∀ b ∈ d.letBs, b.2 ≠ .domain) := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨-, -, -, slotKinds, letKinds, -⟩ := h
  exact ⟨slotKinds, letKinds⟩

theorem q_parent_hkD (P : QSharedLeafParent) : P.nDecl ≤ P.top.d.bsIn.length := by
  have h1 := Tools.ShippingQuadCalls.ok_bsIn_length P.top.d P.pdata.ok
  have h2 := q_callsOk_nIn P.top.d P.nDecl P.pdata.callsOk
  omega

theorem q_parent_hIlen (P : QSharedLeafParent) : (P.top.d.bsIn.drop P.nDecl).length = P.top.d.shape.insts.length := by
  have h1 := Tools.ShippingQuadCalls.ok_bsIn_length P.top.d P.pdata.ok
  have h2 := q_callsOk_nIn P.top.d P.nDecl P.pdata.callsOk
  simp only [List.length_drop]
  omega

theorem q_parent_hSL (P : QSharedLeafParent) : ∀ b ∈ P.top.d.slotBs ++ P.top.d.letBs, b.2 ≠ .domain := by
  intro b hb
  obtain ⟨h1, h2⟩ := q_ok_slotLet P.top.d P.pdata.ok
  rcases List.mem_append.mp hb with h | h
  · exact h1 b h
  · exact h2 b h

theorem q_parent_hSlen (P : QSharedLeafParent) : P.top.d.slotBs.length = P.top.d.shape.layout.slots.length := by
  have h1 := Tools.ShippingQuadCalls.ok_len P.top.d P.pdata.ok
  have h2 := P.pdata.slots
  simp only [MachineData.slotBs, List.length_take, List.length_drop]
  omega

theorem q_parent_hLlen (P : QSharedLeafParent) : P.top.d.letBs.length = P.top.d.shape.layout.lets :=
  (Tools.ShippingQuadCalls.ok_lets P.top.d P.pdata.ok).symm

theorem q_parent_hNIn (P : QSharedLeafParent) :
    machNIn P.top.d.shape = ((P.top.d.bsIn.take P.nDecl).filter (fun b => b.2 != .domain)).length := by
  have h1 := Tools.ShippingQuadCalls.ok_len P.top.d P.pdata.ok
  have h2 := Tools.ShippingQuadCalls.ok_lets P.top.d P.pdata.ok
  have h3 : P.top.d.letBs.length = P.top.d.shape.binders.length - (P.top.d.nIn + P.top.d.ss.length) := by
    simp only [MachineData.letBs, List.length_drop]
  have h4 := q_callsOk_nIn P.top.d P.nDecl P.pdata.callsOk
  have h5 := P.pdata.slots
  unfold machNIn
  have h6 : P.top.d.shape.binders.length - P.top.d.shape.insts.length - P.top.d.shape.layout.slots.length
      - P.top.d.shape.layout.lets = P.nDecl := by omega
  rw [h6]
  simp only [MachineData.bsIn, List.take_take]
  have h7 : min P.nDecl P.top.d.nIn = P.nDecl := by omega
  rw [h7]

/-! ## the parent's per-call `SeqFactsRN` at depth 2 -/

theorem q_hcallsNW (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) (hH : QHCallsStmt P) :
    HCallsOf 2 P.top.d design m (dom := fun _ : Unit => defaultDomain) P.top.lsrc P.top.extS P.top.extBS P.nDecl
      P.bsC P.outsC P.srcC (qPC P O design) := by
  intro i bools bits k c' hk2
  obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hk2
  have hlt : k < P.top.d.shape.insts.length := by simpa using hlt'
  have hget' : (P.top.d.shape.insts[k]).1 = c' := by simpa using hget
  subst hget'
  right
  unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  obtain ⟨hR, hF⟩ := P.group i bools bits k hlt
  obtain ⟨-, hc'⟩ := Tools.ShippingNmEntry.nm_call_callee P.pdata.names hlt
  have hjc := Tools.ShippingNmEntry.nm_idx_lt P.pdata.names hlt
  have hcl : P.cs.length = P.wrappers.length := by rw [P.tieCs]; simp
  have hjw : k / 2 < P.wrappers.length := hcl ▸ hjc
  have tieCs' : P.cs = P.wrappers.map (fun w => (⟨w.pkg.decl, w.pkg.d, [], w.dat.names⟩ : NCal)) := P.tieCs
  have hcw : P.cs[k / 2]? = some (⟨P.wrappers[k / 2].pkg.decl, P.wrappers[k / 2].pkg.d, [], P.wrappers[k / 2].dat.names⟩ : NCal) := by
    rw [tieCs', List.getElem?_map, List.getElem?_eq_getElem hjw] <;> rfl
  have hcc : P.cs[k / 2]'hjc = (⟨P.wrappers[k / 2].pkg.decl, P.wrappers[k / 2].pkg.d, [], P.wrappers[k / 2].dat.names⟩ : NCal) := by
    have h1 : P.cs[k / 2]? = some (P.cs[k / 2]'hjc) := List.getElem?_eq_getElem hjc
    rw [hcw] at h1
    exact (Option.some.inj h1).symm
  have hdecl : (P.top.d.shape.insts[k]).1 = P.wrappers[k / 2].decl := by rw [hc', hcc]
  have hnN : Tools.ShippingNmEntry.nNk P.cs k = machNIn P.wrappers[k / 2].d.shape := by
    unfold Tools.ShippingNmEntry.nNk
    rw [hcw] <;> rfl
  have hwmem : P.wrappers[k / 2] ∈ P.wrappers := List.getElem_mem hjw
  have hbs : P.bsC P.wrappers[k / 2].decl = P.wrappers[k / 2].d.bsIn.take P.wrappers[k / 2].dat.arity :=
    P.tieBsC _ hwmem
  have hos : P.outsC P.wrappers[k / 2].decl = P.wrappers[k / 2].d.shape.layout.outs := P.tieOutsC _ hwmem
  have hsr : P.srcC () P.wrappers[k / 2].decl = fun vals => P.wrappers[k / 2].pkg.src defaultDomain
      (Tools.ShippingMachineChild.boolsOf (P.wrappers[k / 2].d.bsIn.take P.wrappers[k / 2].dat.arity) vals)
      (Tools.ShippingMachineChild.bitsOf (P.wrappers[k / 2].d.bsIn.take P.wrappers[k / 2].dat.arity) vals) :=
    P.tieSrcC _ hwmem
  refine ⟨Tools.ShippingQuadLeafGeneric.origin_child_none _ (P.pdata.nomemKey k hlt), (P.top.d.shape.insts[k]).2.1,
    q_map_getElem? (fun x => x.2.1) hlt, ?_,
    Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args P.top.d P.nDecl P.pdata.callsOk k hlt)
      (by simp [GenPkg.lsrc, letObsB]), hR, hF⟩
  intro mc hmc
  have hmc' := hmc P.wrappers[k / 2] hwmem hdecl.symm
  have hr := q_callRun P O T entryL P.wrappers[k / 2] hH hwmem design hmc'
  rw [hdecl]
  refine ⟨?_, ?_⟩
  · rw [hbs, hos, hsr]; exact hr
  · rw [hr.2.2.2.2.2.1, ← P.wrappers[k / 2].dat.mem.hNIn, ← P.pdata.argsN k hlt, hnN]

/-! ## the parent's trace -/

theorem q_traceXA (P : QSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hRun : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 P.top.decl P.top.d.shape m design) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingServedRealA.ServedRealA O P.top.decl P.top.d.shape m design) P.top.decl P.top.d m design
      (fun _ : Unit => defaultDomain) P.top.src P.top.extS P.top.extBS P.top.lsrc := by
  letI := P.top.inh
  exact genTrace O T hA P.top.d (fun _ : Unit => defaultDomain) P.top.gen (D₀ := 0) hRun

/-! ## the generic `ComposedNW 2` and `HComposedQ` -/

theorem composedNW_of_classQ (P : QSharedLeafParent) (hH : QHCallsStmt P)
    {w w' : Void IO.RealWorld}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    (hw : JQC O 0 w) {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineDepthRun.ComposedNW 2 P.top.decl P.top.d P.nDecl m design (fun _ : Unit => defaultDomain)
      P.top.src P.top.extS P.top.extBS :=
  machine_linkedT_callsRNA 2 O
    (q_traceXA P O T hA (Tests.Compiler.QCloses.machineRun_of_class P O T hA entryL entryW entry hw hcore))
    P.pdata.fne P.nDecl (q_parent_hkD P)
    (bsIn_drop_nodomain P.top.d P.nDecl P.pdata.domB)
    (q_parent_hIlen P) (q_parent_hSL P) (q_parent_hSlen P) (q_parent_hLlen P) (q_parent_hNIn P)
    P.bsC P.outsC P.srcC (qPC P O design)
    (q_hcallsNW P O T entryL m design hH)
    (fun k c' hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      intro wp hwp hdecl
      subst hdecl
      exact q_runWrap P O T entryL wp (entryW wp hwp) (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons)

theorem composedNWRegs_of_classQ (P : QSharedLeafParent) (hH : QHCallsStmt P)
    {w w' : Void IO.RealWorld}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    (hw : JQC O 0 w) {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w')
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    Tools.ShippingSrm28.ComposedNWRegs 2 P.top.decl P.top.d P.nDecl raw D (fun _ : Unit => defaultDomain)
      P.top.src P.top.extS P.top.extBS
      (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        P.top.d.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r) := by
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingSrm4Core2.core_hierGate_anyAM O P.top.d P.pdata.ok P.pdata.body (nDecl := P.nDecl) P.pdata.callsOk
      P.pdata.slots P.pdata.domB P.pdata.insts_ne P.pdata.fne P.outTy hpost
      (Tests.Compiler.QCloses.ranA_of_class P O T hA entryL entryW entry hcore hw)
  exact Tools.ShippingSrm28.composedNWRegs_of_composedNW _
    (composedNW_of_classQ P hH O T hA entryL entryW entry hw hcore)
    (fun _ _ _ _ _ _ hW => Tools.ShippingSrm32.hWd_of_wired hpost hgate P.outTy hW)

/-- **Q-COMPOSED**: the staged composed binder of the assembly, generically, from the one staged hypothesis `QHCallsStmt P`. -/
theorem hcomposedQ_of_class (P : QSharedLeafParent) (hH : QHCallsStmt P) : Tests.Compiler.QShips.HComposedQ P := by
  intro mctx mref cctx cref w w' m design b hcore hpost entry _ hB _
  obtain ⟨O, T, hA, entryL, entryW, hw⟩ := hB
  exact composedNWRegs_of_classQ P hH O T hA entryL entryW entry hw hcore hpost


/-- **C5 with the one staged hypothesis `hH`** (placed right after `P`): the frozen statement (scripts/c5/C5_STATEMENT.lean.txt). -/
theorem qSharedLeaf_ships_of_hcalls (P : QSharedLeafParent) (hH : QHCallsStmt P)
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    (hw : JQC O 0 w)
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = P.top.d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = P.top.d.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T' : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KT 2),
        (∀ t st, t < T' → SourceInputs P.top.decl (P.top.d.bsIn.take P.nDecl) ids cache
          (fun j => (P.top.extBS i bools bits j).val (T' - 1 - t))
          (fun j n => (P.top.extS i bools bits j n).val (T' - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          P.top.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 2 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
          st0 x < 2 ^ declWidth b x) →
        ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
            (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T'
            ⟨st0, mems, kids⟩ = some envsO ∧
          envsO.length = T' ∧
          ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            P.top.d.shape.layout.outs[k]? = some o → (P.top.src i bools bits)[k]? = some f →
            (envsO[j]'hj) o.name = f j :=
  Tests.Compiler.QShips.qSharedLeaf_ships_of_composed P (hcomposedQ_of_class P hH) O T hA entryL entryW entry hw hcore hpost

#print axioms hcomposedQ_of_class
#print axioms qSharedLeaf_ships_of_hcalls

/-- the frozen C5 statement (QDefTest `FrozenC5`) with `hH` inserted right after `P` -/
def FrozenC5H : Prop := ∀ (P : QSharedLeafParent) (hH : QHCallsStmt P)
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    (hw : JQC O 0 w)
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)),
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = P.top.d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = P.top.d.ss.length ∧
      ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (T' : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KT 2),
        (∀ t st, t < T' → SourceInputs P.top.decl (P.top.d.bsIn.take P.nDecl) ids cache
          (fun j => (P.top.extBS i bools bits j).val (T' - 1 - t))
          (fun j n => (P.top.extS i bools bits j n).val (T' - 1 - t)) (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          P.top.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ResetNk 2 raw D kids →
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
          st0 x < 2 ^ declWidth b x) →
        ∃ envsO, runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b))
            (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T'
            ⟨st0, mems, kids⟩ = some envsO ∧
          envsO.length = T' ∧
          ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            P.top.d.shape.layout.outs[k]? = some o → (P.top.src i bools bits)[k]? = some f →
            (envsO[j]'hj) o.name = f j

example : FrozenC5H := @qSharedLeaf_ships_of_hcalls

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``qSharedLeaf_ships_of_hcalls
  let fzh ← getConstInfo ``FrozenC5H
  let fz ← getConstInfo ``Tests.Compiler.QDef.FrozenC5
  let some fvh := fzh.value? | throwError "QCOMPOSED AUDIT FAILED: no FrozenC5H value"
  let some fv := fz.value? | throwError "QCOMPOSED AUDIT FAILED: no FrozenC5 value"
  unless ← isDefEq ci.type fvh do throwError "QCOMPOSED AUDIT FAILED: type differs from FrozenC5H"
  -- full binder comparison against the REAL frozen statement (QDefTest.FrozenC5), with hH removed (binder 2)
  let frozenNames : List String := ["P", "mctx", "mref", "cctx", "cref", "w", "w1", "O", "T", "hA", "entryL", "entryW", "entry", "hw",
    "b", "raw", "D", "hcore", "hpost"]
  let frozenImplicit : List String := ["mctx", "mref", "cctx", "cref", "w", "w1", "b", "raw", "D"]
  forallTelescope ci.type fun xs concl => do
    unless xs.size == frozenNames.length + 1 do throwError "QCOMPOSED AUDIT FAILED: {xs.size} binders"
    let hHn := (← xs[1]!.fvarId!.getUserName).toString
    unless hHn == "hH" do throwError "QCOMPOSED AUDIT FAILED: binder 2 is {hHn}, not hH"
    unless ← isDefEq (← inferType xs[1]!) (mkApp (mkConst ``QHCallsStmt) xs[0]!) do
      throwError "QCOMPOSED AUDIT FAILED: hH type"
    let xs' := (xs.toList.take 1) ++ (xs.toList.drop 2)
    for (x, nm) in xs'.zip frozenNames do
      let u := (← x.fvarId!.getUserName).toString
      unless u == nm do throwError "QCOMPOSED AUDIT FAILED: binder {u}, frozen {nm}"
      let bi ← x.fvarId!.getBinderInfo
      unless (bi == .implicit) == frozenImplicit.contains nm do throwError "QCOMPOSED AUDIT FAILED: binder {nm} info {repr bi}"
    let mut e := fv
    for x in xs' do
      match e with
      | .forallE _ d b _ =>
        unless ← isDefEq (← inferType x) d do throwError "QCOMPOSED AUDIT FAILED: binder type of {← x.fvarId!.getUserName} differs"
        e := b.instantiate1 x
      | _ => throwError "QCOMPOSED AUDIT FAILED: frozen statement has fewer binders"
    unless ← isDefEq concl e do throwError "QCOMPOSED AUDIT FAILED: conclusion differs from FrozenC5"
  logInfo m!"QCOMPOSED|binders ok: names, binder info, types and conclusion equal FrozenC5 (hH only extra); FrozenC5H defeq"
  for n in [``hcomposedQ_of_class, ``qSharedLeaf_ships_of_hcalls] do
    let axs ← Lean.collectAxioms n
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "QCOMPOSED AUDIT FAILED: {x} in {n}"
    logInfo m!"QCOMPOSED|axioms {n}: {axs}"

/-! closure walk from qSharedLeaf_ships_of_hcalls (bodies of thmInfo / defnInfo) -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : List Name := [``qSharedLeaf_ships_of_hcalls]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "QCOMPOSED CLOSURE FAILED: {n} not found"
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
  logInfo m!"QCOMPOSED|closure reached: {reached.size}"
  let okPfx := ["Tests.Compiler.CDef.", "Tests.Compiler.QDef.", "Tests.Compiler.QCloses.", "Tests.Compiler.QShips.",
    "Tests.Compiler.QComposed.", "Tests.Compiler.C4Kid.", "Tests.Compiler.C4Closes.", "Tests.Compiler.C4HCalls.",
    "Tests.Compiler.C4Ships.", "Tests.Compiler.C4Composed."]
  for c in reached do
    unless okPfx.any (fun p => (c.toString.splitOn p).length > 1) do
      throwError "QCOMPOSED CLOSURE FAILED: reaches {c} (outside QDef/CDef and the generic C5 files)"
    for comp in c.components.map (·.toString) do
      if ["P_M", "P_Q", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "wrapM" || comp.startsWith "P_M" || comp.startsWith "P_Q"
          || comp.startsWith "Tq" || comp.startsWith "TmGrp" || comp.startsWith "TmBnd" || comp.startsWith "TmH" then
        throwError "QCOMPOSED CLOSURE FAILED: reaches {c} (instance component {comp})"
  logInfo m!"QCOMPOSED|closure ok"

end Tests.Compiler.QComposed
