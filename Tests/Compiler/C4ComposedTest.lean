import Tests.Compiler.C4ShipsTest
import Tests.Compiler.C4HCallsTest
import Tools.ShippingSrm28Regs
import Tools.ShippingSrm32Width
-- SCOPE: M-shape class only (AMENDMENT 3 / 4; P_Q is not a member).
-- C4 G-COMPOSED (issue sparkle-gen-c4-gcomposed; worker c4-composed3, kjob/c4-composed3 6b6dfb72, integrated in kjob/c4-int):
-- `hcomposed_of_class : HComposed P` (the generalisation of topshareM_composedNW / _hWd to any P : MemSharedLeafParent) with NO extra
-- hypothesis: it uses the real theorems hcalls_of_classF (G-HCALLS), machineRun_of_class / ranA_of_class (G-RUN / G-RAN).
-- `memSharedLeaf_ships`: the frozen C4 statement (scripts/c3/C4_STATEMENT.lean.txt), audited below against FrozenC4.
set_option autoImplicit false
set_option Elab.async false
namespace Tests.Compiler.C4Composed
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

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- what a served run of a wrapper must establish (`tmPC`, indexed by `P.wrappers`): its `MachineRunNCA` at the parent's design,
with the leaf's `MachineDefines` as boundary -/
def cPC (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) :
    Lean.Name → Sparkle.IR.AST.Module → Prop := fun n mc =>
  ∀ w ∈ P.wrappers, w.decl = n →
    MachineRunNCA O w.decl w.d.shape (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape) mc design

/-- the callee record of a wrapper (the element of `P.cs`, `MemSharedLeafParent.tieCs`) -/
def cNCal (P : MemSharedLeafParent) (w : GenPkg DomainConfig (fun i => i)) : NCal :=
  ⟨w.decl, w.d, P.leaf.d.shape.insts.map (·.1), Sparkle.IR.ModuleName.ofDecl P.leaf.decl :: P.lNames⟩

theorem c_map_getElem? {α β : Type} (f : α → β) {l : List α} {k : Nat} (hk : k < l.length) : (l.map f)[k]? = some (f l[k]) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl

/-! ## the leaf and the wrappers: closes / interface -/

theorem c_leaf_none_false (P : MemSharedLeafParent) {k : Nat} (hk : k < P.leaf.d.shape.insts.length)
    (h : (originAt P.leaf.d.shape k).child? = none) : False := by
  have := P.leafAllMem k hk
  rw [h] at this
  exact absurd this (by decide)

theorem c_leaf_closesA (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx P.leaf.decl P.leaf.d.shape :=
  memCallee_closesA O T hA P.leafMem (fun k hk y hn _ => (c_leaf_none_false P hk hn).elim)

theorem c_leaf_ifaceP (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) {y : Res} (h : RealChildA O P.leaf.decl y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl P.leaf.decl) (Tools.ShippingMachineEntry.machNIn P.leaf.d.shape)
      (P.leaf.d.shape.layout.outs.map (·.name)) P.lNames y.1 y.2 :=
  memCallee_ifaceP O T P.leafMem (fun _ _ _ k hk y hn _ => (c_leaf_none_false P hk hn).elim) entryL h

theorem c_wrap_closesA (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx w.decl w.d.shape :=
  memCallee_closesA O T hA (P.wMem w hw) (fun k hk y _ hre => by
    rw [(P.wKids w hw k hk).1] at hre
    exact c_leaf_ifaceP P O T entryL hre)

/-! ## the wrappers' depth-2 runs and served runs -/

/-- the wrapper's run part of `SeqFactsRN` for a call to it: the depth-2 `SeqChildRunN` of its served run -/
theorem c_callRun (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : GenPkg DomainConfig (fun i => i)) (hw : w ∈ P.wrappers) (design : Sparkle.IR.AST.Design)
    (hcalls : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 w.d design m (dom := fun i : DomainConfig => i) w.lsrc w.extS w.extBS P.nDecl
        (memLeafBsC P.leaf.decl P.leaf.d P.nDecl) (memLeafOutsC P.leaf.decl P.leaf.d)
        (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) (memLeafPC O P.leaf.decl P.leaf.d design))
    {mc : Sparkle.IR.AST.Module}
    (hmc : MachineRunNCA O w.decl w.d.shape (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape) mc design) :
    SeqChildRunN (childMap design.modules) design 2 mc (List.take P.nDecl w.d.bsIn) w.d.shape.layout.outs
      (fun vals => w.src defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take P.nDecl w.d.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take P.nDecl w.d.bsIn) vals)) := by
  letI := w.inh
  exact memLeafCallee_seqChildRunN2 (srcG := P.leaf.src) (srcC := w.src) O T (P.wMem w hw) (P.wOutOk w hw)
    (fun k hk => (P.wKids w hw k hk).1) w.gen entryL
    (fun m c hA => c_leaf_closesA P O T hA) P.leafMem.insts_ne hcalls (P.wHextB w hw) (P.wHext w hw) defaultDomain hmc

/-- a served run of a wrapper is a `MachineRunNCA` (the boundary is the leaf's `MachineDefines`) -/
theorem c_runWrap (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : GenPkg DomainConfig (fun i => i)) (hw : w ∈ P.wrappers)
    (entryW : MachineDefines mctx mref cctx cref w.decl w.d.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design} (hreal : RealChildA O w.decl (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    MachineRunNCA O w.decl w.d.shape (fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape) mc design :=
  machineRunNCA_of_real_main O T (BndA := fun m c _ _ _ => MachineDefines m mref c cref P.leaf.decl P.leaf.d.shape)
    hreal hcons entryW (fun _ _ _ _ _ _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx entryL)
    (fun m c _ _ _ hch _ => by
      obtain ⟨_, _, _, hadm', _⟩ := hch
      exact c_wrap_closesA (mctx := m) (cctx := c) P O T hw hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx entryL))
    (P.wMem w hw).insts_ne

/-! ## the parent's side facts, from `P.pdata` (`MachineData.ok`, `callsOk`) -/

theorem c_callsOk_nIn (d : MachineData) (n : Nat) (h : d.callsOk n = true) : n + d.shape.insts.length = d.nIn := by
  unfold Tools.ShippingMachineAuto.MachineData.callsOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

theorem c_ok_slotLet (d : MachineData) (h : d.ok = true) :
    (∀ b ∈ d.slotBs, b.2 ≠ .domain) ∧ (∀ b ∈ d.letBs, b.2 ≠ .domain) := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨-, -, -, slotKinds, letKinds, -⟩ := h
  exact ⟨slotKinds, letKinds⟩

theorem c_parent_hkD (P : MemSharedLeafParent) : P.nDecl ≤ P.top.d.bsIn.length := by
  have h1 := Tools.ShippingQuadCalls.ok_bsIn_length P.top.d P.pdata.ok
  have h2 := c_callsOk_nIn P.top.d P.nDecl P.pdata.callsOk
  omega

theorem c_parent_hIlen (P : MemSharedLeafParent) : (P.top.d.bsIn.drop P.nDecl).length = P.top.d.shape.insts.length := by
  have h1 := Tools.ShippingQuadCalls.ok_bsIn_length P.top.d P.pdata.ok
  have h2 := c_callsOk_nIn P.top.d P.nDecl P.pdata.callsOk
  simp only [List.length_drop]
  omega

theorem c_parent_hSL (P : MemSharedLeafParent) : ∀ b ∈ P.top.d.slotBs ++ P.top.d.letBs, b.2 ≠ .domain := by
  intro b hb
  obtain ⟨h1, h2⟩ := c_ok_slotLet P.top.d P.pdata.ok
  rcases List.mem_append.mp hb with h | h
  · exact h1 b h
  · exact h2 b h

theorem c_parent_hSlen (P : MemSharedLeafParent) : P.top.d.slotBs.length = P.top.d.shape.layout.slots.length := by
  have h1 := Tools.ShippingQuadCalls.ok_len P.top.d P.pdata.ok
  have h2 := P.pdata.slots
  simp only [MachineData.slotBs, List.length_take, List.length_drop]
  omega

theorem c_parent_hLlen (P : MemSharedLeafParent) : P.top.d.letBs.length = P.top.d.shape.layout.lets :=
  (Tools.ShippingQuadCalls.ok_lets P.top.d P.pdata.ok).symm

theorem c_parent_hNIn (P : MemSharedLeafParent) :
    machNIn P.top.d.shape = ((P.top.d.bsIn.take P.nDecl).filter (fun b => b.2 != .domain)).length := by
  have h1 := Tools.ShippingQuadCalls.ok_len P.top.d P.pdata.ok
  have h2 := Tools.ShippingQuadCalls.ok_lets P.top.d P.pdata.ok
  have h3 : P.top.d.letBs.length = P.top.d.shape.binders.length - (P.top.d.nIn + P.top.d.ss.length) := by
    simp only [MachineData.letBs, List.length_drop]
  have h4 := c_callsOk_nIn P.top.d P.nDecl P.pdata.callsOk
  have h5 := P.pdata.slots
  unfold machNIn
  have h6 : P.top.d.shape.binders.length - P.top.d.shape.insts.length - P.top.d.shape.layout.slots.length
      - P.top.d.shape.layout.lets = P.nDecl := by omega
  rw [h6]
  simp only [MachineData.bsIn, List.take_take]
  have h7 : min P.nDecl P.top.d.nIn = P.nDecl := by omega
  rw [h7]

/-! ## the parent's per-call `SeqFactsRN` at depth 2 -/

/-- the parent's per-call `HCallsOf` at depth 2 (generalises `topshareM_hcallsNW`) -/
theorem c_hcallsNW (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design)
    (hH : ∀ w ∈ P.wrappers, ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 w.d design m (dom := fun i : DomainConfig => i) w.lsrc w.extS w.extBS P.nDecl
        (memLeafBsC P.leaf.decl P.leaf.d P.nDecl) (memLeafOutsC P.leaf.decl P.leaf.d)
        (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) (memLeafPC O P.leaf.decl P.leaf.d design)) :
    HCallsOf 2 P.top.d design m (dom := fun _ : Unit => defaultDomain) P.top.lsrc P.top.extS P.top.extBS P.nDecl
      P.bsC P.outsC P.srcC (cPC P O design) := by
  intro i bools bits k c' hk2
  obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hk2
  have hlt : k < P.top.d.shape.insts.length := by simpa using hlt'
  have hget' : (P.top.d.shape.insts[k]).1 = c' := by simpa using hget
  subst hget'
  right
  unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  obtain ⟨hR, hF⟩ := P.group i bools bits k hlt
  -- the callee of call `k` is wrapper `k / 2` (P.pdata.names, P.tieCs)
  obtain ⟨-, hc'⟩ := Tools.ShippingNmEntry.nm_call_callee P.pdata.names hlt
  have hjc := Tools.ShippingNmEntry.nm_idx_lt P.pdata.names hlt
  have hcl : P.cs.length = P.wrappers.length := by rw [P.tieCs]; simp
  have hjw : k / 2 < P.wrappers.length := hcl ▸ hjc
  have hjA : k / 2 < P.wArity.length := P.wlen ▸ hjw
  have tieCs' : P.cs = P.wrappers.map (cNCal P) := P.tieCs
  have hcw : P.cs[k / 2]? = some (cNCal P P.wrappers[k / 2]) := by
    rw [tieCs', List.getElem?_map, List.getElem?_eq_getElem hjw] <;> rfl
  have hcc : P.cs[k / 2]'hjc = cNCal P P.wrappers[k / 2] := by
    have h1 : P.cs[k / 2]? = some (P.cs[k / 2]'hjc) := List.getElem?_eq_getElem hjc
    rw [hcw] at h1
    exact (Option.some.inj h1).symm
  have hdecl : (P.top.d.shape.insts[k]).1 = P.wrappers[k / 2].decl := by rw [hc', hcc]; rfl
  have hnN : Tools.ShippingNmEntry.nNk P.cs k = machNIn P.wrappers[k / 2].d.shape := by
    unfold Tools.ShippingNmEntry.nNk
    rw [hcw] <;> rfl
  have hwmem : P.wrappers[k / 2] ∈ P.wrappers := List.getElem_mem hjw
  have ha : P.wArity[k / 2] = P.nDecl := P.wArityN _ (List.getElem_mem hjA)
  have hz : (P.wrappers.zip P.wArity)[k / 2]? = some (P.wrappers[k / 2], P.wArity[k / 2]) := by
    rw [List.getElem?_eq_getElem (by simp only [List.length_zip]; omega)]; simp
  have hp : (P.wrappers[k / 2], P.wArity[k / 2]) ∈ P.wrappers.zip P.wArity := List.mem_of_getElem? hz
  have hbs : P.bsC P.wrappers[k / 2].decl = P.wrappers[k / 2].d.bsIn.take P.nDecl := by
    have := P.tieBsC _ hp
    dsimp only at this
    rwa [ha] at this
  have hos : P.outsC P.wrappers[k / 2].decl = P.wrappers[k / 2].d.shape.layout.outs := by
    have := P.tieOutsC _ hp
    exact this
  have hsr : P.srcC () P.wrappers[k / 2].decl = fun vals => P.wrappers[k / 2].src defaultDomain
      (Tools.ShippingMachineChild.boolsOf (P.wrappers[k / 2].d.bsIn.take P.nDecl) vals)
      (Tools.ShippingMachineChild.bitsOf (P.wrappers[k / 2].d.bsIn.take P.nDecl) vals) := by
    have := P.tieSrcC _ hp
    dsimp only at this
    rwa [ha] at this
  refine ⟨Tools.ShippingQuadLeafGeneric.origin_child_none _ (P.pdata.nomemKey k hlt), (P.top.d.shape.insts[k]).2.1,
    c_map_getElem? (fun x => x.2.1) hlt, ?_,
    Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args P.top.d P.nDecl P.pdata.callsOk k hlt)
      (by simp [GenPkg.lsrc, letObsB]), hR, hF⟩
  intro mc hmc
  have hmc' := hmc P.wrappers[k / 2] hwmem hdecl.symm
  have hr := c_callRun P O T entryL P.wrappers[k / 2] hwmem design (hH _ hwmem) hmc'
  rw [hdecl]
  refine ⟨?_, ?_⟩
  · rw [hbs, hos, hsr]; exact hr
  · rw [hr.2.2.2.2.2.1, ← (P.wMem _ hwmem).hNIn, ← P.pdata.argsN k hlt, hnN]

/-! ## the parent's trace -/

/-- the trace of the top (`topshareM_traceXA`): `genTrace` at the top's `MachineRunJQC` (G-RUN) -/
theorem c_traceXA (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hRun : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 P.top.decl P.top.d.shape m design) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingServedRealA.ServedRealA O P.top.decl P.top.d.shape m design) P.top.decl P.top.d m design
      (fun _ : Unit => defaultDomain) P.top.src P.top.extS P.top.extBS P.top.lsrc := by
  letI := P.top.inh
  exact genTrace O T hA P.top.d (fun _ : Unit => defaultDomain) P.top.gen (D₀ := 0) hRun

/-! ## the generic `ComposedNW 2` and `HComposed` -/

/-- **`ComposedNW 2` of the top of any `P : MemSharedLeafParent`** (generalises `topshareM_composedNW`): no run/calls hypothesis;
`hcalls_of_classF` (G-HCALLS) and `machineRun_of_class` (G-RUN) are applied inside. -/
theorem composedNW_of_class (P : MemSharedLeafParent)
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
    (c_traceXA P O T hA (Tests.Compiler.C4Closes.machineRun_of_class P O T hA entryL entryW entry hw hcore))
    P.pdata.fne P.nDecl (c_parent_hkD P)
    (bsIn_drop_nodomain P.top.d P.nDecl P.pdata.domB)
    (c_parent_hIlen P) (c_parent_hSL P) (c_parent_hSlen P) (c_parent_hLlen P) (c_parent_hNIn P)
    P.bsC P.outsC P.srcC (cPC P O design)
    (c_hcallsNW P O T entryL m design (Tests.Compiler.C4HCalls.hcalls_of_classF P O T))
    (fun k c' hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      intro wp hwp hdecl
      subst hdecl
      exact c_runWrap P O T entryL wp hwp (entryW wp hwp) (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons)

/-- `ComposedNWRegs` with the width link (generalises `topshareM_composedNW_hWd`): `composedNWRegs_of_composedNW` + `hWd_of_wired`;
`hierGate` from `core_hierGate_anyAM` + `ranA_of_class`. -/
theorem composedNWRegs_of_class (P : MemSharedLeafParent)
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
      (Tests.Compiler.C4Closes.ranA_of_class P O T hA entryL entryW entry hcore hw)
  exact Tools.ShippingSrm28.composedNWRegs_of_composedNW _
    (composedNW_of_class P O T hA entryL entryW entry hw hcore)
    (fun _ _ _ _ _ _ hW => Tools.ShippingSrm32.hWd_of_wired hpost hgate P.outTy hW)

/-- **G-COMPOSED**: the staged composed binder of the assembly, generically. -/
theorem hcomposed_of_class (P : MemSharedLeafParent) : Tests.Compiler.C4Ships.HComposed P := by
  intro mctx mref cctx cref w w' m design b hcore hpost entry _ hB _
  obtain ⟨O, T, hA, entryL, entryW, hw⟩ := hB
  exact composedNWRegs_of_class P O T hA entryL entryW entry hw hcore hpost

/-- **C4**: the frozen statement (scripts/c3/C4_STATEMENT.lean.txt), with no staged hypothesis. -/
theorem memSharedLeaf_ships (P : MemSharedLeafParent)
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
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
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
        (∀ x ∈ (openIns b).map (·.name),
          x ∉ bodyInstOuts (childMap D.modules) b.body →
          st0 x < 2 ^ declWidth b x) →
        ∃ envsO, runModuleTG (KSn (childMap D.modules) 2)
            (declWidth (checkedOptimize b))
            (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T'
            ⟨st0, mems, kids⟩ = some envsO ∧
          envsO.length = T' ∧
          ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            P.top.d.shape.layout.outs[k]? = some o → (P.top.src i bools bits)[k]? = some f →
            (envsO[j]'hj) o.name = f j :=
  Tests.Compiler.C4Ships.memSharedLeaf_ships_of_composed P (hcomposed_of_class P) O T hA entryL entryW entry hw hcore hpost

/-- the topshareM instance recovered from the generic theorem -/
theorem topshareM_ships (hgrp : Tests.Compiler.Srm9ComposedTest.TmGrp) : type_of% (@memSharedLeaf_ships (P_M hgrp)) := @memSharedLeaf_ships (P_M hgrp)

#print axioms hcomposed_of_class
#print axioms memSharedLeaf_ships
#print axioms topshareM_ships

def FrozenC4 : Prop := ∀ (P : MemSharedLeafParent)

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

example : FrozenC4 := @memSharedLeaf_ships

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``memSharedLeaf_ships
  let fz ← getConstInfo ``FrozenC4
  let some fv := fz.value? | throwError "C4COMPOSED AUDIT FAILED: no frozen value"
  unless ← isDefEq ci.type fv do throwError "C4COMPOSED AUDIT FAILED: type differs from the frozen statement"
  let names ← forallTelescope ci.type fun xs _ => xs.mapM fun x => do
    return s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
  let names2 ← forallTelescope fv fun xs _ => xs.mapM fun x => do
    return s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
  let n1 := names.size; let n2 := names2.size
  logInfo m!"C4COMPOSED|binders: {names}"
  -- the FULL binder arrays (names and binder infos) must agree, with the same count
  unless n1 == n2 do throwError "C4COMPOSED AUDIT FAILED: {n1} binders vs {n2} in the frozen statement"
  unless names == names2 do throwError "C4COMPOSED AUDIT FAILED: binder lists differ"
  -- and equal the frozen binder list of scripts/c3/C4_STATEMENT.lean.txt
  -- ("P; implicit mctx mref cctx cref w w1; O T hA entryL entryW entry hw; implicit b raw D; hcore hpost")
  let frozenNames : List String := ["P", "mctx", "mref", "cctx", "cref", "w", "w1", "O", "T", "hA", "entryL", "entryW", "entry", "hw",
    "b", "raw", "D", "hcore", "hpost"]
  let frozenImplicit : List String := ["mctx", "mref", "cctx", "cref", "w", "w1", "b", "raw", "D"]
  unless n1 == frozenNames.length do throwError "C4COMPOSED AUDIT FAILED: {n1} binders, frozen list has {frozenNames.length}"
  forallTelescope ci.type fun xs _ => do
    for (x, nm) in xs.toList.zip frozenNames do
      let u := (← x.fvarId!.getUserName).toString
      unless u == nm do throwError "C4COMPOSED AUDIT FAILED: binder {u}, frozen {nm}"
      let bi ← x.fvarId!.getBinderInfo
      unless (bi == .implicit) == frozenImplicit.contains nm do throwError "C4COMPOSED AUDIT FAILED: binder {nm} info {repr bi}"
    -- and the binder TYPES agree pairwise with the frozen statement's
    forallTelescope fv fun ys _ => do
      for (x, y) in xs.toList.zip ys.toList do
        unless ← isDefEq (← inferType x) (← inferType y) do throwError "C4COMPOSED AUDIT FAILED: binder type of {← x.fvarId!.getUserName} differs"
  logInfo m!"C4COMPOSED|binders ok: all {n1} binders equal the frozen list (names, binder info, types)"
  for n in [``hcomposed_of_class, ``memSharedLeaf_ships, ``topshareM_ships] do
    let axs ← Lean.collectAxioms n
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "C4COMPOSED AUDIT FAILED: {x} in {n}"
    logInfo m!"C4COMPOSED|axioms {n}: {axs}"

/-! closure walk from memSharedLeaf_ships -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : List Name := [``memSharedLeaf_ships]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "C4COMPOSED CLOSURE FAILED: {n} not found"
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
  logInfo m!"C4COMPOSED|closure reached: {reached.size}"
  let okPfx := ["Tests.Compiler.CDef.", "Tests.Compiler.C4Kid.", "Tests.Compiler.C4Closes.", "Tests.Compiler.C4HCalls.",
    "Tests.Compiler.C4Ships.", "Tests.Compiler.C4Composed."]
  for c in reached do
    unless okPfx.any (fun p => (c.toString.splitOn p).length > 1) do
      throwError "C4COMPOSED CLOSURE FAILED: reaches {c} (outside CDef and the generic C4 files)"
    for comp in c.components.map (·.toString) do
      if ["P_M", "P_Q", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "wrapM" || comp.startsWith "P_M"
          || comp.startsWith "TmGrp" || comp.startsWith "TmBnd" || comp.startsWith "TmH" then
        throwError "C4COMPOSED CLOSURE FAILED: reaches {c} (instance component {comp})"
  logInfo m!"C4COMPOSED|closure ok"

end Tests.Compiler.C4Composed
