import Tools.ShippingGen2Data
import Tools.ShippingGen2MemData
import Tools.ShippingGen2DataBridge
import Tools.ShippingSrm4Core5
import Tools.ShippingGen5NameKids3
import Tools.ShippingCacheCoherentRun
import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingSrm12Corr
import Tools.ShippingGen5AuditUA1
set_option autoImplicit false
-- NOT BUILT (no build run yet).
-- U-A4/U-A5 of B-AUD: E-3 (AuditE3) and the B3 part of AuditE4_B3B4 from T1Hyp + existing rows (T1L-12, T1L-04) + the new row hLeafAlias
-- (scripts/gen5/AUD_UA4_FREEZE.md §1, approved e917945e). Bodies are the scratch of AUD_UA4_STUDY2 / STUDY3 / STUDY4.
-- Two origin-only copies (core_kids_facts_ranAO, deepChild_ifaceAO) of ShippingParentTailsA / ShippingSeqChildDeepConsumerA: binder `hnomem` -> `hnomemO`
-- (origin half only) and the one use `nomem_tag` -> `notag_at`; proofs otherwise verbatim. No noMemName premise.
-- Premise delta: T1 +1 (hLeafAlias). No statement or definition of an existing file is changed.
-- No sorry / axiom / native_decide.

variable {tenv : Lean.Environment}

namespace Tools.ShippingGen5AuditE3B3

section CopyTails
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChecksCore Tools.ShippingLinkedFresh Tools.ShippingClosedTyped
open Tools.ShippingHierOpen (linkedWF bodyInstOuts stmtInstOuts linkedWrites instOutWires)
open Tools.ShippingParentRanA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_kids_facts_ranA O` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_kids_facts_ranA O` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_kids_facts_ranAO (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ b.body = M.body ∧ b.outputs = M.outputs ∧
    (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
    (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingChildCacheA.RealChildA O (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      ∀ g2 ∈ y.1 :: y.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran0
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
  have ok' := ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok'
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, hcall1, hinst1, -, houtsM, -, -, -, hGinst, hGcall, -, -, hcleanAny, -⟩ :=
    wired
  obtain ⟨hzb, -, hzi, hzo⟩ := hcleanAny outTy
  -- an instance statement of the module names a module of its design
  have hinstD : ∀ mn i conns, Stmt.inst mn i conns ∈ M.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ mc ∈ D.modules ∧ mc.name = mn := by
    intro mn i conns hm
    by_cases hf : d.shape.instFields = []
    · obtain ⟨k, args, mc, -, hfind, -⟩ := hinst1 hf mn i conns hm
      have hfind' := hfind
      unfold moduleByName at hfind'
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind', by simpa using List.find?_some hfind'⟩
    · obtain ⟨args, outs, mc, hcs, hfind, -⟩ := hGinst hf _ hm rfl
      obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      cases he
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind, rfl⟩
  have hhas : Tools.ShippingMachineShipsHier.hasInst M := by
    have hk0 : 0 < d.shape.insts.length := List.length_pos_iff.mpr hins
    by_cases hf : d.shape.instFields = []
    · obtain ⟨args, mc, st, -, hst, -, hcs⟩ := hcall1 hf 0 hk0
      obtain ⟨_, _, _, iname, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
    · obtain ⟨st, hst, args, outs, mc, hcs, -⟩ := hGcall hf 0 hk0
      obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
  have hbeq : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M := by
    rcases hpost with h | h
    · exact h
    · rw [h]
      refine Tools.ShippingMachineDepthRun.mergeChecked_of_hasInst ?_
      obtain ⟨mn, i, conns, hm⟩ := hhas
      exact ⟨mn, i, conns, by rw [hzb]; exact hm⟩
  have hbody' : b.body = M.body := by rw [hbeq, hzb]
  have hbout : b.outputs = M.outputs := by rw [hbeq, hzo]
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  -- the design: the join of the children
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hnames := Tools.ShippingChecksDepth.visited_name (children := children) hd0
  -- the closed machine assigns its outputs, and so does the module
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hMA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    refine Tools.ShippingChecksDerived2.outsAssigned_of_assigned fun p hp => ?_
    have hp2 : p ∈ (closeMachine d.shape.layout t').outputs := by
      rw [closeMachine_outputs hpw']
      rw [houtsM] at hp
      exact hp
    obtain ⟨r, hr⟩ := Tools.ShippingChecksDerived3.closeMachine_outs_assigned hpw' p hp2
    exact ⟨r, hperm.subset (List.mem_append_left _ hr)⟩
  refine ⟨hMname.trans hname0, hbody', hbout,
    fun mn i conns hm => (hinstD mn i conns hm).imp fun _ h => h.1, ?_,
    Tools.ShippingChecksDerived3.outsAssigned_congr hbody' hbout hMA⟩
  intro g hg
  rw [hDeq] at hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  have hk' : k < d.shape.insts.length := by
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨y', hy', hor'⟩ := hall k hk'
  rw [hk] at hy'
  cases hy'
  rcases hor' with hmem | hre
  · rw [Tools.ShippingChildInv.notag_at hnomemO hk'] at hmem
    cases hmem
  · refine ⟨k, hk', y, hre, hor, fun g2 hg2 => ?_⟩
    rw [hDeq]
    refine hnames g2 (mem_visited.mpr ⟨y, hy, ?_⟩)
    rcases List.mem_cons.mp hg2 with h | h
    · exact Or.inl h
    · exact Or.inr h
end CopyTails

section CopyConsumer
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingKidsChildIface

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`deepChild_ifaceA` with `closes` asked in `AdmCtx` contexts only.** -/
theorem deepChild_ifaceAO (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (w w1 : Void IO.RealWorld)
      (M : Sparkle.IR.AST.Module) (D : Design),
      AdmCtx O.quiet mctx' cctx' ∧ JQ O.quiet (dv w) w ∧ CacheInvA O (cv w) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules ∧
      M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ y.1.body = M.body ∧ y.1.outputs = M.outputs ∧
      (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
      (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
        RealChildA O (d.shape.insts[k]).1 y' ∧ (g = y'.1 ∨ g ∈ y'.2.modules) ∧
        ∀ g2 ∈ y'.1 :: y'.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
    have hw : JQ O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have hc : CacheInvA O (cv w) := fun c r h => cache c r h
    have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
      (closes mctx' cctx' adm) hw (Or.inr hc)
    obtain ⟨hMn, hb, ho, hinst, hreal, hassign⟩ :=
      core_kids_facts_ranAO O d ok hbody hC hslots hdomB hins outTy hnomemO hpost ran
    refine ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, hdesL ?_, hMn, hb, ho, hinst,
      hreal, hassign⟩
    intro x hx e
    obtain ⟨k, hk, y', hre, hor, -⟩ := hreal x hx
    refine hsep k hk y' hre x ?_ (e.trans hMn)
    rcases hor with heq | hin
    · rw [heq]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hin
end CopyConsumer

open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass kidModName)
open Tools.ShippingSrm15Graph (graphOf FirstOcc)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans OrdPath OrdEdge ReachClosed)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.ModuleName (ofDecl)
open Tools.ShippingGen5AuditCarrier (SOf)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingSrm7Rank
open Tools.ShippingGen5NameKids3
open Tools.ShippingSrm12Corr

def StrictDesc (g : CallGraph) (a b : Name) : Prop := ∃ x, OrdEdge g a x ∧ OrdPath g x b

theorem strictDesc_irrefl {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach)
    {c : Name} (hc : Reach c) : ¬ StrictDesc g c c := by
  rintro ⟨x, he, hp⟩
  obtain ⟨r0, h0, -, -⟩ := Tools.ShippingSrm7Rank.inClass_rank hin
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  obtain ⟨r1, h1, hlt⟩ := rank_of_ordEdge hr he
  obtain ⟨r2, h2, hle⟩ := rank_of_reach h1 hp
  rw [hr] at h2
  have := Option.some.inj h2
  omega

theorem ordPath_cons {g : CallGraph} {x y b : Name} (he : OrdEdge g x y) (hp : OrdPath g y b) :
    OrdPath g x b := by
  induction hp with
  | refl => exact OrdPath.step OrdPath.refl he
  | step _ e ih => exact OrdPath.step ih e

theorem strictDesc_of_edge_left {g : CallGraph} {a x b : Name} (h1 : OrdEdge g a x) (h2 : StrictDesc g x b) :
    StrictDesc g a b := by
  obtain ⟨y, he, hp⟩ := h2
  exact ⟨x, h1, ordPath_cons he hp⟩

theorem strictDesc_of_edge {g : CallGraph} {a x : Name} (h1 : OrdEdge g a x) : StrictDesc g a x :=
  ⟨x, h1, OrdPath.refl⟩

theorem ordEdge_of_idx {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hg : GraphAgrees g Reach S) {c : Name} (hc : Reach c) {sp : MachineShape} (hS : S c = some sp)
    {k : Nat} (hk : k < sp.insts.length) (hch : (originAt sp k).child? = none) :
    OrdEdge g c (sp.insts[k]'hk).1 := by
  refine ⟨sp.instTagged, originAt sp k, ?_, Tools.ShippingSrm12Corr.instTagged_mem_idx sp hk, ?_⟩
  · rw [hg c hc, hS]; rfl
  · cases ho : originAt sp k with
    | ord => rfl
    | field i => rfl
    | mem cb aw dw => rw [ho] at hch; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at hch

theorem moduleByName_spec {ms : List Sparkle.IR.AST.Module} {mn : String} {mc : Sparkle.IR.AST.Module}
    (h : Sparkle.IR.Machine.moduleByName ms mn = some mc) : mc ∈ ms ∧ mc.name = mn := by
  unfold Sparkle.IR.Machine.moduleByName at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

section Q
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingCacheCoherentRun (IsMem)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the name fact (UA7C `DescProv`, §4) -/
def DescProvY (g : CallGraph) (c : Name) (y : Res) : Prop :=
  ∀ a ∈ y.2.modules, IsMem a ∨ ∃ c', StrictDesc g c c' ∧ a.name = ofDecl c'

/-- instantiation targets of the result's modules are names of the result's design -/
def OutClosedY (y : Res) : Prop :=
  ∀ a ∈ y.1 :: y.2.modules, ∀ mn i cs, Stmt.inst mn i cs ∈ a.body → ∃ g' ∈ y.2.modules, g'.name = mn

def QY (g : CallGraph) (c : Name) (y : Res) : Prop :=
  y.1.name = ofDecl c ∧ DescProvY g c y ∧ OutClosedY y

/-- a kid result, seen from its parent `c` -/
def KidOK (g : CallGraph) (c : Name) (y : Res) : Prop :=
  (∀ a ∈ y.1 :: y.2.modules, IsMem a ∨ ∃ c', StrictDesc g c c' ∧ a.name = ofDecl c') ∧ OutClosedY y

theorem kidOK_hsep {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) {c : Name} (hc : Reach c)
    {y : Res} (h : KidOK g c y) : ∀ a ∈ y.1 :: y.2.modules, a.name ≠ ofDecl c := by
  intro a ha e
  rcases h.1 a ha with ⟨cb, aw, dw, ea⟩ | ⟨c', hd, hn⟩
  · rw [ea, Tools.ShippingCacheCoherentRun.memModule_name] at e
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw e.symm
  · rw [hn] at e
    have := Tools.ShippingModuleName.ofDecl_injective e
    subst this
    exact strictDesc_irrefl hin hsp hc hd

theorem memModule_kidOK (g : CallGraph) (c : Name) (cb : Bool) (aw dw : Nat) :
    KidOK g c (Sparkle.Compiler.MachMemory.memModule cb aw dw) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    left
    simp [Sparkle.Compiler.MachMemory.memModule] at ha
    rcases ha with rfl | rfl <;> exact ⟨cb, aw, dw, rfl⟩
  · intro a ha mn i cs hm
    simp [Sparkle.Compiler.MachMemory.memModule] at ha
    rcases ha with rfl | rfl <;> simp [Sparkle.Compiler.MachMemory.memModule] at hm

end Q

section Cor
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildInv (Res)
open Tools.ShippingCacheCoherentRun (IsMem)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- AuditE3 (E-3 / B7) from the induction, with `Q` as a named hypothesis. -/
theorem auditE3_of_q {O : RefLawsAOps MkRefd mref cref} {g : CallGraph} {Reach : Name → Prop}
    {S : Name → Option MachineShape} (hcl : ReachClosed Reach S)
    (Q : ∀ c, Reach c → ∀ y, RealChildA O c y → QY g c y) :
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      (originAt sp k).child? = none → ∀ y : Res, RealChildA O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1 := by
  intro c hc sp hS k hk hch y hy
  exact (Q _ (hcl c hc sp hS k hk (by simpa using hch)) y hy).1

/-- B3 for an ordinary kid: with `ns := names of the kid's top and design`, the design-name field,
the inst-target field of `ChildIfaceP`, and `ofDecl c ∉ ns` all follow from `QY` of the kid. -/
theorem b3_of_q {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) {c c' : Name} (hc : Reach c)
    (he : OrdEdge g c c') {y : Res} (hq : QY g c' y) :
    let ns := (y.1 :: y.2.modules).map (·.name)
    (∀ a ∈ y.2.modules, a.name ∈ ns) ∧
    (∀ a ∈ y.1 :: y.2.modules, ∀ mn i cs, Stmt.inst mn i cs ∈ a.body → mn ∈ ns) ∧
    ofDecl c ∉ ns := by
  intro ns
  refine ⟨fun a ha => List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, rfl⟩, ?_, ?_⟩
  · intro a ha mn i cs hm
    obtain ⟨g', hg', rfl⟩ := hq.2.2 a ha mn i cs hm
    exact List.mem_map.mpr ⟨g', List.mem_cons_of_mem _ hg', rfl⟩
  · intro hmem
    obtain ⟨a, ha, e⟩ := List.mem_map.mp hmem
    have K : KidOK g c y := by
      refine ⟨?_, hq.2.2⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr ⟨c', strictDesc_of_edge he, hq.1⟩
      · rcases hq.2.1 a ha with hm | ⟨c'', hs, hnm⟩
        · exact Or.inl hm
        · exact Or.inr ⟨c'', strictDesc_of_edge_left he hs, hnm⟩
    exact kidOK_hsep hin hsp hc K a ha e
end Cor


/-! ## STUDY3 -/
section S3
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- (2) direction: MachineCloses ⇒ MachineClosesAtA (any O, any context). -/
theorem closesAtA_of_closes (O : RefLawsAOps MkRefd mref cref) (mctx : Lean.Meta.Context)
    (cctx : Lean.Core.Context) (c : Name) (sh : MachineShape)
    (h : MachineCloses mctx mref cctx cref c sh) : MachineClosesAtA O mctx cctx c sh := by
  intro tenv b n w r w' _ _ hr
  exact h (Tools.ShippingChildInv.profLogIO b) w r w' hr
#print axioms closesAtA_of_closes

/-- leaf `MachineCloses` from `letsAliasOk` (existing `closes_of_data`), every context. -/
theorem leafCloses_of_data (c : Name) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = []) (hal : d.letsAliasOk = true)
    (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) :
    MachineCloses mctx mref cctx cref c d.shape :=
  Tools.ShippingMachineClosesData.closes_of_data d ok hbody
    (by simp [MachineData.letsOk, hno, hal]) mctx mref cctx cref
#print axioms leafCloses_of_data

/-- leaf `MachineCloses` from `lets = 0` (existing `machineCloses_of_noLets`). -/
theorem leafCloses_of_noLets (c : Name) (sh : MachineShape) (h : sh.layout.lets = 0) (hi : sh.insts = [])
    (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) :
    MachineCloses mctx mref cctx cref c sh :=
  Tools.ShippingMachineEntry.machineCloses_of_noLets h hi
end S3
section Q
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingCacheCoherentRun (IsMem)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
def MachPrem3 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (c : Name) (sp : MachineShape) : Prop :=
  ∃ d : MachineData, d.shape = sp ∧ d.ok = true ∧
    d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) ∧
    MachineDefines mctx mref cctx cref c d.shape ∧
    ((d.shape.insts = [] ∧ ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
        MachineCloses mctx' mref cctx' cref c d.shape) ∨
     (∃ nDecl : Nat, d.callsOk nDecl = true ∧ d.ss.length = d.shape.layout.slots.length ∧
        (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧ d.shape.insts ≠ [] ∧ d.shape.instFields ≠ [] ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape) ∨
     (∃ nDecl : Nat, d.callsOk nDecl = true ∧ d.ss.length = d.shape.layout.slots.length ∧
        (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧ d.shape.insts ≠ [] ∧
        (∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true) ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape))

set_option maxHeartbeats 4000000 in
theorem q_induct3 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach S)
    (hS : ∀ c, Reach c → ∃ sp, S c = some sp)
    (hprem : ∀ c, Reach c → ∀ sp, S c = some sp → MachPrem3 (mctx := mctx) (cctx := cctx) O c sp)
    (hcl : ReachClosed Reach S) :
    ∀ c, Reach c → ∀ y, RealChildA O c y → QY g c y := by
  obtain ⟨r0, h0, -, -⟩ := Tools.ShippingSrm7Rank.inClass_rank hin
  have key : ∀ r c, Reach c → declRank g B c = some r → ∀ y, RealChildA O c y → QY g c y := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro c hc hr y hy
      obtain ⟨sp, hSc⟩ := hS c hc
      -- kids
      have kids : ∀ (k : Nat) (hk : k < sp.insts.length) (y' : Res),
          Tools.ShippingCallsMemA.KidTA O (originAt sp k) (sp.insts[k]'hk).1 y' → KidOK g c y' := by
        intro k hk y' hkid
        rcases hkid with h1 | ⟨hch, hrc⟩
        · obtain ⟨cb, aw, dw, hmo⟩ : ∃ cb aw dw, originAt sp k = .mem cb aw dw := by
            cases ho : originAt sp k with
            | ord => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
            | field i => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
            | mem cb aw dw => exact ⟨cb, aw, dw, rfl⟩
          rw [hmo] at h1
          simp only [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?, Option.some.injEq] at h1
          subst h1
          exact memModule_kidOK g c cb aw dw
        · have he := ordEdge_of_idx hg hc hSc hk hch
          obtain ⟨r1, h1, hlt⟩ := rank_of_ordEdge hr he
          have hc' : Reach (sp.insts[k]'hk).1 := hcl c hc sp hSc k hk (by simpa using hch)
          obtain ⟨hn, hd, ho⟩ := ih r1 hlt _ hc' h1 y' hrc
          refine ⟨?_, ho⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inr ⟨_, strictDesc_of_edge he, hn⟩
          · rcases hd a ha with hm | ⟨c'', hs, hnm⟩
            · exact Or.inl hm
            · exact Or.inr ⟨c'', strictDesc_of_edge_left he hs, hnm⟩
      obtain ⟨d, hdS, ok, hbody, outTy, entry, hcase⟩ := hprem c hc sp hSc
      subst hdS
      rcases hcase with ⟨hno, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hfne, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hnomemO, closes⟩
      · have I := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O d ok hbody hno outTy entry closes hy
        refine ⟨I.name, ?_, ?_⟩
        · intro a ha; rw [I.design] at ha; simp at ha
        · intro a ha mn i cs hm
          rw [I.design] at ha
          have : a = y.1 := by simpa using ha
          subst this
          have := List.all_eq_true.mp I.seqOk _ hm
          simp [Sparkle.IR.OptCheck.seqStmtOk] at this
      · have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            Tools.ShippingCallsMemA.KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hkid => kidOK_hsep hin hsp hc (kids k hk y' hkid)
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          Tools.ShippingSrm4Core5.deepChild_ifaceA'M O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes hy
        have hname : y.1.name = ofDecl c := by
          rcases hpost with e | e
          · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
          · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
        refine ⟨hname, ?_, ?_⟩
        · intro a ha
          rw [hdes] at ha
          obtain ⟨k, hk, y', hkid, hor, -⟩ := hreal a ha
          have K := kids k hk y' hkid
          refine K.1 a ?_
          rcases hor with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h
        · intro a ha mn i cs hm
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hb] at hm
            obtain ⟨mc, hmc⟩ := hinst mn i cs hm
            obtain ⟨hmem, hnm⟩ := moduleByName_spec hmc
            exact ⟨mc, by rw [hdes]; exact hmem, hnm⟩
          · rw [hdes] at ha
            obtain ⟨k, hk, y', hkid, hor, hcov⟩ := hreal a ha
            have K := kids k hk y' hkid
            have ha' : a ∈ y'.1 :: y'.2.modules := by
              rcases hor with rfl | h
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ h
            obtain ⟨g2, hg2, hn2⟩ := K.2 a ha' mn i cs hm
            obtain ⟨g', hg', hn'⟩ := hcov g2 (List.mem_cons_of_mem _ hg2)
            exact ⟨g', by rw [hdes]; exact hg', hn'.trans hn2⟩
      · have hch : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none := by
          intro k hk
          exact Tools.ShippingChildInv.notag_at hnomemO hk
        have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            RealChildA O (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hrc => kidOK_hsep hin hsp hc (kids k hk y' (Or.inr ⟨hch k hk, hrc⟩))
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          deepChild_ifaceAO O T d ok hbody hC hslots hdomB hins outTy hnomemO hsep entry closes hy
        have hname : y.1.name = ofDecl c := by
          rcases hpost with e | e
          · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
          · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
        refine ⟨hname, ?_, ?_⟩
        · intro a ha
          rw [hdes] at ha
          obtain ⟨k, hk, y', hrc, hor, -⟩ := hreal a ha
          have K := kids k hk y' (Or.inr ⟨hch k hk, hrc⟩)
          refine K.1 a ?_
          rcases hor with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h
        · intro a ha mn i cs hm
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hb] at hm
            obtain ⟨mc, hmc⟩ := hinst mn i cs hm
            obtain ⟨hmem, hnm⟩ := moduleByName_spec hmc
            exact ⟨mc, by rw [hdes]; exact hmem, hnm⟩
          · rw [hdes] at ha
            obtain ⟨k, hk, y', hrc, hor, hcov⟩ := hreal a ha
            have K := kids k hk y' (Or.inr ⟨hch k hk, hrc⟩)
            have ha' : a ∈ y'.1 :: y'.2.modules := by
              rcases hor with rfl | h
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ h
            obtain ⟨g2, hg2, hn2⟩ := K.2 a ha' mn i cs hm
            obtain ⟨g', hg', hn'⟩ := hcov g2 (List.mem_cons_of_mem _ hg2)
            exact ⟨g', by rw [hdes]; exact hg', hn'.trans hn2⟩
  intro c hc y hy
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  exact key r c hc hr y hy

#print axioms q_induct3
end Q

section S6
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- Named residual facts about `DataOk` (NOT derived), second version with the one-output branch. -/
structure DataRes3 (DataOk : Pkg ι dom → Prop) : Prop where
  callsRows : ∀ q, DataOk q → q.d.shape.insts ≠ [] →
    q.d.callsOk q.kD = true ∧ q.d.ss.length = q.d.shape.layout.slots.length ∧
      (∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain)
  outTy : ∀ q, DataOk q → ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width
  leafAlias : ∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true
  /-- the one-output row (origin half), `OneOutNoMemRow` (Tools/ShippingGen2DataBridge.lean) -/
  noMemRow : ∀ q, DataOk q →
    (!q.d.shape.instFields.isEmpty || q.d.shape.instTagged.all (fun x => x.2.child?.isNone)) = true

theorem machPrem3_of_t1hyp {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes3 DataOk) (hA : AdmCtx L.O.quiet mctx cctx) :
    ∀ c, Reach c → ∀ sp, SOf P c = some sp → MachPrem3 (mctx := mctx) (cctx := cctx) L.O c sp := by
  intro c hc sp hS
  obtain ⟨q, hq, hdecl, hdo⟩ := H.pkg c hc
  subst hdecl
  simp only [SOf, hq, Option.map_some, Option.some.injEq] at hS
  subst hS
  refine ⟨q.d, rfl, q.ok, q.body_eq, R.outTy q hdo, ?_, ?_⟩
  · exact H.defines _ hc q hq mctx cctx hA
  · by_cases hno : q.d.shape.insts = []
    · refine Or.inl ⟨hno, fun mctx' cctx' => ?_⟩
      exact leafCloses_of_data _ q.d q.ok q.body_eq hno (R.leafAlias q hdo hno) mctx' cctx'
    · obtain ⟨hC, hsl, hdom⟩ := R.callsRows q hdo hno
      have hcl : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx L.O.quiet mctx' cctx' →
          MachineClosesAtA (mref := mref) (cref := cref) L.O mctx' cctx' q.decl q.d.shape :=
        fun mctx' cctx' hA' => H.closes _ hc q hq mctx' cctx' hA'
      by_cases hf : q.d.shape.instFields = []
      · refine Or.inr (Or.inr ⟨q.kD, hC, hsl, hdom, hno, ?_, hcl⟩)
        have hrow := R.noMemRow q hdo
        rw [hf] at hrow
        have hall : q.d.shape.instTagged.all (fun x => x.2.child?.isNone) = true := by
          simpa using hrow
        intro x hx
        exact List.all_eq_true.mp hall x hx
      · exact Or.inr (Or.inl ⟨q.kD, hC, hsl, hdom, hno, hf, hcl⟩)
#print axioms machPrem3_of_t1hyp

/-- E-3 (B7) for the real run, from `T1Hyp` + the named residuals + the carriers (`hin`, `hsp`, `hg`). -/
theorem auditE3_of_t1hyp3 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes3 DataOk) (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)) :
    ∀ c, Reach c → ∀ sp, SOf P c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      (originAt sp k).child? = none → ∀ y : Tools.ShippingChildInv.Res, RealChildA L.O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1 := by
  have hS : ∀ c, Reach c → ∃ sp, SOf P c = some sp := by
    intro c hc
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    exact ⟨q.d.shape, by simp [SOf, hq]⟩
  have hcl : ReachClosed Reach (SOf P) := by
    intro c hc sp hSc k hk hch
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    simp only [SOf, hq, Option.map_some, Option.some.injEq] at hSc
    subst hSc
    exact H.closed c hc q hq k hk hch
  exact auditE3_of_q hcl (q_induct3 L.O L.T hin hsp hg hS (machPrem3_of_t1hyp H R hA) hcl)
#print axioms auditE3_of_t1hyp3
end S6

/-- D.E-3 (AUDIT_CARRIER_FREEZE §2, text copied) -/
def AuditE3 {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) (L : Laws mref cref) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length), (originAt sp k).child? = none →
      ∀ y : Tools.ShippingChildInv.Res,
        Tools.ShippingChildCacheA.RealChildA L.O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1

section ConcRowsS
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
structure ConcRows (DataOk : Pkg ι dom → Prop) : Prop where
  hMemRow : ∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q
  hrow : ∀ q, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  leafAlias : ∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true

theorem dataRes3_of_rows {DataOk : Pkg ι dom → Prop} (C : ConcRows DataOk) : DataRes3 DataOk where
  callsRows := fun q hq _ => by
    obtain ⟨-, hc, hs, -, hd⟩ := MemParentDataOk.rows (C.hMemRow q hq).1
    exact ⟨hc, hs, hd⟩
  outTy := fun q hq => by
    obtain ⟨-, -, -, ho, -⟩ := MemParentDataOk.rows (C.hMemRow q hq).1
    exact ho
  leafAlias := C.leafAlias
  noMemRow := C.hrow
#print axioms dataRes3_of_rows
end ConcRowsS

section Final
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
open Tools.ShippingCacheCoherentRun (IsMem)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- every kid result (memory or ordinary) is `KidOK`, from the induction result `Q` -/
theorem kidOK_of_kidTA {O : RefLawsAOps MkRefd mref cref} {g : CallGraph} {Reach : Name → Prop}
    {S : Name → Option MachineShape} (hg : GraphAgrees g Reach S) (hcl : ReachClosed Reach S)
    (Q : ∀ c, Reach c → ∀ y, RealChildA O c y → QY g c y)
    {c : Name} (hc : Reach c) {sp : MachineShape} (hSc : S c = some sp)
    {k : Nat} (hk : k < sp.insts.length) {y : Res}
    (hkid : Tools.ShippingCallsMemA.KidTA O (originAt sp k) (sp.insts[k]'hk).1 y) : KidOK g c y := by
  rcases hkid with h1 | ⟨hch, hrc⟩
  · obtain ⟨cb, aw, dw, hmo⟩ : ∃ cb aw dw, originAt sp k = .mem cb aw dw := by
      cases ho : originAt sp k with
      | ord => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
      | field i => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
      | mem cb aw dw => exact ⟨cb, aw, dw, rfl⟩
    rw [hmo] at h1
    simp only [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?, Option.some.injEq] at h1
    subst h1
    exact memModule_kidOK g c cb aw dw
  · have he := ordEdge_of_idx hg hc hSc hk hch
    have hc' : Reach (sp.insts[k]'hk).1 := hcl c hc sp hSc k hk (by simpa using hch)
    have hq := Q _ hc' y hrc
    refine ⟨?_, hq.2.2⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inr ⟨_, strictDesc_of_edge he, hq.1⟩
    · rcases hq.2.1 a ha with hm | ⟨c'', hs, hnm⟩
      · exact Or.inl hm
      · exact Or.inr ⟨c'', strictDesc_of_edge_left he hs, hnm⟩

/-- The B3 part of `AuditE4_B3B4` (AUDIT_CARRIER_FREEZE §2), with `namesK k` taken to be the names of the kid's top
and design: design names are in `ns`, instantiation targets of the kid's top and design are in `ns`, and the parent's
`ofDecl c` is not in `ns`. The other fields of `ChildIfaceP` and the B4 conjunct are not part of this statement. -/
def AuditB3 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA L.O (originAt sp k) (sp.insts[k]'hk).1 y →
      let ns := (y.1 :: y.2.modules).map (·.name)
      (∀ a ∈ y.2.modules, a.name ∈ ns) ∧
      (∀ a ∈ y.1 :: y.2.modules, ∀ mn i cs, Stmt.inst mn i cs ∈ a.body → mn ∈ ns) ∧
      ofDecl c ∉ ns

/-- E-3 and the B3 part from `T1Hyp`, the existing rows T1L-12 (`hMemRow`) and T1L-04 (`hrow`), the new row
`hLeafAlias` (AUD_UA4_FREEZE §1), `AdmCtx`, and the E-5 carriers. -/
theorem auditE3B3_of_t1hyp {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)) :
    AuditE3 P Reach L ∧ AuditB3 L P Reach := by
  have R : DataRes3 DataOk := dataRes3_of_rows ⟨hMemRow, hrow, hLeafAlias⟩
  have hS : ∀ c, Reach c → ∃ sp, SOf P c = some sp := by
    intro c hc
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    exact ⟨q.d.shape, by simp [SOf, hq]⟩
  have hcl : ReachClosed Reach (SOf P) := by
    intro c hc sp hSc k hk hch
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    simp only [SOf, hq, Option.map_some, Option.some.injEq] at hSc
    subst hSc
    exact H.closed c hc q hq k hk hch
  have Q := q_induct3 L.O L.T hin hsp hg hS (machPrem3_of_t1hyp H R hA) hcl
  refine ⟨auditE3_of_q hcl Q, ?_⟩
  intro c hc sp hSc k hk y hkid ns
  have K := kidOK_of_kidTA hg hcl Q hc hSc hk hkid
  refine ⟨fun a ha => List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, rfl⟩, ?_, ?_⟩
  · intro a ha mn i cs hm
    obtain ⟨g', hg', rfl⟩ := K.2 a ha mn i cs hm
    exact List.mem_map.mpr ⟨g', List.mem_cons_of_mem _ hg', rfl⟩
  · intro hmem
    obtain ⟨a, ha, e⟩ := List.mem_map.mp hmem
    exact kidOK_hsep hin hsp hc K a ha e
#print axioms auditE3B3_of_t1hyp
end Final

end Tools.ShippingGen5AuditE3B3
