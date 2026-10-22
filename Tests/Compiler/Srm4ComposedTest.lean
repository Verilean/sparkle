import Tests.Compiler.Srm4ParentTest
-- BUILT (unit SRM4): i4 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (residue R5, composed half): `ComposedNW 2` (the stateful linked run at depth 2, the form `ComposedG` is built from) of `topshareM`, HAND-APPLIED: the parent's trace is `topshareM_traceXA`, the callees' depth-2 runs are
-- `memLeafCallee_seqChildRunN2` (callees over the memory-bearing leaf `leafM`), the served callee runs are `MachineRunNCA` by `machineRunNCA_of_real_main` (`MachineClosesAtA` of the callees DERIVED, SRM3).
-- PREMISES kept (named): `hcalls₁` / `hcalls₂` (the callees' per-call `SeqFactsRN`; `memLeafCallee_hcalls` derives them from the callee's `CallFactF` `hF`, text-supplied), `hextB*` / `hext*`, `hgrp` (`QuadGroupFacts` of the parent: the parent's
-- per-call `InRange` and output equation under the GENERATED `machineExt`; text-supplied), `O`, `T`, `hA`, the `MachineDefines` of the four machines, the start world, `hcore`.  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
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
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the callee tables of `topshareM`: the interface of `wrapM` / `wrapM3` is their first four binders -/
noncomputable def tmBsC : Name → List (Name × MixedGateBinder) := fun n =>
  if n = ``wrapM then wrapM.machineData.bsIn.take 4 else if n = ``wrapM3 then wrapM3.machineData.bsIn.take 4 else []
noncomputable def tmOutsC : Name → List OutField := fun n =>
  if n = ``wrapM then wrapM.machineData.shape.layout.outs else if n = ``wrapM3 then wrapM3.machineData.shape.layout.outs else []
noncomputable def tmSrcC : Unit → Name → (Nat → List Nat) → List (Nat → Nat) := fun _ n =>
  if n = ``wrapM then fun vals => wrapM.machineSource defaultDomain
      (Tools.ShippingMachineChild.boolsOf (wrapM.machineData.bsIn.take 4) vals) (Tools.ShippingMachineChild.bitsOf (wrapM.machineData.bsIn.take 4) vals)
  else if n = ``wrapM3 then fun vals => wrapM3.machineSource defaultDomain
      (Tools.ShippingMachineChild.boolsOf (wrapM3.machineData.bsIn.take 4) vals) (Tools.ShippingMachineChild.bitsOf (wrapM3.machineData.bsIn.take 4) vals)
  else fun _ => []
/-- what a served run of a callee must establish: its `MachineRunNCA` at the parent's design, with the leaf's `MachineDefines` as boundary -/
def tmPC (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) : Name → Sparkle.IR.AST.Module → Prop := fun n mc =>
  if n = ``wrapM then MachineRunNCA O ``wrapM wrapM.machineData.shape (fun m c _ _ _ => MachineDefines m mref c cref ``leafM leafM.machineData.shape) mc design
  else if n = ``wrapM3 then MachineRunNCA O ``wrapM3 wrapM3.machineData.shape (fun m c _ _ _ => MachineDefines m mref c cref ``leafM leafM.machineData.shape) mc design
  else True

theorem wrapM3_kids' : ∀ (k : Nat) (hk : k < wrapM3.machineData.shape.insts.length),
    (wrapM3.machineData.shape.insts[k]).1 = ``leafM ∧ Tools.ShippingMemCloses.memKey (originAt wrapM3.machineData.shape k) = none := by
  first | decide | decide +kernel
theorem wrapM3_outOk : ∀ o ∈ wrapM3.machineData.shape.layout.outs, outNameOk o.name = true := by
  first | decide | decide +kernel

noncomputable instance wrapM3_inhab : Inhabited (HList (tys wrapM3.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem wrapM3_gen : GenFacts wrapM3.machineData (fun i : DomainConfig => i) wrapM3.machineInits wrapM3.machineBody wrapM3.machineResult
    wrapM3.machineExt wrapM3.machineExtB wrapM3.machineSource :=
  ⟨wrapM3.machine_ok, wrapM3.machine_body, wrapM3.machine_inits, wrapM3.machine_writes, wrapM3.machine_result, wrapM3.machine_source,
   fun i bools bits S S' t h =>
    wrapM3.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrapM3_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 4 →
    wrapM3.machineExtB i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)) j = bools j := by
  intro i bools bits j hj
  first
    | rfl
    | (delta wrapM3.machineExtB
       simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
       (repeat' split) <;> first | rfl | (exfalso; omega))

theorem wrapM3_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 4 →
    wrapM3.machineExt i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)) j n' = bits j n' := by
  intro i bools bits j n' hj
  delta wrapM3.machineExt
  simp only [Tools.ShippingMachineAuto.extendBits]
  (repeat' split) <;> first | rfl | (exfalso; omega)

theorem wrapM3_argsN : ∀ (k : Nat) (hk : k < wrapM3.machineData.shape.insts.length),
    (wrapM3.machineData.shape.insts[k]).2.1.length = ((leafM.machineData.bsIn.take 4).filter Tools.ShippingPortWidthsPure.nonDom).length := by
  first | decide | decide +kernel

theorem wrapM3_wid : Tools.ShippingPortsMatchRaw.callArgsOk wrapM3.machineData 4 (fun _ => Tools.ShippingCallsChildPorts.argWidths leafM.machineData 4) = true := by
  first | decide | decide +kernel

theorem map_getElem?_of_lt {α β : Type} (f : α → β) {l : List α} {k : Nat} (hk : k < l.length) : (l.map f)[k]? = some (f l[k]) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl

theorem tm_decide_hkD : 4 ≤ topshareM.machineData.bsIn.length := by first | decide | decide +kernel
theorem tm_decide_hIlen : (topshareM.machineData.bsIn.drop 4).length = topshareM.machineData.shape.insts.length := by first | decide | decide +kernel
theorem tm_decide_hSL : ∀ b ∈ topshareM.machineData.slotBs ++ topshareM.machineData.letBs, b.2 ≠ .domain := by first | decide | decide +kernel
theorem tm_decide_hSlen : topshareM.machineData.slotBs.length = topshareM.machineData.shape.layout.slots.length := by first | decide | decide +kernel
theorem tm_decide_hLlen : topshareM.machineData.letBs.length = topshareM.machineData.shape.layout.lets := by first | decide | decide +kernel
theorem tm_decide_hNIn : machNIn topshareM.machineData.shape = ((topshareM.machineData.bsIn.take 4).filter (fun b => b.2 != .domain)).length := by
  first | decide | decide +kernel

/-- the callee's run part of `SeqFactsRN` for call `k`: the depth-2 `SeqChildRunN` of the callee's served run -/
theorem tm_callRun (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (design : Sparkle.IR.AST.Design)
    (hcalls₁ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 wrapM.machineData design m (dom := fun i : DomainConfig => i)
        (letObsB wrapM.machineData (fun i : DomainConfig => i) wrapM.machineInits wrapM.machineBody wrapM.machineExt wrapM.machineExtB)
        (fun i bools bits => wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
        (fun i bools bits => wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
        4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
        (memLeafPC O ``leafM leafM.machineData design))
    (mc : Sparkle.IR.AST.Module) (hmc : tmPC O design ``wrapM mc) :
    SeqChildRunN (childMap design.modules) design 2 mc (tmBsC ``wrapM) (tmOutsC ``wrapM) (tmSrcC () ``wrapM) := by
  unfold tmPC at hmc
  rw [if_pos rfl] at hmc
  have hr := memLeafCallee_seqChildRunN2 (srcG := leafM.machineSource) O T wrapM_memCallee wrapM_outOk (fun k hk => (wrapM_kids' k hk).1) wrapM_gen entryL
    (fun m c hA => leafM_closesA O T hA) leafM_insts_ne hcalls₁ wrapM_hextB wrapM_hext defaultDomain hmc
  unfold tmBsC tmOutsC tmSrcC
  simp only [if_pos rfl]
  exact hr

theorem tm_callRun3 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (design : Sparkle.IR.AST.Design)
    (hcalls₂ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 wrapM3.machineData design m (dom := fun i : DomainConfig => i)
        (letObsB wrapM3.machineData (fun i : DomainConfig => i) wrapM3.machineInits wrapM3.machineBody wrapM3.machineExt wrapM3.machineExtB)
        (fun i bools bits => wrapM3.machineExt i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
        (fun i bools bits => wrapM3.machineExtB i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
        4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
        (memLeafPC O ``leafM leafM.machineData design))
    (mc : Sparkle.IR.AST.Module) (hmc : tmPC O design ``wrapM3 mc) :
    SeqChildRunN (childMap design.modules) design 2 mc (tmBsC ``wrapM3) (tmOutsC ``wrapM3) (tmSrcC () ``wrapM3) := by
  unfold tmPC at hmc
  rw [if_neg (by decide), if_pos rfl] at hmc
  have hr := memLeafCallee_seqChildRunN2 (srcG := leafM.machineSource) O T wrapM3_memCallee wrapM3_outOk (fun k hk => (wrapM3_kids' k hk).1) wrapM3_gen entryL
    (fun m c hA => leafM_closesA O T hA) leafM_insts_ne hcalls₂ wrapM3_hextB wrapM3_hext defaultDomain hmc
  unfold tmBsC tmOutsC tmSrcC
  simp only [if_neg (show ``wrapM3 ≠ ``wrapM by decide), if_pos rfl]
  exact hr

set_option linter.unusedSimpArgs false

/-- the parent's per-call `SeqFactsRN` at depth 2 -/
theorem topshareM_hcallsNW (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design)
    (hcalls₁ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 wrapM.machineData design m (dom := fun i : DomainConfig => i)
        (letObsB wrapM.machineData (fun i : DomainConfig => i) wrapM.machineInits wrapM.machineBody wrapM.machineExt wrapM.machineExtB)
        (fun i bools bits => wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
        (fun i bools bits => wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
        4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
        (memLeafPC O ``leafM leafM.machineData design))
    (hcalls₂ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 wrapM3.machineData design m (dom := fun i : DomainConfig => i)
        (letObsB wrapM3.machineData (fun i : DomainConfig => i) wrapM3.machineInits wrapM3.machineBody wrapM3.machineExt wrapM3.machineExtB)
        (fun i bools bits => wrapM3.machineExt i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
        (fun i bools bits => wrapM3.machineExtB i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
        4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
        (memLeafPC O ``leafM leafM.machineData design))
    (hgrp : QuadGroupFacts topshareM.machineData 4
      (letObsB topshareM.machineData (fun _ : Unit => defaultDomain) topshareM.machineInits topshareM.machineBody topshareM.machineExt topshareM.machineExtB)
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      tmBsC tmOutsC tmSrcC) :
    HCallsOf 2 topshareM.machineData design m (dom := fun _ : Unit => defaultDomain)
      (letObsB topshareM.machineData (fun _ : Unit => defaultDomain) topshareM.machineInits topshareM.machineBody topshareM.machineExt topshareM.machineExtB)
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      4 tmBsC tmOutsC tmSrcC (tmPC O design) := by
  intro i bools bits k c' hk2
  obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hk2
  have hlt : k < topshareM.machineData.shape.insts.length := by simpa using hlt'
  have hget' : (topshareM.machineData.shape.insts[k]).1 = c' := by simpa using hget
  subst hget'
  right
  unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  obtain ⟨hR, hF⟩ := hgrp i bools bits k hlt
  refine ⟨Tools.ShippingQuadLeafGeneric.origin_child_none _ (Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_parentData.nomemKey k hlt),
    (topshareM.machineData.shape.insts[k]).2.1, map_getElem?_of_lt (fun x => x.2.1) hlt, ?_,
    Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args topshareM.machineData 4
      Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_parentData.callsOk k hlt) (by simp [letObsB]), hR, hF⟩
  intro mc hmc
  have hname := topshareM_name k hlt
  have hk4 : k < 4 := by have := topshareM_len; omega
  have hargsK := Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_parentData.argsN k hlt
  by_cases hk2' : k < 2
  · rw [hname, if_pos hk2'] at hmc ⊢
    have hr := tm_callRun O T entryL design hcalls₁ mc hmc
    refine ⟨hr, ?_⟩
    rw [hr.2.2.2.2.2.1]
    unfold tmBsC
    rw [if_pos rfl, ← wrapM_memCallee.hNIn, ← hargsK]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  · rw [hname, if_neg hk2'] at hmc ⊢
    have hr := tm_callRun3 O T entryL design hcalls₂ mc hmc
    refine ⟨hr, ?_⟩
    rw [hr.2.2.2.2.2.1]
    unfold tmBsC
    rw [if_neg (show ``wrapM3 ≠ ``wrapM by decide), if_pos rfl, ← wrapM3_memCallee.hNIn, ← hargsK]
    rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl <;> rfl

/-- a served run of `wrapM` is a `MachineRunNCA` (the boundary is the leaf's `MachineDefines`) -/
theorem tm_runWrapM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design} (hreal : RealChildA O ``wrapM (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    tmPC O design ``wrapM mc := by
  unfold tmPC
  rw [if_pos rfl]
  exact machineRunNCA_of_real_main O T (BndA := fun m c _ _ _ => MachineDefines m mref c cref ``leafM leafM.machineData.shape)
    hreal hcons entry₁ (fun _ _ _ _ _ _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx entryL)
    (fun m c _ _ _ hch _ => by
      obtain ⟨_, _, _, hadm', _⟩ := hch
      exact wrapM_closesA (mctx := m) (cctx := c) O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx entryL))
    (by decide)

theorem tm_runWrapM3 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design} (hreal : RealChildA O ``wrapM3 (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    tmPC O design ``wrapM3 mc := by
  unfold tmPC
  rw [if_neg (by decide), if_pos rfl]
  exact machineRunNCA_of_real_main O T (BndA := fun m c _ _ _ => MachineDefines m mref c cref ``leafM leafM.machineData.shape)
    hreal hcons entry₂ (fun _ _ _ _ _ _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx entryL)
    (fun m c _ _ _ hch _ => by
      obtain ⟨_, _, _, hadm', _⟩ := hch
      exact wrapM3_closesA (mctx := m) (cctx := c) O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx entryL))
    (by decide)

/-- **`ComposedNW 2` of `topshareM`** (the stateful linked run of the parent's module at depth 2 shows the source). -/
theorem topshareM_composedNW (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    (hcalls₁ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 wrapM.machineData design m (dom := fun i : DomainConfig => i)
        (letObsB wrapM.machineData (fun i : DomainConfig => i) wrapM.machineInits wrapM.machineBody wrapM.machineExt wrapM.machineExtB)
        (fun i bools bits => wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
        (fun i bools bits => wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
        4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
        (memLeafPC O ``leafM leafM.machineData design))
    (hcalls₂ : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 wrapM3.machineData design m (dom := fun i : DomainConfig => i)
        (letObsB wrapM3.machineData (fun i : DomainConfig => i) wrapM3.machineInits wrapM3.machineBody wrapM3.machineExt wrapM3.machineExtB)
        (fun i bools bits => wrapM3.machineExt i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
        (fun i bools bits => wrapM3.machineExtB i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits)))
        4 (memLeafBsC ``leafM leafM.machineData 4) (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource)
        (memLeafPC O ``leafM leafM.machineData design))
    (hgrp : QuadGroupFacts topshareM.machineData 4
      (letObsB topshareM.machineData (fun _ : Unit => defaultDomain) topshareM.machineInits topshareM.machineBody topshareM.machineExt topshareM.machineExtB)
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      tmBsC tmOutsC tmSrcC)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineDepthRun.ComposedNW 2 ``topshareM topshareM.machineData 4 m design (fun _ : Unit => defaultDomain) topshareM.machineSource
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits))) :=
  machine_linkedT_callsRNA 2 O (topshareM_traceXA O T hA entryL entry₁ entry₂ entryP hw hcore) topshareM_fne 4 tm_decide_hkD
    (bsIn_drop_nodomain topshareM.machineData 4 (Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_parentData.domB))
    tm_decide_hIlen tm_decide_hSL tm_decide_hSlen tm_decide_hLlen tm_decide_hNIn
    tmBsC tmOutsC tmSrcC (tmPC O design)
    (topshareM_hcallsNW O T entryL m design hcalls₁ hcalls₂ hgrp)
    (fun k c' hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hm : c' ∈ topshareM.machineData.shape.insts.map (·.1) := List.mem_of_getElem? hc'
      rw [topshareM_callees] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact tm_runWrapM O T entryL entry₁ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons
      · exact tm_runWrapM O T entryL entry₁ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons
      · exact tm_runWrapM3 O T entryL entry₂ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons
      · exact tm_runWrapM3 O T entryL entry₂ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcallsNW
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_composedNW
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.tm_callRun
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.tm_callRun3
