import Tests.Compiler.Srm4MixedTest
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (residue R5, composed half): `ComposedNW 2` (the form `ComposedG` is built from) of `topshareQ`, HAND-APPLIED: callees `wrapP` (a PLAIN callee over the plain leaf `leafP`: `leafCallee_seqChildRunN2`) and `wrapQ` (two calls of `leafP` and a
-- memory call: `wrapQ_seqChildRunN2`).  The parent's trace is `topshareQ_traceXA`.
-- PREMISES kept (named): `hcalls₁` (`wrapP`'s per-call `SeqFactsRN`, the old chain's `hcalls` as in `leafCallee_hcalls`), `hF` (`CallFactFO` of `wrapQ`), `hgrp` (`QuadGroupFacts` of the parent; text-supplied), `hR0` / `hcl` (the plain leaf), the
-- `MachineDefines` of the machines, `O`, `T`, `hA`, the start world, `hcore`.  An example does not make the class complete.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Mixed Tools.ShippingSrm4Run
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingQuadComposed (GenFacts genTrace bsIn_drop_nodomain callsOk_args QuadGroupFacts leafBnd)
open Tools.ShippingQuadCalls (LeafSeqRunN)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineDepthRunRA Tools.ShippingMachineDepth
open Tools.ShippingSeqParentLemmas (HCallsOf)
open Tools.ShippingMachineCausal (letObsB)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMachineCallsLinkedT
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

noncomputable instance wrapP_inhab : Inhabited (HList (tys wrapP.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem wrapP_gen : GenFacts wrapP.machineData (fun i : DomainConfig => i) wrapP.machineInits wrapP.machineBody wrapP.machineResult
    wrapP.machineExt wrapP.machineExtB wrapP.machineSource :=
  ⟨wrapP.machine_ok, wrapP.machine_body, wrapP.machine_inits, wrapP.machine_writes, wrapP.machine_result, wrapP.machine_source,
   fun i bools bits S S' t h =>
    wrapP.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrapP_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 3 →
    wrapP.machineExtB i bools bits (stateLoop wrapP.machineInits (wrapP.machineBody i bools bits)) j = bools j := by
  intro i bools bits j hj
  first
    | rfl
    | (delta wrapP.machineExtB
       simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
       (repeat' split) <;> first | rfl | (exfalso; omega))

theorem wrapP_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 3 →
    wrapP.machineExt i bools bits (stateLoop wrapP.machineInits (wrapP.machineBody i bools bits)) j n' = bits j n' := by
  intro i bools bits j n' hj
  delta wrapP.machineExt
  simp only [Tools.ShippingMachineAuto.extendBits]
  (repeat' split) <;> first | rfl | (exfalso; omega)

/-- the callee tables of `topshareQ`: the interface of `wrapP` / `wrapQ` is their first 3 / 5 binders -/
noncomputable def tqBsC : Name → List (Name × MixedGateBinder) := fun n =>
  if n = ``wrapP then wrapP.machineData.bsIn.take 3 else if n = ``wrapQ then wrapQ.machineData.bsIn.take 5 else []
noncomputable def tqOutsC : Name → List OutField := fun n =>
  if n = ``wrapP then wrapP.machineData.shape.layout.outs else if n = ``wrapQ then wrapQ.machineData.shape.layout.outs else []
noncomputable def tqSrcC : Unit → Name → (Nat → List Nat) → List (Nat → Nat) := fun _ n =>
  if n = ``wrapP then fun vals => wrapP.machineSource defaultDomain
      (Tools.ShippingMachineChild.boolsOf (wrapP.machineData.bsIn.take 3) vals) (Tools.ShippingMachineChild.bitsOf (wrapP.machineData.bsIn.take 3) vals)
  else if n = ``wrapQ then fun vals => wrapQ.machineSource defaultDomain
      (Tools.ShippingMachineChild.boolsOf (wrapQ.machineData.bsIn.take 5) vals) (Tools.ShippingMachineChild.bitsOf (wrapQ.machineData.bsIn.take 5) vals)
  else fun _ => []
def tqPC (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) : Name → Sparkle.IR.AST.Module → Prop := fun n mc =>
  if n = ``wrapP then MachineRunNCA O ``wrapP wrapP.machineData.shape (leafBnd ``leafP leafP.machineData mref cref) mc design
  else if n = ``wrapQ then MachineRunNCA O ``wrapQ wrapQ.machineData.shape (leafBnd ``leafP leafP.machineData mref cref) mc design
  else True

theorem tq_decide_hkD : 4 ≤ topshareQ.machineData.bsIn.length := by first | decide | decide +kernel
theorem tq_decide_hIlen : (topshareQ.machineData.bsIn.drop 4).length = topshareQ.machineData.shape.insts.length := by first | decide | decide +kernel
theorem tq_decide_hSL : ∀ b ∈ topshareQ.machineData.slotBs ++ topshareQ.machineData.letBs, b.2 ≠ .domain := by first | decide | decide +kernel
theorem tq_decide_hSlen : topshareQ.machineData.slotBs.length = topshareQ.machineData.shape.layout.slots.length := by first | decide | decide +kernel
theorem tq_decide_hLlen : topshareQ.machineData.letBs.length = topshareQ.machineData.shape.layout.lets := by first | decide | decide +kernel
theorem tq_decide_hNIn : machNIn topshareQ.machineData.shape = ((topshareQ.machineData.bsIn.take 4).filter (fun b => b.2 != .domain)).length := by
  first | decide | decide +kernel

abbrev TqHcallsP (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
    HCallsOf 1 wrapP.machineData design m (dom := fun i : DomainConfig => i)
      (letObsB wrapP.machineData (fun i : DomainConfig => i) wrapP.machineInits wrapP.machineBody wrapP.machineExt wrapP.machineExtB)
      (fun i bools bits => wrapP.machineExt i bools bits (stateLoop wrapP.machineInits (wrapP.machineBody i bools bits)))
      (fun i bools bits => wrapP.machineExtB i bools bits (stateLoop wrapP.machineInits (wrapP.machineBody i bools bits)))
      3 (Tools.ShippingQuadComposed.leafBsC ``leafP leafP.machineData) (Tools.ShippingQuadComposed.leafOutsC ``leafP leafP.machineData)
      (Tools.ShippingQuadComposed.leafSrcC ``leafP leafP.machineData leafP.machineSource) (Tools.ShippingQuadComposed.leafPC ``leafP leafP.machineData)

abbrev TqFQ : Prop := CallFactFO wrapQ.machineData 5
      (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB)
      (fun i bools bits => wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (fun i bools bits => wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (genOutsC ``leafP leafP.machineData.shape.layout.outs) (genSrcC ``leafP leafP.machineData.bsIn leafP.machineSource)

abbrev TqGrp : Prop := QuadGroupFacts topshareQ.machineData 4
      (letObsB topshareQ.machineData (fun _ : Unit => defaultDomain) topshareQ.machineInits topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB)
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      tqBsC tqOutsC tqSrcC

/-- the callee run part for `wrapP` -/
theorem tq_callRunP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (design : Sparkle.IR.AST.Design) (hcalls₁ : TqHcallsP O)
    (mc : Sparkle.IR.AST.Module) (hmc : tqPC O design ``wrapP mc) :
    SeqChildRunN (childMap design.modules) design 2 mc (tqBsC ``wrapP) (tqOutsC ``wrapP) (tqSrcC () ``wrapP) := by
  unfold tqPC at hmc
  rw [if_pos rfl] at hmc
  have hr := Tools.ShippingQuadComposed.leafCallee_seqChildRunN2 O T leafP_data wrapP_calleeData wrapP_extra hcl wrapP_gen hcalls₁ wrapP_hextB wrapP_hext hmc
  unfold tqBsC tqOutsC tqSrcC
  simp only [if_pos rfl]
  exact hr

theorem tq_callRunQ (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (hF : TqFQ) (design : Sparkle.IR.AST.Design)
    (mc : Sparkle.IR.AST.Module) (hmc : tqPC O design ``wrapQ mc) :
    SeqChildRunN (childMap design.modules) design 2 mc (tqBsC ``wrapQ) (tqOutsC ``wrapQ) (tqSrcC () ``wrapQ) := by
  unfold tqPC at hmc
  rw [if_neg (by decide), if_pos rfl] at hmc
  have hr := wrapQ_seqChildRunN2 O T hR0 hcl hF defaultDomain hmc
  unfold tqBsC tqOutsC tqSrcC
  simp only [if_neg (show ``wrapQ ≠ ``wrapP by decide), if_pos rfl]
  exact hr

theorem tq_runWrapP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design} (hreal : RealChildA O ``wrapP (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    tqPC O design ``wrapP mc := by
  unfold tqPC
  rw [if_pos rfl]
  exact Tools.ShippingQuadComposed.leafCallee_runNCA O T leafP_data wrapP_calleeData entry₁ hR0 hcl hreal hcons

theorem tq_runWrapQ (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    {mc : Sparkle.IR.AST.Module} {Dc design : Sparkle.IR.AST.Design} (hreal : RealChildA O ``wrapQ (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) :
    tqPC O design ``wrapQ mc := by
  unfold tqPC
  rw [if_neg (by decide), if_pos rfl]
  exact machineRunNCA_of_real_main O T (BndA := leafBnd ``leafP leafP.machineData mref cref) hreal hcons entry₂
    (fun _ _ _ _ _ _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR0)
    (fun m c _ _ _ hch _ => by
      obtain ⟨_, _, _, hadm', _⟩ := hch
      exact wrapQ_closesA (mctx := m) (cctx := c) O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl)
    (by decide)

set_option linter.unusedSimpArgs false

/-- the parent's per-call `SeqFactsRN` at depth 2 -/
theorem topshareQ_hcallsNW (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design)
    (hcalls₁ : TqHcallsP O) (hF : TqFQ) (hgrp : TqGrp) :
    HCallsOf 2 topshareQ.machineData design m (dom := fun _ : Unit => defaultDomain)
      (letObsB topshareQ.machineData (fun _ : Unit => defaultDomain) topshareQ.machineInits topshareQ.machineBody topshareQ.machineExt topshareQ.machineExtB)
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      4 tqBsC tqOutsC tqSrcC (tqPC O design) := by
  intro i bools bits k c' hk2
  obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hk2
  have hlt : k < topshareQ.machineData.shape.insts.length := by simpa using hlt'
  have hget' : (topshareQ.machineData.shape.insts[k]).1 = c' := by simpa using hget
  subst hget'
  right
  unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  obtain ⟨hR, hF'⟩ := hgrp i bools bits k hlt
  refine ⟨Tools.ShippingQuadLeafGeneric.origin_child_none _ (topshareQ_parentData.nomemKey k hlt),
    (topshareQ.machineData.shape.insts[k]).2.1, map_getElem?_of_lt (fun x => x.2.1) hlt, ?_,
    Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args topshareQ.machineData 4 topshareQ_parentData.callsOk k hlt) (by simp [letObsB]), hR, hF'⟩
  intro mc hmc
  have hname := topshareQ_name k hlt
  have hargsK := topshareQ_parentData.argsN k hlt
  by_cases hk2' : k < 2
  · rw [hname, if_pos hk2'] at hmc ⊢
    have hr := tq_callRunP O T hcl design hcalls₁ mc hmc
    refine ⟨hr, ?_⟩
    rw [hr.2.2.2.2.2.1]
    unfold tqBsC
    rw [if_pos rfl, ← wrapP_calleeData.hNIn, ← hargsK]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  · rw [hname, if_neg hk2'] at hmc ⊢
    have hr := tq_callRunQ O T hR0 hcl hF design mc hmc
    refine ⟨hr, ?_⟩
    rw [hr.2.2.2.2.2.1]
    unfold tqBsC
    rw [if_neg (show ``wrapQ ≠ ``wrapP by decide), if_pos rfl, ← wrapQ_memCallee.hNIn, ← hargsK]
    have hk4 : k < 4 := by have := topshareQ_len; omega
    rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl <;> rfl

/-- **`ComposedNW 2` of `topshareQ`** -/
theorem topshareQ_composedNW (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    (hcalls₁ : TqHcallsP O) (hF : TqFQ) (hgrp : TqGrp)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineDepthRun.ComposedNW 2 ``topshareQ topshareQ.machineData 4 m design (fun _ : Unit => defaultDomain) topshareQ.machineSource
      (fun i bools bits => topshareQ.machineExt i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits)))
      (fun i bools bits => topshareQ.machineExtB i bools bits (stateLoop topshareQ.machineInits (topshareQ.machineBody i bools bits))) :=
  machine_linkedT_callsRNA 2 O (topshareQ_traceXA O T hA hR0 hcl entry₁ entry₂ entryP hw hcore) topshareQ_fne 4 tq_decide_hkD
    (bsIn_drop_nodomain topshareQ.machineData 4 topshareQ_parentData.domB)
    tq_decide_hIlen tq_decide_hSL tq_decide_hSlen tq_decide_hLlen tq_decide_hNIn
    tqBsC tqOutsC tqSrcC (tqPC O design)
    (topshareQ_hcallsNW O T hR0 hcl m design hcalls₁ hF hgrp)
    (fun k c' hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hm : c' ∈ topshareQ.machineData.shape.insts.map (·.1) := List.mem_of_getElem? hc'
      rw [topshareQ_callees'] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact tq_runWrapP O T hR0 hcl entry₁ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons
      · exact tq_runWrapP O T hR0 hcl entry₁ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons
      · exact tq_runWrapQ O T hR0 hcl entry₂ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons
      · exact tq_runWrapQ O T hR0 hcl entry₂ (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcallsNW
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_composedNW
