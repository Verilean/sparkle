import Tests.Compiler.Srm4ParentQTest
import Tests.Compiler.Srm4ComposedTest
import Tools.ShippingSrm4Mixed
-- BUILT (unit SRM4): n4 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (residue R5, composed half, mixed callee): `Tools.ShippingSrm4Mixed.callee_seqChildRunN2` HAND-APPLIED to `wrapQ` (two calls of the PLAIN leaf `leafP` and ONE memory entry), and `ComposedNW 2` of `topshareQ` (callees `wrapP`, plain over the
-- plain leaf, via `leafCallee_seqChildRunN2`; and `wrapQ`).  The leaf `leafP`'s run is its GENERATED `leafP.seq_child_runN` (made here by `generateSeqChildN`, the generator the K-ary templates use).
-- PREMISES kept (named): `hF` (`CallFactFO` of `wrapQ`: the output equation of its ORDINARY calls under the generated `machineExt`; text-supplied), `hcalls` of `wrapP` (the old chain's, as `leafCallee_hcalls`), `hgrp` (`QuadGroupFacts` of the parent;
-- text-supplied), `hR0` / `hcl` (`MachineDefines` / `MachineCloses` of the plain leaf), the `MachineDefines` of the machines, `O`, `T`, `hA`, the start world, `hcore`.  The memory call's `MemFacts` are kernel `rfl`.  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`.
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let _ ← Tools.ShippingMachineDepthCommand.generateSeqChildN ``Tests.Compiler.SharedLeafMemKidTest.leafP

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

theorem leafP_run : LeafSeqRunN ``leafP leafP.machineData leafP.machineSource := leafP.seq_child_runN

/-! ## `wrapQ` -/

noncomputable instance wrapQ_inhab : Inhabited (HList (tys wrapQ.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem wrapQ_gen : GenFacts wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineResult
    wrapQ.machineExt wrapQ.machineExtB wrapQ.machineSource :=
  ⟨wrapQ.machine_ok, wrapQ.machine_body, wrapQ.machine_inits, wrapQ.machine_writes, wrapQ.machine_result, wrapQ.machine_source,
   fun i bools bits S S' t h =>
    wrapQ.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrapQ_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 5 →
    wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)) j = bools j := by
  intro i bools bits j hj
  first
    | rfl
    | (delta wrapQ.machineExtB
       simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
       (repeat' split) <;> first | rfl | (exfalso; omega))

theorem wrapQ_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 5 →
    wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)) j n' = bits j n' := by
  intro i bools bits j n' hj
  delta wrapQ.machineExt
  simp only [Tools.ShippingMachineAuto.extendBits]
  (repeat' split) <;> first | rfl | (exfalso; omega)

theorem wrapQ_outOk : ∀ o ∈ wrapQ.machineData.shape.layout.outs, outNameOk o.name = true := by first | decide | decide +kernel
theorem wrapQ_ordKid : ∀ (k : Nat) (hk : k < wrapQ.machineData.shape.insts.length), (originAt wrapQ.machineData.shape k).child? = none →
    (wrapQ.machineData.shape.insts[k]).1 = ``leafP := fun k hk h => (wrapQ_ord k hk h).2
theorem wrapQ_argsN : ∀ (k : Nat) (hk : k < wrapQ.machineData.shape.insts.length), (originAt wrapQ.machineData.shape k).child? = none →
    (wrapQ.machineData.shape.insts[k]).2.1.length = (leafP.machineData.bsIn.filter Tools.ShippingPortWidthsPure.nonDom).length := by
  first | decide | decide +kernel
noncomputable def wqW : Nat → List Nat := fun k =>
  if k < 2 then (leafP.machineData.bsIn.filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth) else Tools.ShippingMemKid.memIns 4 8
theorem wrapQ_wid : Tools.ShippingPortsMatchRaw.callArgsOk wrapQ.machineData 5 wqW = true := by first | decide | decide +kernel
theorem wrapQ_hw : ∀ (k : Nat) (hk : k < wrapQ.machineData.shape.insts.length), (originAt wrapQ.machineData.shape k).child? = none →
    wqW k = (leafP.machineData.bsIn.filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth := by
  intro k hk h
  have := (wrapQ_ord k hk h).1
  unfold wqW; rw [if_pos this]

theorem wrapQ_nonmem : ∀ (k : Nat) (hk : k < wrapQ.machineData.shape.insts.length), (originAt wrapQ.machineData.shape k).child? ≠ none → k = 2 := by
  first | decide | decide +kernel

/-- the memory call of `wrapQ` (call 2): its `MemFacts`, kernel `rfl` -/
theorem wrapQ_memcalls : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (k : Nat) (c : Name),
    (wrapQ.machineData.shape.insts.map (·.1))[k]? = some c → (originAt wrapQ.machineData.shape k).child? ≠ none →
    MemFacts wrapQ.machineData.shape (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB i bools bits)
      wrapQ.machineData.ls.length (wrapQ.machineData.bsIn.drop 5) 5
      (wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits))) k c := by
  intro i bools bits k c hc hch
  have hk : k < wrapQ.machineData.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
  have hk2 := wrapQ_nonmem k hk hch
  subst hk2
  refine ⟨false, 4, 8, ?A, ?D, ?E, ?R, 1, 2, 3, 1, rfl, rfl, ?h0, by decide, ?h1, by decide, ?h2, by decide, ?h3, by decide, rfl, ?hx⟩
  case hx => intro j; rfl
  all_goals rfl

abbrev wqPCs : Sparkle.IR.AST.Design → Sparkle.IR.AST.Module → Prop := fun _ mc => Tools.ShippingGateChild.MachineRun ``leafP leafP.machineData.shape mc

/-- the per-call `SeqFactsRN` of `wrapQ` (ordinary calls: the plain leaf's run; memory call: `MemFacts`) -/
theorem wrapQ_hcalls (hF : CallFactFO wrapQ.machineData 5
      (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB)
      (fun i bools bits => wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (fun i bools bits => wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (genOutsC ``leafP leafP.machineData.shape.layout.outs) (genSrcC ``leafP leafP.machineData.bsIn leafP.machineSource))
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 wrapQ.machineData design m (dom := fun i : DomainConfig => i)
      (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB)
      (fun i bools bits => wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (fun i bools bits => wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      5 (genBsC ``leafP leafP.machineData.bsIn) (genOutsC ``leafP leafP.machineData.shape.layout.outs)
      (genSrcC ``leafP leafP.machineData.bsIn leafP.machineSource) (genPC (wqPCs design)) :=
  ordCallee_hcalls (initsC := wrapQ.machineInits) (bodyC := wrapQ.machineBody) (extC := wrapQ.machineExt) (extBC := wrapQ.machineExtB)
    (srcG := leafP.machineSource) (bsG := leafP.machineData.bsIn) (outsG := leafP.machineData.shape.layout.outs) (PCs := wqPCs)
    wrapQ_memCallee wrapQ_ordKid wrapQ_argsN wqW wrapQ_wid wrapQ_hw wrapQ_memcalls
    (fun i design mc hmc => by
      obtain ⟨mctx', mref', cctx', cref', w1, w2, Dc, hrun', hdef, hcl⟩ := hmc
      exact leafP_run i hrun' hdef hcl (childMap design.modules) design 1) hF m design

/-- the `hrunN` of `wrapQ`'s ordinary calls: a served run of `leafP` satisfies the plain leaf's run predicate -/
theorem wrapQ_hrunN (O : RefLawsAOps MkRefd mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (design : Sparkle.IR.AST.Design) :
    ∀ (k : Nat) (c : Name), (wrapQ.machineData.shape.insts.map (·.1))[k]? = some c →
      (wrapQ.machineData.shape.instOrigins.getD k .ord).child? = none →
      ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design) (w w' : Void IO.RealWorld),
        AdmCtx O.quiet mctx' cctx' → CacheInvA O (cv w) → sv w = some synthesizeChild → O.quiet w →
        RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w (mc, Dc) w' →
        (∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) →
        moduleByName design.modules mc.name = some mc → wqPCs design mc := by
  intro k c hc hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod
  have hk : k < wrapQ.machineData.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
  have hck : c = ``leafP := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc
    rw [← Option.some.inj hc]
    exact wrapQ_ordKid k hk hnone
  subst hck
  exact ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0, hcl mctx' cctx'⟩

/-- **`wrapQ` (a callee with a memory call next to two calls of the plain leaf `leafP`): `SeqChildRunN` at depth 2 of a served run** -/
theorem wrapQ_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (hF : CallFactFO wrapQ.machineData 5
      (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB)
      (fun i bools bits => wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (fun i bools bits => wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (genOutsC ``leafP leafP.machineData.shape.layout.outs) (genSrcC ``leafP leafP.machineData.bsIn leafP.machineSource))
    (i : DomainConfig) {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : MachineRunNCA O ``wrapQ wrapQ.machineData.shape (fun mctx cctx _ _ _ => MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape) mc design) :
    SeqChildRunN (childMap design.modules) design 2 mc (List.take 5 wrapQ.machineData.bsIn) wrapQ.machineData.shape.layout.outs
      (fun vals => wrapQ.machineSource i
        (Tools.ShippingMachineChild.boolsOf (List.take 5 wrapQ.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take 5 wrapQ.machineData.bsIn) vals)) :=
  callee_seqChildRunN2 (srcG := leafP.machineSource) (bsG := leafP.machineData.bsIn) (outsG := leafP.machineData.shape.layout.outs) (PCs := wqPCs)
    O T wrapQ_memCallee wrapQ_outOk wrapQ_gen (fun mctx cctx _ _ _ => MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (fun {m c w mm dd} hB => wrapQ_hrunN O hB hcl dd)
    (fun m design => wrapQ_hcalls hF m design) wrapQ_hextB wrapQ_hext i h
    (fun m c hA => wrapQ_closesA (mctx := m) (cctx := c) O T hA (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl)

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_hcalls
#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_seqChildRunN2
