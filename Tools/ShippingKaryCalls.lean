import Tools.ShippingKaryComposed
-- BUILT (unit SR21): k6 exit 0 (Tools.ShippingKaryCalls, dev run); the final-SHA rebuild is in REPORT-SR21.md.
-- SCOPE (binding, ledger L8ba): `ComposedG` of a parent with K ≥ 1 callees that share one leaf, with the per-call premises split as in `quad_composed_split` (`Tools/ShippingQuadCalls.lean`,
-- untouched): `kary_composed_split`.  The generated per-declaration facts of EVERY callee are collected in the structure `KaryGen e …` (the elaborator-generated `machine_*` facts `gen`, the
-- per-call output equation `hF`, and `hextB` / `hext`), supplied for each callee of `cs` by a function `gens : ∀ e ∈ cs, KaryGen e …` (an instance proves each of them for its own
-- declaration; nothing here is derived from the data bundles alone).  The parent's text-supplied facts are `GP` (`GenFacts`) and `hFP` (`CallFactF` at the K-ary tables); the leaf's
-- is `hleafRun` (`LeafSeqRunN`).  Derived: the range of every call's arguments (`kary_inRange`), the per-call `SeqFactsRN` of the callees (`leafCallee_hcalls`) and of the parent, the callees'
-- depth-2 runs (`leafCallee_seqChildRunN2`), the served callees' `MachineRunNCA` (`leafCallee_runNCA`), the parent's trace.  `RealChildA` / `ServedRealA` / `JQC` / `MachineRunNCA` are histories
-- of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingKaryCalls
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The generated per-declaration facts of ONE callee** (text-supplied, named exactly): the callee `e` of the shared leaf `G` has the `Inhabited` instance `inh` of its state tuple, the
generated state tuple `inits`, body `body`, observation `obsR`, extensions `ext` / `extB`; `gen` is the callee's `GenFacts` (the generated `machine_ok / machine_body / machine_inits /
machine_writes / machine_result / machine_source / machine_ext_causal`, with source `e.src`), `hF` the output equation of EVERY call of the callee (`CallFactF` at the leaf tables), and
`hextB` / `hext` say that the generated extensions read the declared inputs.  Not derivable from the data bundles. -/
structure KaryGen (e : KCal) (G : Name) (dG : MachineData) (srcG : KSrc) : Type 1 where
  inh : Inhabited (HList (tys e.d.ss))
  ρ : DomainConfig → Type
  inits : HList (tys e.d.ss)
  body : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys e.d.ss)) (Circuit.SigList i (tys e.d.ss)) (tys e.d.ss) →
      Circuit i (Circuit.SigList i (tys e.d.ss)) (ρ i)
  obsR : (i : DomainConfig) → ρ i → List (Nat → Nat)
  ext : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys e.d.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)
  extB : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys e.d.ss)) → Nat → Signal i Bool
  gen : @GenFacts e.d DomainConfig (fun i : DomainConfig => i) ρ inh inits body obsR ext extB e.src
  hF : CallFactF e.d e.n (@letObsB e.d DomainConfig (fun i : DomainConfig => i) inh ρ inits body ext extB)
      (fun i bools bits => ext i bools bits (@stateLoop i (tys e.d.ss) (ρ i) inh inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (@stateLoop i (tys e.d.ss) (ρ i) inh inits (body i bools bits)))
      (leafOutsC G dG) (leafSrcC G dG srcG)
  hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < e.n →
      extB i bools bits (@stateLoop i (tys e.d.ss) (ρ i) inh inits (body i bools bits)) j = bools j
  hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < e.n →
      ext i bools bits (@stateLoop i (tys e.d.ss) (ρ i) inh inits (body i bools bits)) j n' = bits j n'

section Parent
variable {dP dG : MachineData} {cs : List KCal} {c G : Name} {nP : Nat}
  {ι : Type} {dom : ι → DomainConfig} {ρ : ι → Type} [Inhabited (HList (tys dP.ss))]
  {initsP : HList (tys dP.ss)}
  {bodyP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys dP.ss)) (Circuit.SigList (dom i) (tys dP.ss)) (tys dP.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys dP.ss)) (ρ i)}
  {obsRP : (i : ι) → ρ i → List (Nat → Nat)}
  {extP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
  {extBP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → Nat → Signal (dom i) Bool}
  {srcP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
  {srcG : KSrc}

/-- **`ComposedG` at depth 2 of a K-callee parent, the per-call premises split** (K-ary `quad_composed_split`; the `composed` premise of the endpoint).  TEXT-SUPPLIED premises, named:
`GP` (the parent's `GenFacts`), `gens` (`KaryGen` of every callee), `hleafRun` (the leaf's generated `seq_child_runN`), `hFP` (the parent's per-call output equations, `CallFactF`).  Derived here:
the range of every call's arguments, the callees' `hcalls`, depth-2 runs and served `MachineRunNCA`, the parent's trace, the `machine_linkedT_callsRNA` data conditions. -/
theorem kary_composed_split
    (Q : KaryAll dP dG cs c G nP)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (gens : ∀ (j : Nat) (hj : j < cs.length), KaryGen (cs[j]) G dG srcG)
    (hleafRun : LeafSeqRunN G dG srcG)
    (hFP : CallFactF dP nP (letObsB dP dom initsP bodyP extP extBP)
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (kOutsOf cs) (kSrcF cs))
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref c dP.shape)
    (hB : KaryBnd cs G dG mctx mref cctx cref w m design) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) c dP nP m design dom srcP
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits))) := by
  obtain ⟨O, T, hA, hB'⟩ := hB
  obtain ⟨hent, hR0, hw⟩ := kandk_forall hB'
  have h := kary_traceXA O T hA Q GP entry hent hR0 hcl hw hcore
  have hgrp : QuadGroupFacts dP nP (letObsB dP dom initsP bodyP extP extBP)
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (kBsF cs) (kOutsOf cs) (kSrcF cs) :=
    quadGroupFacts_of_RF dP nP (fun i bools bits k hk τ => kary_inRange Q initsP bodyP extP extBP i bools bits k hk τ) hFP
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h Q.hP.fne nP Q.hPX.hkD (bsIn_drop_nodomain dP nP Q.hP.domB) Q.hPX.hIlen Q.hPX.hSL Q.hPX.hSlen
    Q.hPX.hLlen Q.hPX.hNIn (kBsF cs) (kOutsOf cs) (kSrcF cs) (kPC O design G dG cs)
    (fun i bools bits k c' hk2 => by
      obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hk2
      have hlt : k < dP.shape.insts.length := by simpa using hlt'
      have hget' : (dP.shape.insts[k]).1 = c' := by simpa using hget
      subst hget'
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      obtain ⟨hR, hF⟩ := hgrp i bools bits k hlt
      refine ⟨origin_child_none _ (Q.hP.nomemKey k hlt), (dP.shape.insts[k]).2.1,
        by simp [List.getElem?_map, List.getElem?_eq_getElem hlt], ?_,
        Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args dP nP Q.hP.callsOk k hlt)
          (by simp [letObsB]), hR, hF⟩
      intro mc hmc
      have hj : k / 2 < cs.length := kary_idx_lt Q.hP.names hlt
      obtain ⟨hce, hn⟩ := kary_call_callee Q.hP.names hlt
      have he : cs[k / 2] ∈ cs := List.getElem_mem hj
      rw [hn] at hmc ⊢
      unfold kPC at hmc
      rw [kFind_of_mem Q.hP.nodup he] at hmc
      have g := gens (k / 2) hj
      letI := g.inh
      have hr := leafCallee_seqChildRunN2 O T Q.hG (Q.hC _ he) (Q.hX _ he) hcl g.gen
        (fun m' d' => leafCallee_hcalls Q.hG Q.hK (Q.hC _ he) (Q.hX _ he) hleafRun g.hF m' d') g.hextB g.hext hmc
      refine ⟨?_, ?_⟩
      · unfold kBsF kOutsOf kSrcF
        simp only [kFind_of_mem Q.hP.nodup he]
        exact hr
      · rw [hr.2.2.2.2.2.1, ← (Q.hC _ he).hNIn, ← Q.hP.argsN k hlt]
        exact (kNk_of hce).symm)
    (fun k c' hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      obtain ⟨e, he, hck⟩ := kary_name_mem Q.hP.names hc'
      have hrun' : RunsTo (synthesizeCombinational e.c) mctx' mref cctx' cref w1 (mc, Dc) w2 := hck ▸ hrun
      rw [hck]
      unfold kPC
      rw [kFind_of_mem Q.hP.nodup he]
      exact leafCallee_runNCA O T Q.hG (Q.hC e he) (hent e he) hR0 hcl
        (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun') hcons)

end Parent

end Tools.ShippingKaryCalls

#print axioms Tools.ShippingKaryCalls.kary_composed_split
