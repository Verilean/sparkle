import Tools.ShippingSrm4Callee
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (binding, residues R3/R5): the callee-level composition for a callee whose calls are ORDINARY calls of ONE leaf `G` AND/OR memory entries (`wrapQ`: two calls of the plain leaf `leafP` and one memory entry), generic in the leaf's
-- interface tables (`genBsC` / `genOutsC` / `genSrcC` / `genPC`) so that BOTH a plain leaf (old-form `MachineRun`, run at every depth) and a leaf with a memory child (`MachineRunNCA`, depth 1) fit.
-- PROVED: `call_inRange_at` (`call_inRange` of `Tools/ShippingQuadCalls.lean` at ONE call: the table of a memory placeholder is not needed), `ordCallee_hcalls` (the per-call `SeqFactsRN` of the ORDINARY calls, the memory calls by `MemFacts`),
-- `callee_composedNW` (`ComposedNW 1` of the callee's served run from the callee's `GenFacts`, `hcalls` and the `hrunN` of its ordinary calls).
-- PREMISES (named): `MemCalleeData` of the callee, `GenFacts`, `MachineClosesAtA` of the callee, the guarded output equation `CallFactFO` (only the ORDINARY calls; text-supplied), `MemFacts` of the memory calls (kernel `rfl` in an instance),
-- the leaf's run `hrunPC`.  `RealChildA` / `ServedRealA` / `JQC` are histories of past synthesis results.  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field, no heartbeat option.

namespace Tools.ShippingSrm4Mixed
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned
open Tools.ShippingTopShareRun
open Tools.ShippingMemCloses
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses
open Tools.ShippingMachineAuto
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingSeqParentLemmas
open Tools.ShippingMachineCallsLinkedT
open Tools.ShippingQuadComposed
open Tools.ShippingQuadCalls
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Run
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingPortWidthsPure (nonDom declWidths declN)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `call_inRange` at ONE call `k`: the table of the callee name of the other calls (a memory placeholder) is not asked -/
theorem call_inRange_at (d : MachineData) {n : Nat} (hok : d.ok = true)
    (hkD : n ≤ d.bsIn.length) (hIlen : (d.bsIn.drop n).length = d.shape.insts.length)
    (hslots : d.ss.length = d.shape.layout.slots.length) (hco : d.callsOk n = true)
    (widths : Nat → List Nat) (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d n widths = true)
    (bsC : Name → List (Name × MixedGateBinder))
    (k : Nat) (hk : k < d.shape.insts.length)
    (hw' : widths k =
      ((bsC (d.shape.insts[k]).1).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth)
    (hlen' : (d.shape.insts[k]).2.1.length = ((bsC (d.shape.insts[k]).1).filter fun b => b.2 != .domain).length)
    (lsrc : List (Nat → Nat))
    (hl : ∀ (a : Nat) (l : Σ s : SType, Term s), d.ls[a]? = some l →
      ∃ v, lsrc[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width) :
    ∀ (τ : Nat),
      Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf lsrc (d.shape.insts[k]).2.1 τ)
        ((bsC (d.shape.insts[k]).1).filter fun b => b.2 != .domain) := by
  intro τ
  have hnIn : d.nIn = n + d.shape.insts.length := by
    have := ok_bsIn_length d hok
    simp only [List.length_drop] at hIlen
    omega
  have hLT := ok_letsTyped d hok
  apply Zip₂.of_get
  · simp only [Tools.ShippingMachineCallsLinkedT.valsOf, List.length_map]; exact hlen'
  · intro q v b hv hb
    simp only [Tools.ShippingMachineCallsLinkedT.valsOf, List.getElem?_map] at hv
    obtain ⟨a, haq, hva⟩ : ∃ a, (d.shape.insts[k]).2.1[q]? = some a ∧
        (lsrc[a]?.map (· τ)).getD 0 = v := by
      cases hq : (d.shape.insts[k]).2.1[q]? with
      | none => simp [hq] at hv
      | some a => simp [hq] at hv; exact ⟨a, rfl, hv⟩
    have hq : q < (d.shape.insts[k]).2.1.length := (List.getElem?_eq_some_iff.mp haq).1
    have halt : a < d.ls.length := by
      have := List.all_eq_true.mp (callsOk_args d n hco k hk) a (List.mem_of_getElem? haq)
      simpa using this
    obtain ⟨l, hlq⟩ : ∃ l, d.ls[a]? = some l := ⟨_, List.getElem?_eq_getElem halt⟩
    obtain ⟨vv, hvv, hlt⟩ := hl a l hlq
    have hKa := LetsTyped.K_get hLT a l hlq
    simp only [MachineData.K] at hKa
    obtain ⟨bn, hbn, hsort⟩ : ∃ bn, d.shape.binders[d.nIn + d.ss.length + a]? = some bn ∧ sortOf bn.2 = some l.1 := by
      cases hh : d.shape.binders[d.nIn + d.ss.length + a]? with
      | none => simp [hh] at hKa
      | some bn => simp [hh] at hKa; exact ⟨bn, rfl, hKa⟩
    have hbn' : d.shape.binders[n + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn := by
      rw [show n + (d.shape.insts.length + (d.shape.layout.slots.length + a)) = d.nIn + d.ss.length + a by omega]; exact hbn
    have hwq : (widths k)[q]? = some ((kindTy b.2).bitWidth) := by
      rw [hw']; simp [List.getElem?_map, hb]
    have hwd := Tools.ShippingPortsMatchRaw.callArgs_width hargs hk haq hbn' hwq
    have hw1 := sortOf_width hsort
    have hb1 : (kindTy b.2).bitWidth = l.1.width := hwd.symm.trans hw1
    have hvlt : v < 2 ^ l.1.width := by
      rw [← hva]; simp [hvv]; exact hlt τ
    have hbnd : b.2 ≠ .domain := by
      have := List.mem_of_getElem? hb
      have := (List.mem_filter.mp this).2
      simpa using this
    cases hbb : b.2 with
    | domain => exact absurd hbb hbnd
    | bool =>
      rw [hbb] at hb1
      simp only [kindTy, Sparkle.IR.Type.HWType.bitWidth] at hb1
      rw [← hb1] at hvlt; simpa using hvlt
    | bits m =>
      rw [hbb] at hb1
      simp only [kindTy, Sparkle.IR.Type.HWType.bitWidth] at hb1
      rw [← hb1] at hvlt; simpa using hvlt

/-- the child tables of a callee whose ordinary calls are all the leaf `G` with interface binders `bsG` and output fields `outsG` -/
def genBsC (G : Name) (bsG : List (Name × MixedGateBinder)) : Name → List (Name × MixedGateBinder) := fun n => if n = G then bsG else []
def genOutsC (G : Name) (outsG : List OutField) : Name → List OutField := fun n => if n = G then outsG else []
def genSrcC (G : Name) (bsG : List (Name × MixedGateBinder))
    (srcG : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)) :
    DomainConfig → Name → (Nat → List Nat) → List (Nat → Nat) :=
  fun i n => if n = G then fun vals => srcG i (Tools.ShippingMachineChild.boolsOf bsG vals) (Tools.ShippingMachineChild.bitsOf bsG vals) else fun _ => []
def genPC (PCs : Sparkle.IR.AST.Module → Prop) : Name → Sparkle.IR.AST.Module → Prop := fun _ mc => PCs mc

/-- **`CallFactF` of the ORDINARY calls only** (a call whose origin builds no module): the output equation at the call-output position under the generated `machineExt` (text-supplied, as `CallFactF`). -/
def CallFactFO (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig}
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k : Nat) (hk : k < dP.shape.insts.length), (originAt dP.shape k).child? = none →
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
      (S i (dP.shape.insts[k]).1 (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
        (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ

section Callee
variable {dC : MachineData} {C G : Name} {nC : Nat} [Inhabited (HList (tys dC.ss))] {ρ : DomainConfig → Type}
  {initsC : HList (tys dC.ss)}
  {bodyC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys dC.ss)) (Circuit.SigList i (tys dC.ss)) (tys dC.ss) →
      Circuit i (Circuit.SigList i (tys dC.ss)) (ρ i)}
  {obsRC : (i : DomainConfig) → ρ i → List (Nat → Nat)}
  {extC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extBC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → Nat → Signal i Bool}
  {srcC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {srcG : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}

/-- **The per-call `SeqFactsRN` of the ORDINARY calls of a callee over ONE leaf** (`leafCallee_hcalls` / `memLeafCallee_hcalls`, generic in the leaf's tables and run predicate `PCs`); the memory calls are `MemFacts`
(`hmem`).  `widths` is the callee-side table of argument widths of ALL calls (`callArgsOk`), the leaf's only where the call is ordinary. -/
theorem ordCallee_hcalls
    {nameK : Nat → String} {nk : Nat → Nat} {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData dC C nC nameK nk outsK namesK names)
    {bsG : List (Name × MixedGateBinder)} {outsG : List OutField} {PCs : Sparkle.IR.AST.Design → Sparkle.IR.AST.Module → Prop}
    (hkids : ∀ (k : Nat) (hk : k < dC.shape.insts.length), (originAt dC.shape k).child? = none → (dC.shape.insts[k]).1 = G)
    (hargsN : ∀ (k : Nat) (hk : k < dC.shape.insts.length), (originAt dC.shape k).child? = none →
      (dC.shape.insts[k]).2.1.length = (bsG.filter nonDom).length)
    (widths : Nat → List Nat) (hwid : Tools.ShippingPortsMatchRaw.callArgsOk dC nC widths = true)
    (hw : ∀ (k : Nat) (hk : k < dC.shape.insts.length), (originAt dC.shape k).child? = none →
      widths k = (bsG.filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth)
    (hmem : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (k : Nat) (c : Name),
      (dC.shape.insts.map (·.1))[k]? = some c → (originAt dC.shape k).child? ≠ none →
      MemFacts dC.shape (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC i bools bits) dC.ls.length (dC.bsIn.drop nC) nC
        (extC i bools bits (stateLoop initsC (bodyC i bools bits))) k c)
    (hrunPC : ∀ (i : DomainConfig) (design : Sparkle.IR.AST.Design) (mc : Sparkle.IR.AST.Module), PCs design mc →
      SeqChildRunN (childMap design.modules) design 1 mc bsG outsG
        (fun vals => srcG i (Tools.ShippingMachineChild.boolsOf bsG vals) (Tools.ShippingMachineChild.bitsOf bsG vals)))
    (hF : CallFactFO dC nC (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (genOutsC G outsG) (genSrcC G bsG srcG))
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
      (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      nC (genBsC G bsG) (genOutsC G outsG) (genSrcC G bsG srcG) (genPC (PCs design)) := by
  intro i bools bits k c hc
  have hlt : k < dC.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
  by_cases hch : (originAt dC.shape k).child? = none
  · right
    have hcG : (dC.shape.insts[k]).1 = G := hkids k hlt hch
    have hck : (dC.shape.insts[k]).1 = c := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hlt] at hc; simpa using hc
    subst hck
    have hR := call_inRange_at dC hC.ok hC.hkD hC.hIlen hC.slots hC.callsOk widths hwid (genBsC G bsG) k hlt
      (by rw [hcG]; unfold genBsC; rw [if_pos rfl]; exact hw k hlt hch)
      (by rw [hcG]; unfold genBsC; rw [if_pos rfl]; exact hargsN k hlt hch)
      _ (letObsB_hl dC (fun i : DomainConfig => i) initsC bodyC extC extBC i bools bits)
    unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
    refine ⟨hch, (dC.shape.insts[k]).2.1, by simp [List.getElem?_map, List.getElem?_eq_getElem hlt], ?_,
      Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args dC nC hC.callsOk k hlt) (by simp [Tools.ShippingMachineCausal.letObsB]),
      hR, hF i bools bits k hlt hch⟩
    intro mc hmc
    have hr := hrunPC i design mc hmc
    rw [hcG]
    refine ⟨?_, ?_⟩
    · unfold genBsC genOutsC genSrcC; simp only [↓reduceIte]; exact hr
    · rw [hr.2.2.2.2.2.1]; exact (hargsN k hlt hch).symm
  · left
    exact hmem i bools bits k c hc hch

/-- **`ComposedNW 1` of a callee with ordinary and memory calls** from `GenFacts`, `hcalls` (`ordCallee_hcalls`) and the `hrunN` of its ordinary calls (a served run of the leaf satisfies the leaf's run predicate `PCs`). -/
theorem callee_composedNW (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {nameK : Nat → String} {nk : Nat → Nat} {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData dC C nC nameK nk outsK namesK names)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    {bsG : List (Name × MixedGateBinder)} {outsG : List OutField} {PCs : Sparkle.IR.AST.Design → Sparkle.IR.AST.Module → Prop}
    (hcalls : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
        (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
        (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
        (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
        nC (genBsC G bsG) (genOutsC G outsG) (genSrcC G bsG srcG) (genPC (PCs design)))
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hrunN : ∀ (k : Nat) (c : Name), (dC.shape.insts.map (·.1))[k]? = some c →
      (dC.shape.instOrigins.getD k .ord).child? = none →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design) (w w' : Void IO.RealWorld),
        AdmCtx O.quiet mctx' cctx' → CacheInvA O (cv w) → sv w = some synthesizeChild → O.quiet w →
        RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w (mc, Dc) w' →
        (∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) →
        moduleByName design.modules mc.name = some mc → PCs design mc)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore C [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref C dC.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx C dC.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 C dC nC m design (fun i : DomainConfig => i) srcC
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits))) := by
  have h := genTrace O T hA dC (fun i : DomainConfig => i) GF (machineRunJQC_of_closesA O hA hcore entry closes hw hc)
  exact machine_linkedT_callsRNA 1 O h hC.fne nC hC.hkD (bsIn_drop_nodomain dC nC hC.domB) hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn
    (genBsC G bsG) (genOutsC G outsG) (genSrcC G bsG srcG) (genPC (PCs design)) (hcalls m design) hrunN

/-- **`SeqChildRunN` at depth 2 of a served run of a callee with ordinary and memory calls** (the boundary `BndA` of the callee's run is not read by the composed theorem). -/
theorem callee_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {nameK : Nat → String} {nk : Nat → Nat} {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData dC C nC nameK nk outsK namesK names)
    (hOk : ∀ o ∈ dC.shape.layout.outs, outNameOk o.name = true)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    {bsG : List (Name × MixedGateBinder)} {outsG : List OutField} {PCs : Sparkle.IR.AST.Design → Sparkle.IR.AST.Module → Prop}
    (BndA : Meta.Context → Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop)
    (hB : ∀ {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      BndA mctx cctx w m design → ∀ (k : Nat) (c : Name), (dC.shape.insts.map (·.1))[k]? = some c →
      (dC.shape.instOrigins.getD k .ord).child? = none →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design) (w w' : Void IO.RealWorld),
        AdmCtx O.quiet mctx' cctx' → CacheInvA O (cv w) → sv w = some synthesizeChild → O.quiet w →
        RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w (mc, Dc) w' →
        (∀ g ∈ Dc.modules, moduleByName design.modules g.name = some g) →
        moduleByName design.modules mc.name = some mc → PCs design mc)
    (hcalls : ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
        (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
        (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
        (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
        nC (genBsC G bsG) (genOutsC G outsG) (genSrcC G bsG srcG) (genPC (PCs design)))
    (hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < nC →
      extBC i bools bits (stateLoop initsC (bodyC i bools bits)) j = bools j)
    (hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < nC →
      extC i bools bits (stateLoop initsC (bodyC i bools bits)) j n' = bits j n')
    (i : DomainConfig) {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : MachineRunNCA O C dC.shape BndA mc design)
    (hcl : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx C dC.shape) :
    SeqChildRunN (childMap design.modules) design 2 mc (List.take nC dC.bsIn) dC.shape.layout.outs
      (fun vals => srcC i
        (Tools.ShippingMachineChild.boolsOf (List.take nC dC.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take nC dC.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 BndA
    (fun hcore hadm hjqc entry cl hBnd =>
      callee_composedNW O T hadm hC GF hcalls (hB hBnd) hjqc.1 (Or.inr hjqc.2) hcore entry (hcl _ _ hadm))
    hC.outTy hOk hC.slotsNe (Nat.pos_of_ne_zero (fun h0 => hC.insts_ne (List.eq_nil_of_length_eq_zero h0)))
    hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn hextB hext i h

end Callee

end Tools.ShippingSrm4Mixed
