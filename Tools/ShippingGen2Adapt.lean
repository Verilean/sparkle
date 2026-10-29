import Tools.ShippingGen2CallDec
set_option autoImplicit false

/-! # U-ADAPT: the pointwise CallDec adapter (scripts/gen2/G3GEN_CALL_PLAN.md rev1 §1, approved 508b365e)

For ONE ordinary call `k`: its complete `HPointAt` (output relation included) and LOCAL argument-width/count data give
`CallDec p q k`. No `HPointAt`, package or width/arity table of any other call is used. The data hypotheses are
`p.d.ok`, the GLOBAL syntactic check `p.d.callsOk p.kD` (retained; it is a whole-parent data check), the slot count,
and the k-local `callArgsOkAt`/arity rows. Memory calls are not handled here (`MemDec`). -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

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
open Tools.ShippingQuadComposed
open Tools.ShippingQuadCalls Tools.ShippingQuadHPoint (HPointAt)

variable {ι : Type} {dom : ι → DomainConfig}

/-- The k-th slice of `callArgsOk` (Tools/ShippingPortsMatchRaw.lean:199), against a width list `ws`. -/
def callArgsOkAt (d : MachineData) (nDecl k : Nat) (ws : List Nat) : Bool :=
  (List.range ws.length).all fun j =>
    decide ((((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
      (d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]?).map
        fun bn => (kindTy bn.2).bitWidth) = ws[j]?)

/-- A callee package's declared non-domain port widths. -/
def SrcPkg.portWidths (q : SrcPkg ι dom) : List Nat := q.ports.map fun b => (kindTy b.2).bitWidth

/-- What `callArgsOkAt` gives at an argument position (as `callArgs_width`, PortsMatchRaw.lean:208). -/
theorem callArgsOkAt_width {d : MachineData} {nDecl k : Nat} {ws : List Nat}
    (h : callArgsOkAt d nDecl k ws = true) (hk : k < d.shape.insts.length) {j a : Nat}
    (ha : ((d.shape.insts[k]).2.1)[j]? = some a) {bn : Name × MixedGateBinder}
    (hbn : d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn)
    {wd : Nat} (hwd : ws[j]? = some wd) : (kindTy bn.2).bitWidth = wd := by
  unfold callArgsOkAt at h
  have hj : j < ws.length := (List.getElem?_eq_some_iff.mp hwd).1
  have h2 : (((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
        (d.shape.binders[nDecl + (d.shape.insts.length +
          (d.shape.layout.slots.length + a))]?).map fun bn => (kindTy bn.2).bitWidth) = ws[j]? :=
    of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr hj))
  rw [List.getElem?_eq_getElem hk] at h2
  have h3 : (((d.shape.insts[k]).2.1)[j]?).bind (fun a =>
        (d.shape.binders[nDecl + (d.shape.insts.length +
          (d.shape.layout.slots.length + a))]?).map fun bn => (kindTy bn.2).bitWidth) = ws[j]? := h2
  rw [ha] at h3
  have h4 : (d.shape.binders[nDecl + (d.shape.insts.length +
        (d.shape.layout.slots.length + a))]?).map (fun bn => (kindTy bn.2).bitWidth) = ws[j]? := h3
  rw [hbn, hwd] at h4
  have h5 : some ((kindTy bn.2).bitWidth) = some wd := h4
  exact Option.some.inj h5

/-- **Local `InRange`** (the per-k body of `call_inRange`, QuadCalls.lean:112-176, with local tables). -/
theorem call_inRange_at (p q : SrcPkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hargsK : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ τ, Tools.ShippingMachineChild.InRange (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1 τ) q.ports := by
  intro τ
  have hl := @letObsB_hl p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB i bools bits
  have hnIn : p.d.nIn = p.kD + p.d.shape.insts.length := (callsOk_nIn p.d p.kD hco).symm
  have hLT := ok_letsTyped p.d hok
  apply Zip₂.of_get
  · simp only [Tools.ShippingMachineCallsLinkedT.valsOf, List.length_map]; exact hlenK
  · intro r v b hv hb
    simp only [Tools.ShippingMachineCallsLinkedT.valsOf, List.getElem?_map] at hv
    obtain ⟨a, har, hva⟩ : ∃ a, (p.d.shape.insts[k]).2.1[r]? = some a ∧
        ((p.lsrc i bools bits)[a]?.map (· τ)).getD 0 = v := by
      cases hr : (p.d.shape.insts[k]).2.1[r]? with
      | none => simp [hr] at hv
      | some a => simp [hr] at hv; exact ⟨a, rfl, hv⟩
    have halt : a < p.d.ls.length := by
      have := List.all_eq_true.mp (callsOk_args p.d p.kD hco k hk) a (List.mem_of_getElem? har)
      simpa using this
    obtain ⟨l, hlr⟩ : ∃ l, p.d.ls[a]? = some l := ⟨_, List.getElem?_eq_getElem halt⟩
    obtain ⟨vv, hvv, hlt⟩ := hl a l hlr
    have hKa := LetsTyped.K_get hLT a l hlr
    simp only [MachineData.K] at hKa
    obtain ⟨bn, hbn, hsort⟩ : ∃ bn, p.d.shape.binders[p.d.nIn + p.d.ss.length + a]? = some bn ∧
        sortOf bn.2 = some l.1 := by
      cases hh : p.d.shape.binders[p.d.nIn + p.d.ss.length + a]? with
      | none => simp [hh] at hKa
      | some bn => simp [hh] at hKa; exact ⟨bn, rfl, hKa⟩
    have hbn' : p.d.shape.binders[p.kD + (p.d.shape.insts.length + (p.d.shape.layout.slots.length + a))]? =
        some bn := by
      rw [show p.kD + (p.d.shape.insts.length + (p.d.shape.layout.slots.length + a)) =
        p.d.nIn + p.d.ss.length + a by omega]; exact hbn
    have hwr : q.portWidths[r]? = some ((kindTy b.2).bitWidth) := by
      simp [SrcPkg.portWidths, List.getElem?_map, hb]
    have hwd := callArgsOkAt_width hargsK hk har hbn' hwr
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

/-- **The pointwise adapter** (frozen interface). -/
theorem callDec_of_hPointAt_at (P : Pkgs ι dom) (p q : SrcPkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hH : HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k)
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hargsK : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length) :
    CallDec p q k := by
  refine ⟨hnone, (p.d.shape.insts[k]).2.1, by simp [hk], hlenK, ?_⟩
  intro i bools bits
  have hl := @letObsB_hl p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB i bools bits
  refine ⟨?_, call_inRange_at p q k hk hok hco hslots hargsK hlenK i bools bits, ?_⟩
  · intro r hr
    have hlt := callsOk_argsLets p.d p.kD hco k hk r hr
    refine ⟨hlt, ?_⟩
    obtain ⟨v, hv, -⟩ := hl _ _ (List.getElem?_eq_getElem hlt)
    exact ⟨v, hv⟩
  · obtain ⟨A, B, hA, hB, k', o, f, ho, hon, hf, hpos⟩ := hH i bools bits hk
    refine ⟨k', o, f, ?_, hon, ?_, hpos⟩
    · simpa [pkgOutsC, hP] using ho
    · have hS := pkgS_dispatch P i (p.d.shape.insts[k]).1 (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1)
      rw [hA, hB] at hS
      have hS' : q.S i (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) =
          pkgSrc P i (p.d.shape.insts[k]).1 A B := by
        rw [← hS]; simp [pkgS, hP]
      rw [hS']; exact hf

end Tools.ShippingGen2
