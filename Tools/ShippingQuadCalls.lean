import Tools.ShippingQuadComposed
-- BUILT (unit SR16): c1 exit 0 (qbuild build Tools.ShippingQuadCalls); final-SHA rebuild in REPORT-SR16.md.
-- SCOPE (binding, ledger L8av): splits the text-supplied premises of `Tools/ShippingQuadComposed.lean`.  PROVED here: `call_inRange` / `quad_inRange` (the `InRange` of every call's argument values,
-- the old `gfR*` fact, DERIVED from `MachineData.ok` (typed `let`s), `callsOk`, `callArgsOk` and the callee tables); `leafCallee_hcalls` (the callee's `hcalls`, per call, DERIVED: child is the leaf, no memory
-- origin, argument list, arguments are `let`s, range, port count, leaf's run); `quad_composed_split` (`quad_composed` with the callees' `hcalls` and the parent's `QuadGroupFacts` derived).
-- PREMISES that remain (named): `LeafSeqRunN` (the leaf's generated `seq_child_runN`); `CallFactF` of each callee and of the parent (the output equation at the call-output position under the GENERATED
-- `machineExt/ExtB`; not derivable from `GenFacts`); `GenFacts`; `hext`/`hextB`.  No sorry / axiom / native_decide.  RealChildA/ServedRealA/JQC are histories, not freshness.
namespace Tools.ShippingQuadCalls
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

/-! ## Facts read off `MachineData.ok` -/

/-- the `LetsTyped` conjunct of `ok` -/
theorem ok_letsTyped (d : MachineData) (h : d.ok = true) :
    LetsTyped d.bpos d.vpos d.kb d.kv d.vw d.K (d.nIn + d.ss.length) d.ls := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, hslots, fb, fv, fslots, flets, nextsWF, houts, hne⟩ := h
  exact flets

/-- the declared inputs and the state fit in the binders -/
theorem ok_len (d : MachineData) (h : d.ok = true) : d.nIn + d.ss.length ≤ d.shape.binders.length := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hlen, -⟩ := h
  exact hlen

theorem ok_lets (d : MachineData) (h : d.ok = true) : d.shape.layout.lets = d.letBs.length := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨-, hlets, -⟩ := h
  exact hlets

theorem ok_bsIn_length (d : MachineData) (h : d.ok = true) : d.bsIn.length = d.nIn := by
  have := ok_len d h
  simp only [MachineData.bsIn, List.length_take]; omega

/-- the declared-input count of a machine with `d.ss.length = layout.slots.length` is `nIn` -/
theorem declN_eq (d : MachineData) (h : d.ok = true) (hs : d.ss.length = d.shape.layout.slots.length) :
    declN d = d.nIn := by
  have h1 := ok_len d h
  have h2 := ok_lets d h
  have h3 : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp only [MachineData.letBs, List.length_drop]
  unfold declN
  omega

/-! ## Values of `let` observations are in range of their sort -/

theorem enc_lt : ∀ (s : SType) (v : s.Type), enc s v < 2 ^ s.width
  | .bool, b => by
    show Tools.ShippingMuxLoweringSoundness.encodeBool b < 2 ^ 1
    exact Tools.ShippingMuxLoweringSoundness.encodeBool_lt b
  | .bits w, v => by
    show v.toNat < 2 ^ w
    exact v.isLt

theorem LetsTyped.K_get {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {K : Nat → Option SType} :
    ∀ {p : Nat} {ls : List (Σ s : SType, Term s)}, LetsTyped bpos vpos kb kv vw K p ls →
      ∀ (a : Nat) (l : Σ s : SType, Term s), ls[a]? = some l → K (p + a) = some l.1
  | _, [], _, a, l, h => by simp at h
  | p, _ :: _, h, 0, l, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl; simpa using h.2.2.1
  | p, _ :: _, h, a + 1, l, hl => by
    have := LetsTyped.K_get h.2.2.2 a l (by simpa using hl)
    rw [show p + (a + 1) = p + 1 + a by omega]; exact this

theorem sortOf_width {b : MixedGateBinder} {s : SType} (h : sortOf b = some s) :
    (kindTy b).bitWidth = s.width := by
  cases b <;> simp [sortOf] at h <;> subst h <;> simp [kindTy, SType.width, Sparkle.IR.Type.HWType.bitWidth]


/-- **The argument values of every call are in range of the callee's binders** — DERIVED from `MachineData.ok` (the `let`s are typed), `callsOk`
(the arguments are `let`s), `callArgsOk` (the width of the parent's `let` binder is the width of the callee's port) and the table facts `hw` / `hlen`
(the callee's port widths and count, from the child tables).  This is the `R` conjunct of the old chain's `gfR*` facts; it no longer needs the generated
`machineExt` text.  `lsrc` is any list of observations bounded by the sort of the `let` (`letObsB` is, by `letObsB_lt`). -/
theorem call_inRange (d : MachineData) {n : Nat} (hok : d.ok = true)
    (hkD : n ≤ d.bsIn.length) (hIlen : (d.bsIn.drop n).length = d.shape.insts.length)
    (hslots : d.ss.length = d.shape.layout.slots.length) (hco : d.callsOk n = true)
    (widths : Nat → List Nat) (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d n widths = true)
    (bsC : Name → List (Name × MixedGateBinder))
    (hw : ∀ (k : Nat) (hk : k < d.shape.insts.length), widths k =
      ((bsC (d.shape.insts[k]).1).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth)
    (hlen : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).2.1.length = ((bsC (d.shape.insts[k]).1).filter fun b => b.2 != .domain).length)
    (lsrc : List (Nat → Nat))
    (hl : ∀ (a : Nat) (l : Σ s : SType, Term s), d.ls[a]? = some l →
      ∃ v, lsrc[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (τ : Nat),
      Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf lsrc (d.shape.insts[k]).2.1 τ)
        ((bsC (d.shape.insts[k]).1).filter fun b => b.2 != .domain) := by
  intro k hk τ
  have hnIn : d.nIn = n + d.shape.insts.length := by
    have := ok_bsIn_length d hok
    simp only [List.length_drop] at hIlen
    omega
  have hLT := ok_letsTyped d hok
  apply Zip₂.of_get
  · simp only [Tools.ShippingMachineCallsLinkedT.valsOf, List.length_map]; exact hlen k hk
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
      rw [hw k hk]; simp [List.getElem?_map, hb]
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


/-! ## `leafNk` / `declWidths` of a leaf are read off its binders -/

theorem leafNk_eq (d : MachineData) (h : d.ok = true) (hs : d.ss.length = d.shape.layout.slots.length) :
    leafNk d = (d.bsIn.filter fun b => b.2 != .domain).length := by
  have h1 : d.shape.binders.length - d.shape.layout.slots.length - d.shape.layout.lets = d.nIn := declN_eq d h hs
  unfold leafNk
  rw [h1]; rfl

theorem declWidths_eq (d : MachineData) (h : d.ok = true) (hs : d.ss.length = d.shape.layout.slots.length) :
    declWidths d = (d.bsIn.filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth := by
  have h1 : declN d = d.nIn := declN_eq d h hs
  unfold declWidths Tools.ShippingPortWidthsPure.declTys
  rw [h1, List.map_map]
  rfl

/-- the `let` observations are bounded by the sort of the `let` -/
theorem letObsB_hl (d : MachineData) {ι : Type} (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ (a : Nat) (l : Σ s : SType, Term s), d.ls[a]? = some l →
      ∃ v, (Tools.ShippingMachineCausal.letObsB d dom inits body ext extB i bools bits)[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width := by
  intro a l hl
  unfold Tools.ShippingMachineCausal.letObsB
  rw [List.getElem?_map, hl]
  exact ⟨_, rfl, fun τ => enc_lt l.1 _⟩


/-! ## The residue of a call's group facts: only the output equation `F` -/

/-- **The ONE text-supplied fact of a call, `F`** (named exactly): the callee's source output at the field the call reads, on the decoded argument values, is at
every time the value of the parent's input position `nP + k` (the call-output position) under the GENERATED `machineExt` / `machineExtB`.  It depends on the
generated definitions of `machineExt` / `machineExtB` (and on the decoded families of the call's arguments being those of the call, the old `gfHb*` / `gfHv*`),
so it is NOT derivable from `GenFacts`; in an instance it is the old chain's `gfHb*` / `gfHv*` plus `decoded_eq`.  The existence of the output field is the
`∃`; the range of the arguments is NOT part of this (it is derived by `call_inRange`). -/
def CallFactF (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig}
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
    (k : Nat) (hk : k < dP.shape.insts.length),
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
      (S i (dP.shape.insts[k]).1 (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
        (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ

/-- `QuadGroupFacts` = the derived range `R` + the residue `F`. -/
theorem quadGroupFacts_of_RF (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {bsC : Name → List (Name × MixedGateBinder)} {outsC : Name → List OutField}
    {S : ι → Name → (Nat → List Nat) → List (Nat → Nat)}
    (hR : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (k : Nat) (hk : k < dP.shape.insts.length) (τ : Nat),
      Tools.ShippingMachineChild.InRange
        (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1 τ)
        ((bsC (dP.shape.insts[k]).1).filter fun b => b.2 != .domain))
    (hF : CallFactF dP nP lsrc ext extB outsC S) :
    QuadGroupFacts dP nP lsrc ext extB bsC outsC S :=
  fun i bools bits k hk => ⟨hR i bools bits k hk, hF i bools bits k hk⟩

/-! ## The range `R` of the parent's calls (QUAD), derived -/

/-- **`R` of the QUAD parent's calls, derived** (the `InRange` conjunct of the old `gfR*` facts): from `ok` of the parent, the data bundle and the callees' binder tables. -/
theorem quad_inRange {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    {ι : Type} {dom : ι → DomainConfig} [Inhabited (HList (tys dP.ss))] {ρ : ι → Type}
    (initsP : HList (tys dP.ss))
    (bodyP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys dP.ss)) (Circuit.SigList (dom i) (tys dP.ss)) (tys dP.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys dP.ss)) (ρ i))
    (extP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extBP : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys dP.ss)) → Nat → Signal (dom i) Bool)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ (k : Nat) (hk : k < dP.shape.insts.length) (τ : Nat),
      Tools.ShippingMachineChild.InRange
        (Tools.ShippingMachineCallsLinkedT.valsOf (Tools.ShippingMachineCausal.letObsB dP dom initsP bodyP extP extBP i bools bits)
          (dP.shape.insts[k]).2.1 τ)
        ((quadBsF c₁ c₂ d₁ d₂ n₁ n₂ (dP.shape.insts[k]).1).filter fun b => b.2 != .domain) := by
  have hwid : ∀ (d : MachineData) (n : Nat), Tools.ShippingCallsChildPorts.argWidths d n =
      ((d.bsIn.take n).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth := by
    intro d n
    unfold Tools.ShippingCallsChildPorts.argWidths
    rw [List.map_map]; rfl
  refine call_inRange dP (n := nP) Q.hP.ok Q.hPX.hkD Q.hPX.hIlen Q.hP.slots Q.hP.callsOk
    (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) Q.hPX.callArgs (quadBsF c₁ c₂ d₁ d₂ n₁ n₂) ?_ ?_
    (Tools.ShippingMachineCausal.letObsB dP dom initsP bodyP extP extBP i bools bits)
    (letObsB_hl dP dom initsP bodyP extP extBP i bools bits)
  · intro k hk
    show quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k) = _
    rw [quadCalleeAt_eq dP k hk]
    rcases quad_insts_mem Q.hP k hk with hn | hn
    · rw [hn]; unfold quadWidthsOf quadBsF; rw [if_pos rfl, if_pos rfl]; exact hwid d₁ n₁
    · rw [hn]; unfold quadWidthsOf quadBsF
      rw [if_neg (Ne.symm Q.hP.c12), if_neg (Ne.symm Q.hP.c12), if_pos rfl, if_pos rfl]; exact hwid d₂ n₂
  · intro k hk
    have hnk := Q.hP.argsN k hk
    rcases quad_callee_at Q.hP k hk with ⟨hn, hk2⟩ | ⟨hn, hk2⟩
    · rw [hn]; unfold quadBsF; rw [if_pos rfl]
      simp only [quadNk, hk2, if_true] at hnk
      rw [← hnk, Q.hC₁.hNIn]
    · rw [hn]; unfold quadBsF; rw [if_neg (Ne.symm Q.hP.c12), if_pos rfl]
      simp only [quadNk, hk2, if_false] at hnk
      rw [← hnk, Q.hC₂.hNIn]


/-! ## The callee's `hcalls`, split per call -/

/-- **The leaf's generated run theorem** (`G.seq_child_runN`, TEXT-SUPPLIED, one per leaf; produced by the machine-route elaborator from `G.machine_sound`): a served
run of the leaf's entry is a `SeqChildRunN` of its source at every depth.  The leaf has no calls of its own, so this is the depth-free fact the callee's `SeqFactsRN`
needs for its calls (the part of the old `hcalls` that is about the LEAF, not about the callee's `machineExt`). -/
def LeafSeqRunN (G : Name) (dG : MachineData)
    (srcG : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∀ (i : DomainConfig) {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinational G) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref G dG.shape → MachineCloses mctx mref cctx cref G dG.shape →
    ∀ (children : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (dsn : Sparkle.IR.AST.Design) (n : Nat),
      Tools.ShippingMachineDepth.SeqChildRunN children dsn n b dG.bsIn dG.shape.layout.outs fun vals =>
        srcG i (Tools.ShippingMachineChild.boolsOf dG.bsIn vals) (Tools.ShippingMachineChild.bitsOf dG.bsIn vals)

section Callee
variable {dC dG : MachineData} {C G : Name} {n : Nat} [Inhabited (HList (tys dC.ss))] {ρ : DomainConfig → Type}
  {initsC : HList (tys dC.ss)}
  {bodyC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys dC.ss)) (Circuit.SigList i (tys dC.ss)) (tys dC.ss) →
      Circuit i (Circuit.SigList i (tys dC.ss)) (ρ i)}
  {extC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extBC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → Nat → Signal i Bool}
  {srcG : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}

/-- **The callee's `hcalls`, split per call and DERIVED** (replaces the text-supplied `ts0_C_hcalls` / `ts1_C_hcalls` / `epD2M{i}_C_hcalls` of SR15): every call `k` of the
callee `dC` to the leaf `dG` is a `SeqFactsRN` at the child tables of the leaf.  Derived from the data bundles (the child is the leaf, no memory origin, the argument list,
the arguments are `let`s, their ranges (`call_inRange`), the port count of the leaf) and from the two text-supplied facts that remain, each named: `hrun` (the leaf's
generated `seq_child_runN`) and `hF` (the output equation `F` of EVERY call, `CallFactF`).  The statement is the type of the old `hcalls` (`HCallsOf 1 …`). -/
theorem leafCallee_hcalls
    (hG : LeafData dG) (hK : LeafKidData dG) (hC : LeafCalleeData dC dG C G n) (hX : LeafCalleeExtra dC dG n)
    (hrun : LeafSeqRunN G dG srcG)
    (hF : CallFactF dC n (Tools.ShippingMachineCausal.letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (leafOutsC G dG) (leafSrcC G dG srcG))
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
      (Tools.ShippingMachineCausal.letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      n (leafBsC G dG) (leafOutsC G dG) (leafSrcC G dG srcG) (leafPC G dG) := by
  intro i bools bits k c hc
  have hlt : k < dC.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
  have hcG : (dC.shape.insts[k]).1 = G := (hC.kids k hlt).1
  have hck : (dC.shape.insts[k]).1 = c := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt] at hc; simpa using hc
  subst hck
  right
  have hR := call_inRange dC hC.ok hC.hkD hC.hIlen hC.slots hC.callsOk (fun _ => declWidths dG) hX.callArgs (leafBsC G dG)
    (fun k hk => by
      rw [(hC.kids k hk).1]; unfold leafBsC; rw [if_pos rfl]; exact declWidths_eq dG hG.ok hK.slots)
    (fun k hk => by
      rw [(hC.kids k hk).1]; unfold leafBsC; rw [if_pos rfl]
      rw [← leafNk_eq dG hG.ok hK.slots, hC.argsN k hk])
    _ (letObsB_hl dC (fun i : DomainConfig => i) initsC bodyC extC extBC i bools bits) k hlt
  unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  refine ⟨origin_child_none _ (hC.kids k hlt).2, (dC.shape.insts[k]).2.1,
    by simp [List.getElem?_map, List.getElem?_eq_getElem hlt], ?_,
    Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args dC n hC.callsOk k hlt) (by simp [Tools.ShippingMachineCausal.letObsB]), hR, hF i bools bits k hlt⟩
  intro mc hmc
  have hmc' : Tools.ShippingGateChild.MachineRun G dG.shape mc := by
    unfold leafPC at hmc; split at hmc <;> exact hmc
  obtain ⟨mctx', mref', cctx', cref', w1, w2, Dc, hrun', hdef, hcl⟩ := hmc'
  have hr := hrun i hrun' hdef hcl (childMap design.modules) design 1
  rw [hcG]
  refine ⟨?_, ?_⟩
  · unfold leafBsC leafOutsC leafSrcC; simp only [↓reduceIte]; exact hr
  · rw [hr.2.2.2.2.2.1, ← hC.argsN k hlt, leafNk_eq dG hG.ok hK.slots]

end Callee


/-! ## `ComposedG` of the QUAD parent with the split premises -/

section Parent3
variable {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
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
  [Inhabited (HList (tys d₁.ss))] [Inhabited (HList (tys d₂.ss))]
  {ρ₁ ρ₂ : DomainConfig → Type}
  {inits₁ : HList (tys d₁.ss)}
  {body₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys d₁.ss)) (Circuit.SigList i (tys d₁.ss)) (tys d₁.ss) →
      Circuit i (Circuit.SigList i (tys d₁.ss)) (ρ₁ i)}
  {obsR₁ : (i : DomainConfig) → ρ₁ i → List (Nat → Nat)}
  {ext₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₁.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extB₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₁.ss)) → Nat → Signal i Bool}
  {src₁ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {inits₂ : HList (tys d₂.ss)}
  {body₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys d₂.ss)) (Circuit.SigList i (tys d₂.ss)) (tys d₂.ss) →
      Circuit i (Circuit.SigList i (tys d₂.ss)) (ρ₂ i)}
  {obsR₂ : (i : DomainConfig) → ρ₂ i → List (Nat → Nat)}
  {ext₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₂.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extB₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d₂.ss)) → Nat → Signal i Bool}
  {src₂ : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {srcG : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}

set_option maxHeartbeats 8000000 in
/-- **`quad_composed` with the callees' `hcalls` and the parent's `QuadGroupFacts` DERIVED** (SR16): the text-supplied premises are now the per-call output equations
`hF₁` / `hF₂` / `hFP` (`CallFactF`: the generated `machineExt` at the call-output position equals the callee source's output at the decoded argument values), the leaf's
generated `seq_child_runN` (`hrun`), the generated `machine_*` facts `GP` / `G₁` / `G₂`, and `hextB` / `hext` of the callees.  Derived: the range `R` of every call's
arguments (`call_inRange`, `quad_inRange`), the per-call `SeqFactsRN` of the callees (`leafCallee_hcalls`) and of the parent (inside `quad_composed`). -/
theorem quad_composed_split
    (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂)
    (GP : GenFacts dP dom initsP bodyP obsRP extP extBP srcP)
    (G₁ : GenFacts d₁ (fun i : DomainConfig => i) inits₁ body₁ obsR₁ ext₁ extB₁ src₁)
    (G₂ : GenFacts d₂ (fun i : DomainConfig => i) inits₂ body₂ obsR₂ ext₂ extB₂ src₂)
    (hrun : LeafSeqRunN G dG srcG)
    (hF₁ : CallFactF d₁ n₁ (Tools.ShippingMachineCausal.letObsB d₁ (fun i : DomainConfig => i) inits₁ body₁ ext₁ extB₁)
      (fun i bools bits => ext₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)))
      (fun i bools bits => extB₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)))
      (leafOutsC G dG) (leafSrcC G dG srcG))
    (hF₂ : CallFactF d₂ n₂ (Tools.ShippingMachineCausal.letObsB d₂ (fun i : DomainConfig => i) inits₂ body₂ ext₂ extB₂)
      (fun i bools bits => ext₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)))
      (fun i bools bits => extB₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)))
      (leafOutsC G dG) (leafSrcC G dG srcG))
    (hFP : CallFactF dP nP (Tools.ShippingMachineCausal.letObsB dP dom initsP bodyP extP extBP)
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (quadOutsOf c₁ c₂ d₁ d₂) (quadSrcF c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂))
    (hextB₁ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < n₁ →
      extB₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)) j = bools j)
    (hext₁ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < n₁ →
      ext₁ i bools bits (stateLoop inits₁ (body₁ i bools bits)) j n' = bits j n')
    (hextB₂ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < n₂ →
      extB₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)) j = bools j)
    (hext₂ : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < n₂ →
      ext₂ i bools bits (stateLoop inits₂ (body₂ i bools bits)) j n' = bits j n')
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref c dP.shape)
    (hB : QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w m design) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) c dP nP m design dom srcP
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits))) :=
  quad_composed Q GP G₁ G₂
    (fun m' design' => leafCallee_hcalls Q.hG Q.hK Q.hC₁ Q.hX₁ hrun hF₁ m' design')
    (fun m' design' => leafCallee_hcalls Q.hG Q.hK Q.hC₂ Q.hX₂ hrun hF₂ m' design')
    hextB₁ hext₁ hextB₂ hext₂
    (quadGroupFacts_of_RF dP nP (fun i bools bits k hk τ => quad_inRange Q initsP bodyP extP extBP i bools bits k hk τ) hFP)
    hcl hcore entry hB

end Parent3

end Tools.ShippingQuadCalls

#print axioms Tools.ShippingQuadCalls.call_inRange
#print axioms Tools.ShippingQuadCalls.quad_inRange
#print axioms Tools.ShippingQuadCalls.leafCallee_hcalls
#print axioms Tools.ShippingQuadCalls.quad_composed_split
