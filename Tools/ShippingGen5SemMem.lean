import Tools.ShippingGen5SemCongr
set_option autoImplicit false
-- Clean build smu4v-1258f07e (exit 0, 709 jobs, approved at 1258f07e; Lean content unchanged since c28de8a1). No sorry/axiom/native_decide.
/-! # DG-SEM U4F (scripts/gen5/DG_SEM_FREEZE_P4.md rev1 §5.3): final-stage memory equation, `lsrcAt_genSemGen`, `memFacts_of_genSem`

Premises are those of the freeze (`GenWF`, `d.ok`); none of them is supplied here for a real run (DG-WFCOVER, DG-DATAOF). -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## the three rows at one call -/

theorem rowC_at (d : MachineData) (h : RowC d = true) (k : Nat) (hk : k < d.shape.insts.length) :
    ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true := by
  unfold RowC at h
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  intro l hl
  have := List.all_eq_true.mp this l hl
  simpa using this

theorem rowA_at (d : MachineData) (h : RowA d = true) (k : Nat) (hk : k < d.shape.insts.length) :
    (∀ l ∈ callArgs d k, l < d.ls.length) ∧
    (∀ cb aw dw, originOf d k = .mem cb aw dw → (callArgs d k).length = 4) := by
  unfold RowA at h
  simp only [Bool.and_eq_true] at h
  have h2 := List.all_eq_true.mp h.2 k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true] at h2
  refine ⟨fun l hl => ?_, fun cb aw dw ho => ?_⟩
  · have := List.all_eq_true.mp h2.1 l hl
    simpa using this
  · have := h2.2
    rw [ho] at this
    simpa using this

theorem rowB_at (d : MachineData) (h : RowB d = true) (k : Nat) (hk : k < d.shape.insts.length)
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (ho : originOf d k = .mem cb aw dw)
    (ha : callArgs d k = [l0, l1, l2, l3]) :
    callKind d k = .bits dw ∧ letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
      letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw) := by
  unfold RowB at h
  have h2 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true] at h2
  have h3 := h2.2
  rw [ho, ha] at h3
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  exact ⟨h3.1.1.1.1, h3.1.1.1.2, h3.1.1.2, h3.1.2, h3.2⟩

/-! ## P4c and the memory equation at the final stage -/

theorem lsrcAt_genSemGen (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) :
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    lsrcAt g.d (extBOf Q g i bools bits Sst) (extOf Q g i bools bits Sst) Sst =
      (SemPkg.gen (genSemGen Q X g)).lsrc i bools bits := rfl

theorem ext_mem_final (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = .mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]) (hwf : GenWF g.d = true) (hok : g.d.ok = true) :
    extOf Q g i bools bits S (kDOf g.d + k) dw =
      Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l0 j)⟩
        ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l1 j)⟩
        ⟨fun j => lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l2 j != 0⟩
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l3 j)⟩ := by
  have hkn : k < g.d.shape.insts.length := by
    rcases Nat.lt_or_ge k g.d.shape.insts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  have hwf' : RowA g.d = true ∧ RowB g.d = true ∧ RowC g.d = true := by
    unfold GenWF at hwf
    simp only [Bool.and_eq_true] at hwf
    exact ⟨hwf.1.1, hwf.1.2, hwf.2⟩
  have hC := rowC_at g.d hwf'.2.2 k hkn
  -- position `kD + k` of the final stage is its value at stage `k + 1`
  have hagree := ExtStage_agree Q g i bools bits S (n := k + 1) (m := g.d.shape.insts.length) hkn
    (kDOf g.d + k) (by omega)
  have hval := callOut_mem_val Q g i S k (ExtStage Q g i bools bits S k) cb aw dw l0 l1 l2 l3 c a κ hk ho ha
  have hv1 : extOf Q g i bools bits S (kDOf g.d + k) dw =
      memOut g cb aw dw l0 l1 l2 l3 i S (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 := by
    show (ExtStage Q g i bools bits S g.d.shape.insts.length).2 (kDOf g.d + k) dw = _
    rw [(hagree.2 dw), ExtStage_succ, hval]
  rw [hv1]
  -- the four argument lets are clean at stage `k`: the observations agree between stage `k` and the final families
  have hagk := fun p (hp : p < kDOf g.d + k) =>
    ExtStage_agree Q g i bools bits S (n := k) (m := g.d.shape.insts.length) (by omega) p (by omega)
  have hl : ∀ l ∈ [l0, l1, l2, l3], ∀ j, lsrcGet (lsrcAt g.d (ExtStage Q g i bools bits S k).1
      (ExtStage Q g i bools bits S k).2 S) l j =
      lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l j := by
    intro l hlm j
    refine lsrcAt_congr g.d hok k _ _ _ _ S j (fun p hp => ?_) (fun p w hp => ?_) l (hC l (by rw [ha]; exact hlm))
    · exact (congrArg (fun s => s.val j) (hagk p hp).1).symm
    · exact (congrArg (fun s => s.val j) ((hagk p hp).2 w)).symm
  unfold memOut
  have e0 := hl l0 (by simp)
  have e1 := hl l1 (by simp)
  have e2 := hl l2 (by simp)
  have e3 := hl l3 (by simp)
  simp only [e0, e1, e2, e3]

theorem memFacts_of_genSem (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hok : g.d.ok = true) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder) (hk : g.d.shape.insts[k]? = some (c, a, κ))
    (cb : Bool) (aw dw : Nat) (ho : originOf g.d k = .mem cb aw dw) :
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    Tools.ShippingMachineCallsLinkedT.MemFacts (D := dom i) g.d.shape
      ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) g.d.ls.length (g.d.bsIn.drop (kDOf g.d)) (kDOf g.d)
      (extOf Q g i bools bits Sst) k c := by
  intro Sst
  have hkn : k < g.d.shape.insts.length := by
    rcases Nat.lt_or_ge k g.d.shape.insts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  have hwf' : RowA g.d = true ∧ RowB g.d = true ∧ RowC g.d = true := by
    have := g.wf
    unfold GenWF at this
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  obtain ⟨hAl, hA4⟩ := rowA_at g.d hwf'.1 k hkn
  have h4 := hA4 cb aw dw ho
  obtain ⟨l0, l1, l2, l3, ha⟩ : ∃ l0 l1 l2 l3, callArgs g.d k = [l0, l1, l2, l3] := by
    match hh : callArgs g.d k, h4 with
    | [l0, l1, l2, l3], _ => exact ⟨l0, l1, l2, l3, rfl⟩
  obtain ⟨hKind, hs0, hs1, hs2, hs3⟩ := rowB_at g.d hwf'.2.1 k hkn cb aw dw l0 l1 l2 l3 ho ha
  have hlt : ∀ l ∈ [l0, l1, l2, l3], l < g.d.ls.length := fun l hl => hAl l (by rw [ha]; exact hl)
  -- the observations are bounded by the sort of the `let`
  have hhl := @Tools.ShippingQuadCalls.letObsB_hl g.d ι dom ⟨g.inits⟩ (fun _ => List (Nat → Nat)) g.inits
    (refBodyE g (extBOf Q g) (extOf Q g)) (extOf Q g) (extBOf Q g) i bools bits
  have hbound : ∀ l s, letSort g.d l = some s → l < g.d.ls.length →
      ∃ v, ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits)[l]? = some v ∧ ∀ τ, v τ < 2 ^ s.width := by
    intro l s hs hl
    have hgl : g.d.ls[l]? = some g.d.ls[l] := List.getElem?_eq_getElem hl
    obtain ⟨v, hv, hvb⟩ := hhl l g.d.ls[l] hgl
    have : g.d.ls[l].1 = s := by
      unfold letSort at hs
      rw [hgl] at hs
      simpa using hs
    rw [this] at hvb
    exact ⟨v, hv, hvb⟩
  have hargs : (g.d.shape.insts.map (·.2.1))[k]? = some [l0, l1, l2, l3] := by
    unfold callArgs at ha
    rw [List.getElem?_map, hk] at ha ⊢
    simpa using ha
  have hbs : ((g.d.bsIn.drop (kDOf g.d))[k]?.map (·.2)) = some (.bits dw) := by
    unfold callKind at hKind
    cases hb : (g.d.bsIn.drop (kDOf g.d))[k]? with
    | none => rw [hb] at hKind; simp at hKind
    | some b => rw [hb] at hKind; simpa using hKind
  have hbits : ∀ (l w : Nat), letSort g.d l = some (.bits w) → l < g.d.ls.length →
      ∃ v, ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits)[l]? = some v ∧
        v = fun j => (BitVec.ofNat w (lsrcGet ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) l j)).toNat := by
    intro l w hs hl
    obtain ⟨v, hv, hvb⟩ := hbound l _ hs hl
    refine ⟨v, hv, ?_⟩
    funext j
    have := hvb j
    simp only [SType.width] at this
    simp [lsrcGet, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
  refine ⟨cb, aw, dw, ⟨fun j => BitVec.ofNat aw (lsrcGet ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) l0 j)⟩,
    ⟨fun j => BitVec.ofNat dw (lsrcGet ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) l1 j)⟩,
    ⟨fun j => lsrcGet ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) l2 j != 0⟩,
    ⟨fun j => BitVec.ofNat aw (lsrcGet ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) l3 j)⟩,
    l0, l1, l2, l3, ?_, hargs, ?_, hlt l0 (by simp), ?_, hlt l1 (by simp), ?_, hlt l2 (by simp), ?_, hlt l3 (by simp),
    hbs, ?_⟩
  · show (originOf g.d k).child? = _
    rw [ho]; rfl
  · obtain ⟨v, hv, hve⟩ := hbits l0 aw hs0 (hlt l0 (by simp)); rw [hv, hve]
  · obtain ⟨v, hv, hve⟩ := hbits l1 dw hs1 (hlt l1 (by simp)); rw [hv, hve]
  · obtain ⟨v, hv, hvb⟩ := hbound l2 .bool hs2 (hlt l2 (by simp))
    rw [hv]
    congr 1
    funext j
    have := hvb j
    simp only [SType.width] at this
    by_cases h : v j = 0
    · simp [lsrcGet, hv, h]
    · have h1 : v j = 1 := by omega
      simp [lsrcGet, hv, h1]
  · obtain ⟨v, hv, hve⟩ := hbits l3 aw hs3 (hlt l3 (by simp)); rw [hv, hve]
  · intro j
    exact congrArg (fun s => s.val j)
      (ext_mem_final Q g i bools bits Sst k cb aw dw l0 l1 l2 l3 c a κ hk ho ha g.wf hok)

end Tools.ShippingGen5Sem
