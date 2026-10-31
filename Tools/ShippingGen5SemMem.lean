import Tools.ShippingGen5SemCongr
set_option autoImplicit false
-- NOT BUILT (g5sm-u4, work in progress)
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

end Tools.ShippingGen5Sem
