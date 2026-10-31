import Tools.ShippingGen5SemMem
set_option autoImplicit false
-- NOT BUILT (U5A-D of scripts/gen5/DG_SEM_FREEZE_P4E.md rev2; Pod build result is recorded by a comment-only commit). No sorry/axiom/native_decide.
/-! # DG-SEM U5A-U5D (scripts/gen5/DG_SEM_FREEZE_P4E.md §2, rev2 §5)

U5A the stage value of an ordinary call, U5B stage-independence of the `calleeOut` read and the final families at
`kDOf g.d + k`, U5C/U5D `calleeOut` as the callee's `src` on the decoded families and the `CallField` index selection.
All results are conditional on their stated hypotheses. Nothing here supplies `GenWF`/`d.ok` coverage of a real run,
`hq`/`hp` (callee package / `GenIn` of a run), causality, `GenExtAtCall` for a package (U5E, not here), `dataOf`, ACC, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## U5A -/

theorem callOut_bool_val (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bool) :
    (callOut Q g i S k st).1 (kDOf g.d + k) = ⟨fun τ => calleeOut Q g i S st.1 st.2 k τ != 0⟩ := by
  unfold callOut
  rw [hk]
  dsimp only
  split
  · rename_i cb aw dw h
    exact absurd h (hno cb aw dw)
  · unfold withCall
    rw [hκ]
    simp

theorem callOut_bits_val (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bits w) :
    (callOut Q g i S k st).2 (kDOf g.d + k) w = ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S st.1 st.2 k τ)⟩ := by
  unfold callOut
  rw [hk]
  dsimp only
  split
  · rename_i cb aw dw h
    exact absurd h (hno cb aw dw)
  · unfold withCall
    rw [hκ]
    simp

/-! ## U5B -/

theorem calleeOut_congr (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (h : ∀ l ∈ callArgs g.d k, ∀ j, lsrcGet (lsrcAt g.d bs vs S) l j = lsrcGet (lsrcAt g.d bs' vs' S) l j) :
    calleeOut Q g i S bs vs k = calleeOut Q g i S bs' vs' k := by
  have hv : Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k) =
      Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs' vs' S) (callArgs g.d k) := by
    funext τ
    unfold Tools.ShippingMachineCallsLinkedT.valsOf
    refine List.map_congr_left fun l hl => ?_
    have := h l hl τ
    unfold lsrcGet at this
    exact this
  unfold calleeOut
  simp only [hv]

theorem calleeOut_final (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (hkn : k < g.d.shape.insts.length) :
    calleeOut Q g i S (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 k =
      calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k := by
  have hwf' : RowA g.d = true ∧ RowB g.d = true ∧ RowC g.d = true := by
    have := g.wf
    unfold GenWF at this
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hC := rowC_at g.d hwf'.2.2 k hkn
  have hagk := fun p (hp : p < kDOf g.d + k) =>
    ExtStage_agree Q g i bools bits S (n := k) (m := g.d.shape.insts.length) (by omega) p (by omega)
  refine calleeOut_congr Q g i S _ _ _ _ k fun l hl j => ?_
  refine lsrcAt_congr g.d g.ok k _ _ _ _ S j (fun p hp => ?_) (fun p w hp => ?_) l (hC l hl)
  · exact (congrArg (fun s => s.val j) (hagk p hp).1).symm
  · exact (congrArg (fun s => s.val j) ((hagk p hp).2 w)).symm

theorem ext_call_final_bool (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bool) :
    extBOf Q g i bools bits S (kDOf g.d + k) =
      ⟨fun τ => calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ != 0⟩ := by
  have hkn : k < g.d.shape.insts.length := by
    rcases Nat.lt_or_ge k g.d.shape.insts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  have hagree := ExtStage_agree Q g i bools bits S (n := k + 1) (m := g.d.shape.insts.length) hkn
    (kDOf g.d + k) (by omega)
  have hval := callOut_bool_val Q g i S k (ExtStage Q g i bools bits S k) c a κ hk hno hκ
  have hfin := calleeOut_final Q g i bools bits S k hkn
  show (ExtStage Q g i bools bits S g.d.shape.insts.length).1 (kDOf g.d + k) = _
  rw [hagree.1, ExtStage_succ, hval, hfin]

theorem ext_call_final_bits (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bits w) :
    extOf Q g i bools bits S (kDOf g.d + k) w =
      ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ)⟩ := by
  have hkn : k < g.d.shape.insts.length := by
    rcases Nat.lt_or_ge k g.d.shape.insts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  have hagree := ExtStage_agree Q g i bools bits S (n := k + 1) (m := g.d.shape.insts.length) hkn
    (kDOf g.d + k) (by omega)
  have hval := callOut_bits_val Q g i S k (ExtStage Q g i bools bits S k) c a κ w hk hno hκ
  have hfin := calleeOut_final Q g i bools bits S k hkn
  show (ExtStage Q g i bools bits S g.d.shape.insts.length).2 (kDOf g.d + k) w = _
  rw [hagree.2 w, ExtStage_succ, hval, hfin]

/-! ## U5C / U5D -/

theorem callArgs_of_insts (d : MachineData) (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : d.shape.insts[k]? = some (c, a, κ)) : callArgs d k = a := by
  unfold callArgs
  simp [List.getElem?_map, hk]

theorem calleeOut_eq_src (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (c : Name) (a : List Nat) (κ : MixedGateBinder) (q : SemPkg ι dom) (k' : Nat) (f : Nat → Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hQ : Q c = some q) (hsel : selIdx g.d q k = some k')
    (hf : (q.src i (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a))
                  (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a)))[k']? = some f) :
    calleeOut Q g i S bs vs k = f := by
  unfold calleeOut
  rw [hk]
  dsimp only
  rw [hQ]
  dsimp only
  rw [hsel]
  dsimp only
  rw [callArgs_of_insts g.d k c a κ hk, hf]
  rfl

theorem outs_findIdx_nodup (l : List Sparkle.IR.Machine.OutField) (n : String) (k' : Nat)
    (o : Sparkle.IR.Machine.OutField) (hnd : (l.map (·.name)).Nodup) (ho : l[k']? = some o)
    (hn : o.name = n) : l.findIdx? (·.name = n) = some k' := by
  induction l generalizing k' with
  | nil => simp at ho
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    cases k' with
    | zero =>
      simp at ho
      subst ho
      simp [List.findIdx?_cons, hn]
    | succ k'' =>
      simp only [List.getElem?_cons_succ] at ho
      have hxn : ¬ x.name = n := by
        intro hx
        apply hnd.1
        rw [List.mem_map]
        exact ⟨o, List.mem_iff_getElem?.mpr ⟨k'', ho⟩, by rw [hn, hx]⟩
      rw [List.findIdx?_cons]
      simp [hxn, ih k'' hnd.2 ho]

theorem selIdx_of_callField (d : MachineData) (q : SemPkg ι dom) (k k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (ho : q.d.shape.layout.outs[k']? = some o)
    (hcf : if d.shape.instFields = [] then q.d.shape.layout.outs = [o] else o.name = d.shape.instFields.getD k "")
    (hnd : d.shape.instFields ≠ [] → (q.d.shape.layout.outs.map (·.name)).Nodup) :
    selIdx d q k = some k' := by
  unfold selIdx
  by_cases h1 : d.shape.instFields = []
  · rw [if_pos h1] at hcf ⊢
    rw [hcf] at ho ⊢
    have hk0 : k' = 0 := by
      cases k' with
      | zero => rfl
      | succ n => simp at ho
    subst hk0
    simp
  · rw [if_neg h1] at hcf ⊢
    exact outs_findIdx_nodup _ _ k' o (hnd h1) ho hcf

end Tools.ShippingGen5Sem
