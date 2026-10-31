import Tools.ShippingGen5SemExt
import Tools.ShippingMachineMemCausal
-- Pod incremental build (kjob lake build Tools.ShippingGen5SemCausal) exit 0 on this content before commit; the clean issue-linked build is the coder's (not yet run). No sorry/axiom/native_decide.
-- NOT BUILT: no Pod build has run on this file yet; the built SHA goes here by a comment-only commit. No sorry/axiom/native_decide.
/-! # DG-SEM U6A (scripts/gen5/DG_SEM_FREEZE_P6C.md §3): `extCausal_of_genSem`

`SrcCausal`/`CalleesCausal` (DGEN rev2 text), the memory-read causality `memRead_causal`, the stage-wise `ExtStage_causal`
(induction on the stage count, `t` generalized) and `HCausalOf g.d dom (extOf Q g) (extBOf Q g)`.
Conditional on `CalleesCausal Q g.d`. The proof route does not use `g.wf` (a `GenIn` contains it). `hord`-type facts are
not supplied here (the ordinary-callee condition is used only through `ordCallees`). Nothing here supplies `hp`/`hq`/`GenIn`
of a run, `CalleesCausal` for a real table (P10/P11), `GenSFacts`, ACC, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}

def SrcCausal (s : SemPkg ι dom) : Prop :=
  ∀ (i : ι) (A A' : Nat → Signal (dom i) Bool) (B B' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
    (∀ c, c ≤ t → (∀ j, (A j).val c = (A' j).val c) ∧ ∀ j n, (B j n).val c = (B' j n).val c) →
    (s.src i A B).map (fun f => f t) = (s.src i A' B').map (fun f => f t)

def CalleesCausal (Q : Name → Option (SemPkg ι dom)) (d : MachineData) : Prop :=
  ∀ k ∈ ordCallees d, ∀ s, Q (d.shape.insts[k]).1 = some s → SrcCausal s

theorem memRead_causal {D : DomainConfig} {aw dw : Nat} (cb : Bool)
    (A A' : Signal D (BitVec aw)) (Dd Dd' : Signal D (BitVec dw)) (E E' : Signal D Bool) (R R' : Signal D (BitVec aw)) (t : Nat)
    (hA : ∀ c, c ≤ t → A.val c = A'.val c) (hD : ∀ c, c ≤ t → Dd.val c = Dd'.val c)
    (hE : ∀ c, c ≤ t → E.val c = E'.val c) (hR : ∀ c, c ≤ t → R.val c = R'.val c) :
    (Tools.ShippingMachineMemLinked.memRead cb A Dd E R).val t =
      (Tools.ShippingMachineMemLinked.memRead cb A' Dd' E' R').val t := by
  cases cb with
  | true =>
    show (Signal.memoryComboRead A Dd E R).val t = (Signal.memoryComboRead A' Dd' E' R').val t
    rw [Signal.memoryComboRead_val, Signal.memoryComboRead_val,
      Tools.ShippingMachineCausal.memState_congr _ A A' Dd Dd' E E' t (fun c hc =>
        ⟨hA c (Nat.le_of_lt hc), hD c (Nat.le_of_lt hc), hE c (Nat.le_of_lt hc)⟩), hR t (Nat.le_refl t)]
  | false =>
    show (Signal.memory A Dd E R).val t = (Signal.memory A' Dd' E' R').val t
    cases t with
    | zero => rfl
    | succ n =>
      rw [Signal.memory_val_succ, Signal.memory_val_succ,
        Tools.ShippingMachineCausal.memState_congr _ A A' Dd Dd' E E' n (fun c hc =>
          ⟨hA c (by omega), hD c (by omega), hE c (by omega)⟩), hR n (by omega)]

theorem lsrcAt_causal_at (d : MachineData) {D : DomainConfig} (bs bs' : Nat → Signal D Bool)
    (vs vs' : (j n : Nat) → Signal D (BitVec n)) (S S' : Signal D (HList (tys d.ss))) (c : Nat)
    (hS : S.val c = S'.val c) (hb : ∀ p, (bs p).val c = (bs' p).val c)
    (hv : ∀ p w, (vs p w).val c = (vs' p w).val c) (l : Nat) :
    lsrcGet (lsrcAt d bs vs S) l c = lsrcGet (lsrcAt d bs' vs' S') l c := by
  have e1 : (fun p => (bs p).val c) = (fun p => (bs' p).val c) := funext hb
  have e2 : (fun p w => (vs p w).val c) = (fun p w => (vs' p w).val c) := funext fun p => funext fun w => hv p w
  have ht : typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs c (S.val c) =
      typedVal d.nIn d.bpos d.vpos d.ss d.ls bs' vs' c (S'.val c) := by
    unfold typedVal
    rw [hS, e1, e2]
  unfold lsrcGet lsrcAt
  rw [List.getElem?_map, List.getElem?_map]
  cases d.ls[l]? with
  | none => rfl
  | some x => simp only [Option.map_some, Option.getD_some, ht]

theorem getD_apply_congr (l l' : List (Nat → Nat)) (t k' : Nat) (h : l.map (fun f => f t) = l'.map (fun f => f t)) :
    ((l[k']?).getD (fun _ => 0)) t = ((l'[k']?).getD (fun _ => 0)) t := by
  have h2 := congrArg (fun m => m[k']?) h
  simp only [List.getElem?_map] at h2
  cases ha : l[k']? with
  | none =>
    cases hb : l'[k']? with
    | none => rfl
    | some y => rw [ha, hb] at h2; simp at h2
  | some x =>
    cases hb : l'[k']? with
    | none => rw [ha, hb] at h2; simp at h2
    | some y => rw [ha, hb] at h2; simpa using h2

theorem calleeOut_causal (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (S S' : Signal (dom i) (HList (tys g.d.ss)))
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n)) (k t : Nat)
    (hch : (originOf g.d k).child? = none)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c)
    (h : ∀ c, c ≤ t → (∀ p, (bs p).val c = (bs' p).val c) ∧ ∀ p w, (vs p w).val c = (vs' p w).val c) :
    calleeOut Q g i S bs vs k t = calleeOut Q g i S' bs' vs' k t := by
  unfold calleeOut
  cases hk : g.d.shape.insts[k]? with
  | none => rfl
  | some e =>
    obtain ⟨c, a, κ⟩ := e
    dsimp only
    cases hQc : Q c with
    | none => rfl
    | some q =>
      dsimp only
      cases hsel : selIdx g.d q k with
      | none => rfl
      | some k' =>
        dsimp only
        have hn : k < g.d.shape.insts.length := by
          rcases Nat.lt_or_ge k g.d.shape.insts.length with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none h1] at hk; cases hk
        have h2 : g.d.shape.insts[k] = (c, a, κ) := by
          rw [List.getElem?_eq_getElem hn] at hk
          exact Option.some.inj hk
        have hsc : SrcCausal q := hQ ⟨k, hn⟩ ((mem_ordCallees g.d ⟨k, hn⟩).2 hch) q (by simpa [h2] using hQc)
        have hvals : ∀ c', c' ≤ t → Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k) c' =
            Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs' vs' S') (callArgs g.d k) c' := by
          intro c' hc'
          unfold Tools.ShippingMachineCallsLinkedT.valsOf
          refine List.map_congr_left fun l _ => ?_
          have := lsrcAt_causal_at g.d bs bs' vs vs' S S' c' (hS c' hc') (h c' hc').1 (h c' hc').2 l
          unfold lsrcGet at this
          exact this
        have key := hsc i
          (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
            (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)))
          (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
            (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs' vs' S') (callArgs g.d k)))
          (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
            (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)))
          (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
            (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs' vs' S') (callArgs g.d k))) t (fun c' hc' => by
          refine ⟨fun j => ?_, fun j n => ?_⟩
          · show Tools.ShippingMachineChild.decB _ _ j = Tools.ShippingMachineChild.decB _ _ j
            rw [hvals c' hc']
          · show Tools.ShippingMachineChild.decV _ _ j n = Tools.ShippingMachineChild.decV _ _ j n
            rw [hvals c' hc'])
        exact getD_apply_congr _ _ t k' key


theorem withCall_causal (g : GenIn) (i : ι) (k : Nat) (κ : MixedGateBinder) (f f' : Nat → Nat) (t : Nat)
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n))
    (hf : f t = f' t) (hb : ∀ p, (bs p).val t = (bs' p).val t) (hv : ∀ p w, (vs p w).val t = (vs' p w).val t) :
    (∀ p, ((withCall g i k κ f bs vs).1 p).val t = ((withCall g i k κ f' bs' vs').1 p).val t) ∧
    (∀ p w, ((withCall g i k κ f bs vs).2 p w).val t = ((withCall g i k κ f' bs' vs').2 p w).val t) := by
  unfold withCall
  cases κ with
  | bool =>
    refine ⟨fun p => ?_, hv⟩
    by_cases hp : p = kDOf g.d + k
    · simp [hp, hf]
    · simp [hp, hb p]
  | bits w =>
    refine ⟨hb, fun p n => ?_⟩
    by_cases hp : p = kDOf g.d + k
    · simp [hp, hf]
    · simp [hp, hv p n]
  | domain => exact ⟨hb, hv⟩

theorem callOut_causal (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (k t : Nat)
    (st st' : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hS : ∀ c, c ≤ t → S.val c = S'.val c)
    (h : ∀ c, c ≤ t → (∀ p, (st.1 p).val c = (st'.1 p).val c) ∧ ∀ p w, (st.2 p w).val c = (st'.2 p w).val c) :
    (∀ p, ((callOut Q g i S k st).1 p).val t = ((callOut Q g i S' k st').1 p).val t) ∧
    (∀ p w, ((callOut Q g i S k st).2 p w).val t = ((callOut Q g i S' k st').2 p w).val t) := by
  have ht := h t (Nat.le_refl t)
  unfold callOut
  cases hk : g.d.shape.insts[k]? with
  | none => exact ht
  | some e =>
    obtain ⟨c, a, κ⟩ := e
    dsimp only
    cases ho : originOf g.d k with
    | mem cb aw dw =>
      dsimp only
      split
      · refine ⟨ht.1, fun p w => ?_⟩
        by_cases hp : p = kDOf g.d + k
        · by_cases hw : dw = w
          · subst hp hw
            simp only [if_true, dite_true]
            unfold memOut
            have hl := fun c' (hc' : c' ≤ t) =>
              lsrcAt_causal_at g.d st.1 st'.1 st.2 st'.2 S S' c' (hS c' hc') (h c' hc').1 (h c' hc').2
            refine memRead_causal _ _ _ _ _ _ _ _ _ t ?_ ?_ ?_ ?_
            · intro c' hc'; exact congrArg (BitVec.ofNat _) (hl c' hc' _)
            · intro c' hc'; exact congrArg (BitVec.ofNat _) (hl c' hc' _)
            · intro c' hc'; exact congrArg (· != 0) (hl c' hc' _)
            · intro c' hc'; exact congrArg (BitVec.ofNat _) (hl c' hc' _)
          · simp [hp, hw]
        · simp [hp]; exact ht.2 p w
      · exact ht
    | ord =>
      dsimp only
      exact withCall_causal g i k _ _ _ t _ _ _ _
        (calleeOut_causal Q g hQ i S S' _ _ _ _ k t (by rw [ho]; rfl) hS h) ht.1 ht.2
    | field n =>
      dsimp only
      exact withCall_causal g i k _ _ _ t _ _ _ _
        (calleeOut_causal Q g hQ i S S' _ _ _ _ k t (by rw [ho]; rfl) hS h) ht.1 ht.2


theorem ExtStage_causal (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c) :
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools bits S' n).1 p).val t) ∧
    (∀ p w, ((ExtStage Q g i bools bits S n).2 p w).val t = ((ExtStage Q g i bools bits S' n).2 p w).val t) := by
  induction n generalizing t with
  | zero => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    rw [ExtStage_succ, ExtStage_succ]
    exact callOut_causal Q g hQ i S S' n t _ _ hS fun c hc =>
      ih c (fun c' hc' => hS c' (Nat.le_trans hc' hc))

theorem extCausal_of_genSem (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    Tools.ShippingSeqParentLemmas.HCausalOf g.d dom (extOf Q g) (extBOf Q g) := by
  intro i bools bits S S' t hS
  have := ExtStage_causal Q g hQ i bools bits S S' g.d.shape.insts.length t hS
  exact ⟨this.2, this.1⟩

end Tools.ShippingGen5Sem
