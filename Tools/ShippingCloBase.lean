import Tools.ShippingLetsReaderInv

/-! # Unit LCQ2 (base): the closedness predicate `Clo`, the state invariant `CloSt`, the let-binding lemmas

BUILT: see the header of `Tools/ShippingCloInv.lean` (run names and exits). No `sorry`, no axiom, no `native_decide`.

`Clo d e`: every loose bound variable of `e` has index below `d` PLUS the binders crossed (`bvar j` needs
`j < d` at depth `d`; under a binder the depth grows).  So `Clo 0 e` says `e` has no loose `bvar` at all.
Unlike `LetOk` this predicate does not depend on the size of the `let` table and the reader needs NO input
condition for it: an input `bvar` outside the environment is replaced by `machIn`, an environment value is
a result of the reader itself.

The reader invariant is `CloSt st` (every `let` value, every nested machine's saved result and the domain are
`Clo 0`) + `EnvClo env` (every converted value of the environment is `Clo 0`); the lemmas here are the pure
parts: spines/arrays (copies of the `LetOk` ones), the `let`-binding helpers `machBindLet` / `machBindLetNamed` /
`machBindLetAlias` / `machLetIndex`, `machProjIota`. -/
namespace Tools.ShippingCloInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
open Tools.ShippingReaderMatcherArity Tools.ShippingReaderMatcherArityArray

/-- No loose bound variable of `e` escapes `d` enclosing binders. -/
def Clo : Nat → Lean.Expr → Bool
  | d, .bvar j => decide (j < d)
  | d, .app f a => Clo d f && Clo d a
  | d, .lam _ t b _ => Clo d t && Clo (d + 1) b
  | d, .forallE _ t b _ => Clo d t && Clo (d + 1) b
  | d, .letE _ t v b _ => Clo d t && Clo d v && Clo (d + 1) b
  | d, .mdata _ e => Clo d e
  | d, .proj _ _ e => Clo d e
  | _, _ => true

theorem clo_mono : ∀ (e : Lean.Expr) {d d' : Nat}, d ≤ d' → Clo d e = true → Clo d' e = true
  | .bvar j, d, d', h, he => by
    simp only [Clo, decide_eq_true_eq] at he ⊢
    omega
  | .fvar _, _, _, _, _ => rfl
  | .mvar _, _, _, _, _ => rfl
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .lit _, _, _, _, _ => rfl
  | .app f a, d, d', h, he => by
    simp only [Clo, Bool.and_eq_true] at he ⊢
    exact ⟨clo_mono f h he.1, clo_mono a h he.2⟩
  | .lam _ t b _, d, d', h, he => by
    simp only [Clo, Bool.and_eq_true] at he ⊢
    exact ⟨clo_mono t h he.1, clo_mono b (Nat.succ_le_succ h) he.2⟩
  | .forallE _ t b _, d, d', h, he => by
    simp only [Clo, Bool.and_eq_true] at he ⊢
    exact ⟨clo_mono t h he.1, clo_mono b (Nat.succ_le_succ h) he.2⟩
  | .letE _ t v b _, d, d', h, he => by
    simp only [Clo, Bool.and_eq_true] at he ⊢
    exact ⟨⟨clo_mono t h he.1.1, clo_mono v h he.1.2⟩, clo_mono b (Nat.succ_le_succ h) he.2⟩
  | .mdata _ e, d, d', h, he => by
    simp only [Clo] at he ⊢
    exact clo_mono e h he
  | .proj _ _ e, d, d', h, he => by
    simp only [Clo] at he ⊢
    exact clo_mono e h he

theorem clo_zero {d : Nat} {e : Lean.Expr} (h : Clo 0 e = true) : Clo d e = true :=
  clo_mono e (Nat.zero_le d) h

theorem clo_app {d : Nat} {f a : Lean.Expr} :
    Clo d (.app f a) = true ↔ Clo d f = true ∧ Clo d a = true := by
  simp [Clo]

theorem clo_slot (d i : Nat) : Clo d (machSlot i) = true := rfl
theorem clo_in (d i : Nat) : Clo d (machIn i) = true := rfl
theorem clo_inst (d i : Nat) : Clo d (machInstOut i) = true := rfl
theorem clo_machLet (d i : Nat) : Clo d (machLet i) = true := rfl

theorem clo_natLit (d k : Nat) : Clo d (inlNatLit k) = true := by
  simp [Clo, inlNatLit, mkApp3, mkApp, mkAppB]

/-! ## Spines and arrays (copies of the `Clo` ones) -/

theorem clo_spine (d : Nat) (e : Lean.Expr) : ∀ (acc : List Lean.Expr), Clo d e = true →
    (∀ a ∈ acc, Clo d a = true) →
    Clo d (inlSpine e acc).1 = true ∧ ∀ a ∈ (inlSpine e acc).2, Clo d a = true := by
  induction e with
  | app f a ihf iha =>
    intro acc he hacc
    simp only [Clo, Bool.and_eq_true] at he
    have := ihf (a :: acc) he.1 (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he.2
      · exact hacc x hx)
    simpa only [inlSpine] using this
  | _ =>
    intro acc he hacc
    simp only [inlSpine]
    exact ⟨he, hacc⟩

theorem clo_headT (d : Nat) : ∀ e : Lean.Expr, Clo d e = true → Clo d (headT e) = true
  | .app f a, he => by
    simp only [Clo, Bool.and_eq_true] at he
    simpa only [headT] using clo_headT d f he.1
  | .bvar _, he => he
  | .fvar _, he => he
  | .mvar _, he => he
  | .sort _, he => he
  | .const _ _, he => he
  | .lit _, he => he
  | .lam _ _ _ _, he => he
  | .forallE _ _ _ _, he => he
  | .letE _ _ _ _ _, he => he
  | .mdata _ _, he => he
  | .proj _ _ _, he => he

theorem clo_argsAcc (d : Nat) : ∀ (e : Lean.Expr) (acc : List Lean.Expr), Clo d e = true →
    (∀ a ∈ acc, Clo d a = true) → ∀ a ∈ argsAcc e acc, Clo d a = true
  | .app f a, acc, he, hacc => by
    simp only [Clo, Bool.and_eq_true] at he
    refine clo_argsAcc d f (a :: acc) he.1 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.2
    · exact hacc x hx
  | .bvar _, _, _, hacc => hacc
  | .fvar _, _, _, hacc => hacc
  | .mvar _, _, _, hacc => hacc
  | .sort _, _, _, hacc => hacc
  | .const _ _, _, _, hacc => hacc
  | .lit _, _, _, hacc => hacc
  | .lam _ _ _ _, _, _, hacc => hacc
  | .forallE _ _ _ _, _, _, hacc => hacc
  | .letE _ _ _ _ _, _, _, hacc => hacc
  | .mdata _ _, _, _, hacc => hacc
  | .proj _ _ _, _, _, hacc => hacc

theorem clo_getAppFn {d : Nat} {e : Lean.Expr} (he : Clo d e = true) :
    Clo d e.getAppFn = true := by
  rw [← headT_eq_getAppFn]
  exact clo_headT d e he

theorem clo_getAppArgs {d : Nat} {e : Lean.Expr} (he : Clo d e = true) :
    ∀ a ∈ e.getAppArgs, Clo d a = true := by
  intro a ha
  rw [getAppArgs_eq] at ha
  exact clo_argsAcc d e [] he (by simp) a (Array.mem_toArray.mp ha)

theorem clo_foldl_app {d : Nat} : ∀ (l : List Lean.Expr) (f : Lean.Expr), Clo d f = true →
    (∀ a ∈ l, Clo d a = true) → Clo d (l.foldl Lean.Expr.app f) = true
  | [], _, hf, _ => hf
  | a :: l, f, hf, hl => by
    refine clo_foldl_app l (.app f a) ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [Clo, Bool.and_eq_true]
    exact ⟨hf, hl a List.mem_cons_self⟩

theorem clo_mkAppN {d : Nat} {f : Lean.Expr} {as : Array Lean.Expr} (hf : Clo d f = true)
    (has : ∀ a ∈ as, Clo d a = true) : Clo d (mkAppN f as) = true := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  exact clo_foldl_app as.toList f hf (fun a ha => has a (Array.mem_toList_iff.mp ha))

/-- The out-of-range default of `a[i]!`. -/
theorem clo_getElem! {d : Nat} {a : Array Lean.Expr} (h : ∀ x ∈ a, Clo d x = true) (i : Nat) :
    Clo d a[i]! = true := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]
    exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]
    rfl


/-! ## `machProjIota` (copy of `projIota_ok`) -/

theorem clo_getD {d : Nat} {e : Lean.Expr} {o : Option Lean.Expr} (he : Clo d e = true)
    (ho : ∀ x, o = some x → Clo d x = true) : Clo d (o.getD e) = true := by
  cases o with
  | none => exact he
  | some x => exact ho x rfl

theorem projIota_clo (projs : Name → Option (Name × Nat × Nat)) (d : Nat) (e : Lean.Expr)
    (he : Clo d e = true) : Clo d (machProjIota projs e) = true := by
  have hs := clo_spine d e [] he (by simp)
  unfold machProjIota
  split
  · rename_i heq0
    rw [heq0] at hs
    dsimp only at hs
    split
    · rename_i r _ hq
      split
      · have hrm := List.mem_of_getLast? hq
        have hrok : Clo d r = true := hs.2 r hrm
        have hs2 := clo_spine d r [] hrok (by simp)
        split
        · rename_i heq2
          rw [heq2] at hs2
          dsimp only at hs2
          split
          · exact clo_getD he (fun x hx => hs2.2 x (List.mem_of_getElem? hx))
          · exact he
        · exact he
      · exact he
    · exact he
  · exact he


/-! ## The reader state and the environment -/

/-- Every `let` value is closed. -/
def LetsClo (lets : MachLets) : Prop := ∀ l ∈ lets.toList, Clo 0 l.2.2 = true

/-- **The state invariant**: the `let` values, the saved results of the nested machines and the domain are
closed (`Clo 0`: no loose bound variable). -/
def CloSt (st : MachRead) : Prop :=
  LetsClo st.lets ∧
  (∀ x ∈ st.nested.toList, Clo 0 x.2.2.2.2.2 = true) ∧
  (∀ d, st.dom = some d → Clo 0 d = true)

/-- Every converted value the environment holds is closed. -/
def EnvClo (env : List MachVal) : Prop := ∀ v, MachVal.val v ∈ env → Clo 0 v = true

theorem envClo_cons {env : List MachVal} {x : MachVal} (H : EnvClo env)
    (hx : ∀ v, x = MachVal.val v → Clo 0 v = true) : EnvClo (x :: env) := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · exact hx v h.symm
  · exact H v h

/-- A machine value is closed. -/
def MvClo : MachVal → Prop
  | .val e => Clo 0 e = true
  | _ => True

theorem cloSt_init : CloSt ({} : MachRead) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp at hx
  · intro x hx
    simp at hx
  · intro d hd
    cases hd

theorem cloSt_congr {st st' : MachRead} (H : CloSt st) (h1 : st'.lets = st.lets)
    (h2 : st'.nested = st.nested) (h3 : st'.dom = st.dom) : CloSt st' := by
  obtain ⟨a, b, c⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact a
  · rw [h2]; exact b
  · rw [h3]; exact c

theorem cloSt_lets {st st' : MachRead} (H : CloSt st) (hl : LetsClo st'.lets)
    (h2 : st'.nested = st.nested) (h3 : st'.dom = st.dom) : CloSt st' := by
  obtain ⟨_, b, c⟩ := H
  exact ⟨hl, by rw [h2]; exact b, by rw [h3]; exact c⟩

theorem cloSt_dom {st st' : MachRead} (H : CloSt st) (h1 : st'.lets = st.lets)
    (h2 : st'.nested = st.nested) {d : Lean.Expr} (h3 : st'.dom = some d)
    (hd : Clo 0 d = true) : CloSt st' := by
  obtain ⟨a, b, _⟩ := H
  refine ⟨by rw [h1]; exact a, by rw [h2]; exact b, ?_⟩
  rw [h3]
  intro d' hd'
  cases hd'
  exact hd

theorem cloSt_nested {st st' : MachRead} (H : CloSt st) (h1 : st'.lets = st.lets)
    (h3 : st'.dom = st.dom)
    {e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr}
    (h2 : st'.nested = st.nested.push e) (he : Clo 0 e.2.2.2.2.2 = true) : CloSt st' := by
  obtain ⟨a, b, c⟩ := H
  refine ⟨by rw [h1]; exact a, ?_, by rw [h3]; exact c⟩
  rw [h2, Array.toList_push]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact b x hx
  · rw [List.mem_singleton.mp hx]; exact he

/-! ## The let-binding helpers keep the table closed -/

theorem letsClo_push {lets : MachLets} {nm : Name} {k : MixedGateBinder} {v : Lean.Expr}
    (H : LetsClo lets) (hv : Clo 0 v = true) : LetsClo (lets.push (nm, k, v)) := by
  intro l hl
  rw [Array.toList_push] at hl
  rcases List.mem_append.mp hl with hl | hl
  · exact H l hl
  · rw [List.mem_singleton.mp hl]; exact hv

theorem machBindLetNamed_clo {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (H : LetsClo lets) (hv : Clo 0 v' = true) :
    LetsClo (machBindLetNamed nm ty v' lets).2 ∧ Clo 0 (machBindLetNamed nm ty v' lets).1 = true := by
  unfold machBindLetNamed
  split
  · exact ⟨H, hv⟩
  · exact ⟨H, hv⟩
  · split
    · exact ⟨H, clo_machLet _ _⟩
    · exact ⟨letsClo_push H hv, clo_machLet _ _⟩

theorem machBindLet_clo {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (H : LetsClo lets) (hv : Clo 0 v' = true) :
    LetsClo (machBindLet nm ty v' lets).2 ∧ Clo 0 (machBindLet nm ty v' lets).1 = true := by
  unfold machBindLet
  split
  · exact ⟨H, hv⟩
  · exact ⟨H, hv⟩
  · split
    · exact ⟨H, hv⟩
    · split
      · exact ⟨H, clo_machLet _ _⟩
      · exact ⟨letsClo_push H hv, clo_machLet _ _⟩

/-- The `resolve` of `machBindLetAlias` only ever returns the value or a stored (closed) `let` value. -/
theorem resolve_clo (lets : MachLets) (H : LetsClo lets) :
    ∀ (fuel : Nat) (e : Lean.Expr), Clo 0 e = true →
      Clo 0 (machBindLetAlias.resolve lets fuel e) = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro e he
    unfold machBindLetAlias.resolve
    split
    · exact he
    · split
      · rename_i a b v hget
        have hmem : (a, b, v) ∈ lets.toList := by
          obtain ⟨hj, hx⟩ := getElem?_eq_some_iff.mp hget
          rw [← hx]
          exact Array.mem_toList_iff.mpr (Array.getElem_mem hj)
        exact ih _ (by omega) v (H _ hmem)
      · exact he
    · exact he

theorem machBindLetAlias_clo {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (H : LetsClo lets) (hv : Clo 0 v' = true) :
    LetsClo (machBindLetAlias nm ty v' lets).2 ∧ Clo 0 (machBindLetAlias nm ty v' lets).1 = true := by
  unfold machBindLetAlias
  by_cases hc : machIsLetVar (machBindLetAlias.resolve lets lets.size v') = true
  · rw [if_pos hc]
    exact machBindLetNamed_clo H hv
  · rw [if_neg hc]
    have hr := resolve_clo lets H lets.size v' hv
    split
    · exact ⟨H, hv⟩
    · exact ⟨H, hv⟩
    · dsimp only
      split
      · exact ⟨H, clo_machLet _ _⟩
      · exact ⟨letsClo_push H hr, clo_machLet _ _⟩

theorem machLetIndex_clo {nm : Name} {k : MixedGateBinder} {v' : Lean.Expr} {lets : MachLets}
    (H : LetsClo lets) (hv : Clo 0 v' = true) : LetsClo (machLetIndex nm k v' lets).2 := by
  unfold machLetIndex
  split
  · exact H
  · split
    · exact H
    · exact letsClo_push H hv

/-- The three-way choice of `machLoopBody`. -/
theorem loopLet_clo {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} (H : LetsClo lets)
    (hv : Clo 0 v' = true) :
    LetsClo (if machIsSlot v' then machBindLetNamed nm ty v' lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' lets
      else machBindLet nm ty v' lets).2 ∧
    Clo 0 (if machIsSlot v' then machBindLetNamed nm ty v' lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' lets
      else machBindLet nm ty v' lets).1 = true := by
  by_cases h1 : machIsSlot v' = true
  · rw [if_pos h1]
    exact machBindLetNamed_clo H hv
  · rw [if_neg h1]
    by_cases h2 : machIsLetVar v' = true
    · rw [if_pos h2]
      exact machBindLetAlias_clo H hv
    · rw [if_neg h2]
      exact machBindLet_clo H hv

end Tools.ShippingCloInv
