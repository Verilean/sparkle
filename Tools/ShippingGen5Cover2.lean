import Tools.ShippingGen5Cover
set_option autoImplicit false
-- Built in g5cv-r4 at f921375b (Pod `kjob lake build`, exit 0; Cover2Check: TYPE 10, MUTANT 5, AXIOMS standard, CLOSURE OK with 3 negative / 2 clean controls). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-COVER rev2 preservation lemmas and range suppliers, `scripts/gen5/DG_COVER_FREEZE_REV2.md` §1.2, §2.2

The statements `CallOrderInv` (with `ArgsExist`), `PushInstPreserves`, `PushLetPreserves`, `PhInRange` are the freeze rev2 texts (same text as
`Tests/Gen5/CoverNegCheck.lean`, which is not imported because it is a test). Here `PushInstPreserves` and `PushLetPreserves` are **proved**, and the
range clauses of `PhInRange` for the *let* and *instance* placeholders are supplied from `CallOrderInv`.

Not supplied here: the reader-side fact that the actual reader steps are pushes of the premise shape (fuel-twin induction); `ReadsOfQuoteStmt`; the slot and
input clauses of `PhInRange`; write/result expressions; Q-cmp / Q-snd / Q-wit. Nothing here concerns a run, `dataOf`, `GenWF` on real data, M5 or FG. -/

namespace Tools.ShippingGen5Cover2
open Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge

/-! ## Definitions (freeze rev1 §2.4 / rev2 §1.2, §2.2) -/

def MentionsPh (tag : String) (i : Nat) : Lean.Expr → Prop
  | .fvar ⟨.num (.str .anonymous t) j⟩ => t = tag ∧ j = i
  | .app f a => MentionsPh tag i f ∨ MentionsPh tag i a
  | .lam _ t b _ => MentionsPh tag i t ∨ MentionsPh tag i b
  | .forallE _ t b _ => MentionsPh tag i t ∨ MentionsPh tag i b
  | _ => False

abbrev MentionsLet (i : Nat) (e : Lean.Expr) : Prop := MentionsPh "_machLet" i e
abbrev MentionsInst (i : Nat) (e : Lean.Expr) : Prop := MentionsPh "_machInst" i e

def LetEdge (lets : MachLets) (a i : Nat) : Prop :=
  ∃ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[a]? = some (nm, kd, v) ∧ MentionsLet i v

inductive LetReach (lets : MachLets) : Nat → Nat → Prop
  | refl (a : Nat) : LetReach lets a a
  | step {a i j : Nat} : LetEdge lets a i → LetReach lets i j → LetReach lets a j

def LetValuesEarlier (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsLet i v → i < j

def LetsInstRange (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ m, MentionsInst m v → m < st.insts.size

def ArgsInstBounded (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ i, LetReach st.lets a i →
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[i]? = some (nm, kd, v) → ∀ m, MentionsInst m v → m < k

def ArgsExist (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, a < st.lets.size

def CallOrderInv (st : MachRead) : Prop :=
  LetValuesEarlier st ∧ LetsInstRange st ∧ ArgsExist st ∧ ArgsInstBounded st

def PushInstPreserves : Prop :=
  ∀ (st st' : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder),
    CallOrderInv st → (∀ a ∈ js, a < st.lets.size) →
    st' = { st with insts := st.insts.push (c, js, r) } → CallOrderInv st'

def PushLetPreserves : Prop :=
  ∀ (st st' : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
    CallOrderInv st → (∀ i, MentionsLet i v → i < st.lets.size) → (∀ m, MentionsInst m v → m < st.insts.size) →
    st' = { st with lets := st.lets.push (nm, kd, v) } → CallOrderInv st'

def PhInRange (nDecl kI n k : Nat) (v : Lean.Expr) : Prop :=
  (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
  (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k)

/-! ## Empty state -/

theorem callOrderInv_of_empty (st : MachRead) (hl : st.lets = #[]) (hi : st.insts = #[]) : CallOrderInv st := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j nm kd v h; simp [hl] at h
  · intro j nm kd v h; simp [hl] at h
  · intro k c js r h; simp [hi] at h
  · intro k c js r h; simp [hi] at h

/-! ## PushInst -/

theorem pushInst_preserves : PushInstPreserves := by
  intro st st' c js r ⟨hE, hR, hX, hB⟩ hjs hst
  subst hst
  refine ⟨hE, ?_, ?_, ?_⟩
  · intro j nm kd v h m hm
    have := hR j nm kd v h m hm
    simp only [Array.size_push]
    omega
  · intro k c' js' r' h a ha
    simp only [Array.getElem?_push] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact hjs a ha
    · exact hX k c' js' r' h a ha
  · intro k c' js' r' h a ha i hr nm kd v hv m hm
    simp only [Array.getElem?_push] at h
    split at h
    · rename_i hk
      have := hR i nm kd v hv m hm
      omega
    · exact hB k c' js' r' h a ha i hr nm kd v hv m hm

/-! ## PushLet -/

/-- Reachability in `lets.push x` from an index that already existed stays inside `lets` (needs `LetValuesEarlier`). -/
theorem letReach_push (lets : MachLets) (x : Name × MixedGateBinder × Lean.Expr)
    (hE : ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[j]? = some (nm, kd, v) → ∀ i, MentionsLet i v → i < j)
    {a i : Nat} (h : LetReach (lets.push x) a i) : a < lets.size → LetReach lets a i := by
  induction h with
  | refl a => intro _; exact LetReach.refl a
  | @step a i j he _ ih =>
    intro ha
    obtain ⟨nm, kd, v, hl, hm⟩ := he
    have hl' : lets[a]? = some (nm, kd, v) := by
      rw [Array.getElem?_push] at hl
      split at hl
      · omega
      · exact hl
    have hia : i < a := hE a nm kd v hl' i hm
    exact LetReach.step ⟨nm, kd, v, hl', hm⟩ (ih (by omega))

theorem letReach_lt (lets : MachLets)
    (hE : ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[j]? = some (nm, kd, v) → ∀ i, MentionsLet i v → i < j)
    {a i : Nat} (h : LetReach lets a i) : a < lets.size → i < lets.size := by
  induction h with
  | refl a => exact id
  | @step a i j he _ ih =>
    intro ha
    obtain ⟨nm, kd, v, hl, hm⟩ := he
    exact ih (Nat.lt_trans (hE a nm kd v hl i hm) ha)

theorem pushLet_preserves : PushLetPreserves := by
  intro st st' nm kd v ⟨hE, hR, hX, hB⟩ hvl hvi hst
  subst hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j nm' kd' v' h i hi
    simp only [Array.getElem?_push] at h
    split at h
    · rename_i hj
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      rw [hj]
      exact hvl i hi
    · exact hE j nm' kd' v' h i hi
  · intro j nm' kd' v' h m hm
    simp only [Array.getElem?_push] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact hvi m hm
    · exact hR j nm' kd' v' h m hm
  · intro k c js r h a ha
    have := hX k c js r h a ha
    simp only [Array.size_push]
    omega
  · intro k c js r h a ha i hr nm' kd' v' hv m hm
    have hr' : LetReach st.lets a i := letReach_push st.lets (nm, kd, v) hE hr (hX k c js r h a ha)
    have hi : i < st.lets.size := letReach_lt st.lets hE hr' (hX k c js r h a ha)
    have hv1 : st.lets[i]? = some (nm', kd', v') := by
      simp only [Array.getElem?_push] at hv
      split at hv
      · omega
      · exact hv
    exact hB k c js r h a ha i hr' nm' kd' v' hv1 m hm

/-! ## Range suppliers (let and instance clauses of `PhInRange`) -/

theorem letPh_lt_of_inv (st : MachRead) (h : CallOrderInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
    (hj : st.lets[j]? = some (nm, kd, v)) {k : Nat} (hk : j ≤ k) : ∀ i, MentionsPh "_machLet" i v → i < k := by
  intro i hi
  have := h.1 j nm kd v hj i hi
  omega

theorem instPh_lt_of_inv (st : MachRead) (h : CallOrderInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
    (hj : st.lets[j]? = some (nm, kd, v)) {kI : Nat} (hk : st.insts.size ≤ kI) : ∀ m, MentionsPh "_machInst" m v → m < kI := by
  intro m hm
  have := h.2.1 j nm kd v hj m hm
  omega

/-- The let and instance clauses of `PhInRange` for the value of let `j`; the input and slot clauses are hypotheses (no supplier in this file). -/
theorem phInRange_of_inv (st : MachRead) (h : CallOrderInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
    (hj : st.lets[j]? = some (nm, kd, v)) {nDecl kI n k : Nat} (hk : j ≤ k) (hkI : st.insts.size ≤ kI)
    (hin : ∀ i, MentionsPh "_machIn" i v → i < nDecl) (hsl : ∀ i, MentionsPh "_machSlot" i v → i < n) :
    PhInRange nDecl kI n k v :=
  ⟨hin, instPh_lt_of_inv st h hj hkI, hsl, letPh_lt_of_inv st h hj hk⟩

theorem phInRange_mono {nDecl kI n k nDecl' kI' n' k' : Nat} {v : Lean.Expr}
    (h : PhInRange nDecl kI n k v) (h1 : nDecl ≤ nDecl') (h2 : kI ≤ kI') (h3 : n ≤ n') (h4 : k ≤ k') :
    PhInRange nDecl' kI' n' k' v :=
  ⟨fun i hi => Nat.lt_of_lt_of_le (h.1 i hi) h1, fun i hi => Nat.lt_of_lt_of_le (h.2.1 i hi) h2,
   fun i hi => Nat.lt_of_lt_of_le (h.2.2.1 i hi) h3, fun i hi => Nat.lt_of_lt_of_le (h.2.2.2 i hi) h4⟩

/-! ## Reachability by pushes -/

/-- One push step of the shape the preservation lemmas assume. -/
inductive PushStep : MachRead → MachRead → Prop
  | inst (st : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder) :
      (∀ a ∈ js, a < st.lets.size) → PushStep st { st with insts := st.insts.push (c, js, r) }
  | letv (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr) :
      (∀ i, MentionsLet i v → i < st.lets.size) → (∀ m, MentionsInst m v → m < st.insts.size) →
      PushStep st { st with lets := st.lets.push (nm, kd, v) }

/-- Reflexive-transitive closure of `PushStep`. -/
inductive PushReach : MachRead → MachRead → Prop
  | refl (st : MachRead) : PushReach st st
  | tail {a b c : MachRead} : PushReach a b → PushStep b c → PushReach a c

theorem callOrderInv_of_steps {st0 st : MachRead} (h0 : CallOrderInv st0) (h : PushReach st0 st) : CallOrderInv st := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    cases hs with
    | inst c js r hj => exact pushInst_preserves _ _ c js r ih hj rfl
    | letv nm kd v hl hi => exact pushLet_preserves _ _ nm kd v ih hl hi rfl

end Tools.ShippingGen5Cover2
