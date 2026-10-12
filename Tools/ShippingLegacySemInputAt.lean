import Tools.ShippingLegacySemEntry

/-! # The prepared setup maps the variable of a binder to that binder's value

`sha256Out_done_input` (`Tests/Compiler/LegacySemInstanceTest.lean`) proves,
for ONE binder list and ONE position, that the prepared setup's input map
gives the variable of the field its value — by unfolding three `extend`
steps. Here: the same for any binder list (`.domain` / `.bool` / `.bits n`)
and any position of a non-domain binder.

**Defined here**

* `AtIdx l i a` — the list `l` has `a` at position `i` (a structural
  definition, so that an instance is closed by `rfl` and an induction step by
  a definitional unfolding; no library index lemma is used).
* `kindValue bools bits k x` — the source value of a binder of kind `k`
  bound to the variable `x`: `.bool (bools x)`, `.bits n (bits x n)`; for
  `.domain` a placeholder never used (every statement asks `k ≠ .domain`).
* `kindWidth k` — its width; `kindValue_width`.

**Proved here**

* `extend_frame` — one `extend` step at another variable leaves the two
  input maps at `x` unchanged.
* `prepare_frame` — the same for `prepare` over binders none of whose
  variables is `x`.
* `extend_inputValue` — one `extend` step of a non-domain binder at `x` maps
  `x` to the binder's value.
* `prepare_inputValue` — THE GENERIC INPUT FACT: for DISTINCT variables
  `ids`, a binder `(nm, k)` at position `i` of `bs`, `k ≠ .domain`, and the
  variable `x` at position `i` of `ids`:
  `inputValues (prepare … (bs.zip ids) a).bools (prepare … (bs.zip ids) a).bits x
     = some (kindValue bools bits k x)`, for ANY start `a`.

**Where distinctness is used**: `prepare`'s later steps overwrite the maps at
their own variable; that the binder's entry survives needs the later
variables to differ from `x` (`prepare_frame`). The earlier ones are
irrelevant (the binder's own step overwrites). So `ids.Nodup` is more than
needed (only "x does not occur AFTER position i"), and it is what the
telescope provides (`LamTelescopeND`).

Nothing here reads a compiler definition's program text; `extend` and
`prepare` are the certified entry's pure description of its input walk. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab

/-- The list `l` has `a` at position `i`. -/
def AtIdx {α : Type} : List α → Nat → α → Prop
  | [], _, _ => False
  | a :: _, 0, x => a = x
  | _ :: l, i + 1, x => AtIdx l i x

/-- A position of one list is a position of a list of the same length. -/
theorem AtIdx.transfer {α β : Type} (l : List α) :
    ∀ (l' : List β) (i : Nat) (a : α), l'.length = l.length → AtIdx l i a →
      ∃ b : β, AtIdx l' i b := by
  induction l with
  | nil =>
    intro l' i a _ h
    cases i <;> exact False.elim h
  | cons c l ih =>
    intro l' i a hlen h
    cases l' with
    | nil =>
      first
        | exact absurd (hlen.symm : l.length + 1 = 0) (Nat.succ_ne_zero l.length)
        | (simp at hlen)
    | cons b l' =>
      cases i with
      | zero => exact ⟨b, (rfl : b = b)⟩
      | succ i =>
        have hlen' : l'.length = l.length := by
          first
            | exact Nat.succ.inj hlen
            | exact Nat.add_right_cancel hlen
            | simpa using hlen
        exact ih l' i a hlen' h

/-- The source value of a binder of kind `k` bound to the variable `x`. -/
def kindValue (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    MixedGateBinder → FVarId → Tools.ShippingUnifiedMeaning.Value
  | .bool, x => Tools.ShippingUnifiedMeaning.Value.bool (bools x)
  | .bits n, x => Tools.ShippingUnifiedMeaning.Value.bits n (bits x n)
  | .domain, _ => Tools.ShippingUnifiedMeaning.Value.bool false

/-- The width of a binder's value. -/
def kindWidth : MixedGateBinder → Nat
  | .bool => 1
  | .bits n => n
  | .domain => 1

theorem kindValue_width (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (k : MixedGateBinder) (x : FVarId) :
    (kindValue bools bits k x).kind.width = kindWidth k := by
  cases k <;> rfl

/-- The input map at `x` depends only on the two maps at `x`. -/
theorem inputValues_congr {b1 b2 : Tools.ShippingBoolSourceSoundness.BoolValuation}
    {v1 v2 : Tools.ShippingTranslateSoundness.Valuation} {x : FVarId}
    (hb : b1 x = b2 x) (hv : v1 x = v2 x) :
    Tools.ShippingUnifiedMeaning.inputValues b1 v1 x =
      Tools.ShippingUnifiedMeaning.inputValues b2 v2 x := by
  first
    | (unfold Tools.ShippingUnifiedMeaning.inputValues
       rw [hb, hv])
    | simp only [Tools.ShippingUnifiedMeaning.inputValues, hb, hv]
    | simp [Tools.ShippingUnifiedMeaning.inputValues, hb, hv]

/-- The input map at a variable bound to a vector and to no Bool. -/
theorem inputValues_bits_none {bools : Tools.ShippingBoolSourceSoundness.BoolValuation}
    {bits : Tools.ShippingTranslateSoundness.Valuation} {id : FVarId} {n : Nat} {v : BitVec n}
    (hb : bools id = none) (h : bits id = some ⟨n, v⟩) :
    Tools.ShippingUnifiedMeaning.inputValues bools bits id =
      some (Tools.ShippingUnifiedMeaning.Value.bits n v) := by
  simp [Tools.ShippingUnifiedMeaning.inputValues, hb, h]

/-- **One `extend` step at another variable** leaves the maps at `x`. -/
theorem extend_frame (a : Tools.ShippingMixedEntrySoundness.Setup) (nm : Name)
    (k : MixedGateBinder) (id x : FVarId) (bools : FVarId → Bool)
    (bits : (id : FVarId) → (n : Nat) → BitVec n) (hne : x ≠ id) :
    (Tools.ShippingMixedEntrySoundness.extend a ((nm, k), id) bools bits).bools x = a.bools x ∧
    (Tools.ShippingMixedEntrySoundness.extend a ((nm, k), id) bools bits).bits x = a.bits x := by
  cases k with
  | domain => exact ⟨rfl, rfl⟩
  | bool => exact ⟨if_neg hne, if_neg hne⟩
  | bits n => exact ⟨if_neg hne, if_neg hne⟩

/-- **`prepare` over binders none of whose variables is `x`** leaves the maps
at `x`. -/
theorem prepare_frame {bools : FVarId → Bool} {bits : (id : FVarId) → (n : Nat) → BitVec n}
    (bs : List (Name × MixedGateBinder)) :
    ∀ (ids : List FVarId) (a : Tools.ShippingMixedEntrySoundness.Setup) (x : FVarId),
      x ∉ ids →
      (Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids) a).bools x = a.bools x ∧
      (Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids) a).bits x =
        a.bits x := by
  induction bs with
  | nil =>
    intro ids a x _
    cases ids <;> exact ⟨rfl, rfl⟩
  | cons q bs ih =>
    intro ids a x hx
    cases ids with
    | nil => exact ⟨rfl, rfl⟩
    | cons id ids =>
      obtain ⟨nm, k⟩ := q
      have hne : x ≠ id := fun h => hx (List.mem_cons.mpr (Or.inl h))
      have hin : x ∉ ids := fun h => hx (List.mem_cons.mpr (Or.inr h))
      obtain ⟨h1, h2⟩ := ih ids
        (Tools.ShippingMixedEntrySoundness.extend a ((nm, k), id) bools bits) x hin
      obtain ⟨e1, e2⟩ := extend_frame a nm k id x bools bits hne
      exact ⟨h1.trans e1, h2.trans e2⟩

/-- **One `extend` step of a non-domain binder at `x`** maps `x` to the
binder's value. -/
theorem extend_inputValue (a : Tools.ShippingMixedEntrySoundness.Setup) (nm : Name)
    (k : MixedGateBinder) (x : FVarId) (bools : FVarId → Bool)
    (bits : (id : FVarId) → (n : Nat) → BitVec n) (hk : k ≠ MixedGateBinder.domain) :
    Tools.ShippingUnifiedMeaning.inputValues
      (Tools.ShippingMixedEntrySoundness.extend a ((nm, k), x) bools bits).bools
      (Tools.ShippingMixedEntrySoundness.extend a ((nm, k), x) bools bits).bits x =
      some (kindValue bools bits k x) := by
  cases k with
  | domain => exact absurd rfl hk
  | bool => exact Tools.ShippingUnifiedMeaning.inputValues_bool (if_pos rfl)
  | bits n => exact inputValues_bits_none (if_pos rfl) (if_pos rfl)

/-- **The generic input fact**: the prepared setup maps the variable at
position `i` to the value of the (non-domain) binder at position `i`. -/
theorem prepare_inputValue {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} (bs : List (Name × MixedGateBinder)) :
    ∀ (ids : List FVarId) (i : Nat) (a : Tools.ShippingMixedEntrySoundness.Setup)
      (nm : Name) (k : MixedGateBinder) (x : FVarId),
      ids.Nodup → AtIdx bs i (nm, k) → AtIdx ids i x → k ≠ MixedGateBinder.domain →
      Tools.ShippingUnifiedMeaning.inputValues
        (Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids) a).bools
        (Tools.ShippingMixedEntrySoundness.prepare bools bits (bs.zip ids) a).bits x =
        some (kindValue bools bits k x) := by
  induction bs with
  | nil =>
    intro ids i a nm k x _ hb _ _
    cases i <;> exact False.elim hb
  | cons q bs ih =>
    intro ids i a nm k x nd hb hx hk
    cases ids with
    | nil => cases i <;> exact False.elim hx
    | cons id ids =>
      obtain ⟨hnotin, nd'⟩ := List.nodup_cons.mp nd
      cases i with
      | zero =>
        have hq : q = (nm, k) := hb
        have hid : id = x := hx
        have hx0 : x ∉ ids := by
          rw [← hid]
          exact hnotin
        obtain ⟨f1, f2⟩ := prepare_frame (bools := bools) (bits := bits) bs ids
          (Tools.ShippingMixedEntrySoundness.extend a (q, id) bools bits) x hx0
        have g : Tools.ShippingUnifiedMeaning.inputValues
            (Tools.ShippingMixedEntrySoundness.extend a (q, id) bools bits).bools
            (Tools.ShippingMixedEntrySoundness.extend a (q, id) bools bits).bits x =
            some (kindValue bools bits k x) := by
          rw [hq, hid]
          exact extend_inputValue a nm k x bools bits hk
        exact (inputValues_congr f1 f2).trans g
      | succ i =>
        exact ih ids i (Tools.ShippingMixedEntrySoundness.extend a (q, id) bools bits)
          nm k x nd' hb hx hk

end Tools.ShippingLegacySem
