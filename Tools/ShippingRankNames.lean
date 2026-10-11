import Tools.ShippingClosedOrder
import Tools.ShippingTopoBody

/-! # A rank on the names of a closed transition (one-output calls)

For the one-output closing only (every statement drives one name). The rank
of a name, by what drives it:

* a wire a transition statement drives: `3·f·M + pos` — `f` the first field
  whose prefix of the body contains the driver (the number of fields if
  none: the core), `pos` its position;
* the port of `let` `a`: `(3a+1)·M`;
* the output port of call `j`: `(3·m_j+2)·M`, `m_j` a bound of its argument
  `let`s;
* anything else (next-value and output names): `3·(K+1)·M`.

Here: the definitions and the order facts about lists. Which reads a real
transition's statements have is not here. -/
namespace Tools.ShippingRankNames
open Sparkle.IR.AST Sparkle.IR.Reorder
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingClosedOrder

/-- Position of the first occurrence (the length if none). -/
def posOf : List String → String → Nat
  | [], _ => 0
  | y :: ys, x => if y = x then 0 else posOf ys x + 1

theorem posOf_le : ∀ (l : List String) (x : String), posOf l x ≤ l.length
  | [], _ => Nat.le_refl _
  | y :: ys, x => by
    unfold posOf
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (posOf_le ys x)

theorem posOf_lt : ∀ {l : List String} {x : String}, x ∈ l → posOf l x < l.length
  | y :: ys, x, h => by
    unfold posOf
    split
    · exact Nat.succ_pos _
    · rename_i hne
      rcases List.mem_cons.mp h with e | h
      · exact absurd e.symm hne
      · exact Nat.succ_lt_succ (posOf_lt h)

theorem posOf_append_mem : ∀ {A : List String} (C : List String) {x : String}, x ∈ A →
    posOf (A ++ C) x = posOf A x
  | y :: ys, C, x, h => by
    show posOf (y :: (ys ++ C)) x = posOf (y :: ys) x
    unfold posOf
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp h with e | h
      · exact absurd e.symm hne
      · rw [posOf_append_mem C h]

theorem posOf_append_notMem : ∀ {A : List String} (C : List String) {x : String}, x ∉ A →
    posOf (A ++ C) x = A.length + posOf C x
  | [], C, x, _ => by simp
  | y :: ys, C, x, h => by
    have hne : ¬ y = x := fun e => h (e ▸ List.mem_cons_self ..)
    show (if y = x then 0 else posOf (ys ++ C) x + 1) = (y :: ys).length + posOf C x
    rw [if_neg hne, posOf_append_notMem C (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp only [List.length_cons]
    omega

/-- In a list without repetition, the position of the element at index `a`. -/
theorem posOf_getElem : ∀ {l : List String} {a : Nat} {x : String}, l.Nodup → l[a]? = some x →
    posOf l x = a
  | y :: ys, 0, x, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    unfold posOf
    rw [if_pos h]
  | y :: ys, a + 1, x, hnd, h => by
    simp only [List.getElem?_cons_succ] at h
    have hnd' := List.nodup_cons.mp hnd
    have hne : ¬ y = x := fun e => hnd'.1 (e ▸ List.mem_of_getElem? h)
    unfold posOf
    rw [if_neg hne, posOf_getElem hnd'.2 h]

/-- The first of the lists that drives `x` (their number if none). -/
def firstIdx : List (List Stmt) → String → Nat
  | [], _ => 0
  | pre :: ps, x => if x ∈ writesOf pre then 0 else firstIdx ps x + 1

theorem firstIdx_le_length : ∀ (ps : List (List Stmt)) (x : String), firstIdx ps x ≤ ps.length
  | [], _ => Nat.le_refl _
  | p :: ps, x => by
    unfold firstIdx
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (firstIdx_le_length ps x)

theorem firstIdx_le : ∀ {ps : List (List Stmt)} {i : Nat} {pre : List Stmt} {x : String},
    ps[i]? = some pre → x ∈ writesOf pre → firstIdx ps x ≤ i
  | p :: ps, 0, pre, x, h, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    unfold firstIdx
    rw [if_pos (h ▸ hx)]
    exact Nat.le_refl _
  | p :: ps, i + 1, pre, x, h, hx => by
    simp only [List.getElem?_cons_succ] at h
    unfold firstIdx
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (firstIdx_le h hx)

theorem firstIdx_spec : ∀ {ps : List (List Stmt)} {x : String}, firstIdx ps x < ps.length →
    ∃ pre, ps[firstIdx ps x]? = some pre ∧ x ∈ writesOf pre
  | p :: ps, x, h => by
    unfold firstIdx at h ⊢
    split
    · rename_i hx
      exact ⟨p, rfl, hx⟩
    · rename_i hx
      rw [if_neg hx] at h
      obtain ⟨pre, h1, h2⟩ := firstIdx_spec (ps := ps) (x := x) (by simpa using h)
      exact ⟨pre, by simpa using h1, h2⟩

/-- `c₁·M + r₁ < c₂·M + r₂` for `c₁ < c₂`, `r₁ < M`. -/
theorem block_lt {c1 c2 r1 r2 M : Nat} (h : c1 < c2) (hr : r1 < M) : c1 * M + r1 < c2 * M + r2 := by
  have : (c1 + 1) * M ≤ c2 * M := Nat.mul_le_mul_right M h
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem block_le_lt {c1 c2 r1 r2 M : Nat} (h : c1 ≤ c2) (hr : r1 < r2) :
    c1 * M + r1 < c2 * M + r2 := by
  have : c1 * M ≤ c2 * M := Nat.mul_le_mul_right M h
  omega

/-! ## Ordered bodies -/

/-- In an ordered body, a name a statement reads that the body drives is
driven strictly before the statement's target. -/
theorem pos_lt_of_read : ∀ {T : List Stmt}, Acyclic T → ∀ {l : String} {r : Expr} {x : String},
    Stmt.assign l r ∈ T → x ∈ refsOf r → x ∈ writesOf T →
    posOf (writesOf T) x < posOf (writesOf T) l := by
  intro T hT l r x hm hx hw
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hm
  have hsuf := Acyclic.suffix hT
  have hwd := Acyclic.writes_disjoint hT
  cases hsuf with
  | @cons _ _ _ ht hrd _ =>
    have hxl := hrd x hx
    have hxA : x ∈ writesOf A := by
      have : writesOf (A ++ Stmt.assign l r :: B) = writesOf A ++ (l :: writesOf B) := by
        unfold writesOf
        rw [List.flatMap_append]
        rfl
      rw [this] at hw
      rcases List.mem_append.mp hw with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h hxl.1
        · exact absurd h hxl.2
    have hlA : l ∉ writesOf A := fun h => hwd l h (List.mem_cons_self ..)
    have hsplit : writesOf (A ++ Stmt.assign l r :: B) = writesOf A ++ (l :: writesOf B) := by
      unfold writesOf
      rw [List.flatMap_append]
      rfl
    rw [hsplit, posOf_append_mem _ hxA, posOf_append_notMem _ hlA]
    have := posOf_lt hxA
    omega

/-- A prefix of an ordered body that drives a statement's target drives
every body-driven name the statement reads. -/
theorem prefix_closed {T pre : List Stmt} (hT : Acyclic T) (hp : pre <+: T) {l : String} {r : Expr}
    {x : String} (hm : Stmt.assign l r ∈ T) (hl : l ∈ writesOf pre) (hx : x ∈ refsOf r)
    (hw : x ∈ writesOf T) : x ∈ writesOf pre := by
  obtain ⟨rest, rfl⟩ := hp
  have hwd := Acyclic.writes_disjoint hT
  have hrdj := Acyclic.reads_disjoint hT
  have hin : Stmt.assign l r ∈ pre := by
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exact absurd (mem_writes_assign h) (hwd l hl)
  have hsplit : writesOf (pre ++ rest) = writesOf pre ++ writesOf rest := by
    unfold writesOf
    exact List.flatMap_append ..
  rw [hsplit] at hw
  rcases List.mem_append.mp hw with h | h
  · exact h
  · exact absurd h (hrdj l r hin x hx)

end Tools.ShippingRankNames
