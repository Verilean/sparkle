import Tools.ShippingClosedOrder
import Tools.ShippingTopoBody

/-! # A rank on the names of a closed transition (one-output calls)

For the one-output closing only (every statement drives one name). The rank
of a name, by what drives it:

* a wire a transition statement drives: `(4f+2)·M + pos` — `f` the first
  field whose prefix of the body contains the driver (the number of fields
  if none: the core), `pos` its position;
* the port of `let` `a`: `(4a+3)·M`;
* the output port of call `j`: `(4c+1)·M`, every argument `let` of the call
  below `c`;
* anything else (next-value and output names): `4·(K+1)·M`.

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

/-! ## The rank -/

/-- The rank of a name (see the file's header). -/
def rho (T : List Stmt) (pres : List (List Stmt)) (letNames instNames : List String)
    (cs : List Nat) (x : String) : Nat :=
  if x ∈ writesOf T then (4 * firstIdx pres x + 2) * (T.length + 1) + posOf (writesOf T) x
  else if x ∈ letNames then (4 * posOf letNames x + 3) * (T.length + 1)
  else if x ∈ instNames then (4 * cs.getD (posOf instNames x) 0 + 1) * (T.length + 1)
  else 4 * (pres.length + 1) * (T.length + 1)

variable {T : List Stmt} {pres : List (List Stmt)} {letNames instNames : List String}
  {cs : List Nat}

theorem writes_length : ∀ {T : List Stmt}, Acyclic T → (writesOf T).length = T.length
  | [], _ => rfl
  | _ :: T, h => by
    cases h with
    | @cons l r _ _ _ htl =>
      show (l :: writesOf T).length = _
      simp [writes_length htl]

theorem rho_body {x : String} (h : x ∈ writesOf T) :
    rho T pres letNames instNames cs x =
      (4 * firstIdx pres x + 2) * (T.length + 1) + posOf (writesOf T) x := by
  unfold rho
  rw [if_pos h]

theorem rho_let {x : String} {a : Nat} (h1 : x ∉ writesOf T) (hnd : letNames.Nodup)
    (ha : letNames[a]? = some x) :
    rho T pres letNames instNames cs x = (4 * a + 3) * (T.length + 1) := by
  unfold rho
  rw [if_neg h1, if_pos (List.mem_of_getElem? ha), posOf_getElem hnd ha]

theorem rho_inst {x : String} {j c : Nat} (h1 : x ∉ writesOf T) (h2 : x ∉ letNames)
    (hnd : instNames.Nodup) (hj : instNames[j]? = some x) (hc : cs[j]? = some c) :
    rho T pres letNames instNames cs x = (4 * c + 1) * (T.length + 1) := by
  unfold rho
  rw [if_neg h1, if_neg h2, if_pos (List.mem_of_getElem? hj), posOf_getElem hnd hj]
  simp [List.getD, hc]

theorem rho_other {x : String} (h1 : x ∉ writesOf T) (h2 : x ∉ letNames) (h3 : x ∉ instNames) :
    rho T pres letNames instNames cs x = 4 * (pres.length + 1) * (T.length + 1) := by
  unfold rho
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem pos_lt_M {x : String} (hT : Acyclic T) (h : x ∈ writesOf T) :
    posOf (writesOf T) x < T.length + 1 := by
  have := posOf_lt h
  rw [writes_length hT] at this
  omega

/-- The field of a body statement's target bounds what the reads' rules say:
if every prefix that drives `l` puts `n` below its index, and `n ≤ K`
otherwise, then `n` is at most the field of `l`. -/
theorem le_field {l : String} {n : Nat}
    (hpre : ∀ i pre, pres[i]? = some pre → l ∈ writesOf pre → n ≤ i) (hK : n ≤ pres.length) :
    n ≤ firstIdx pres l := by
  by_cases h : firstIdx pres l < pres.length
  · obtain ⟨pre, h1, h2⟩ := firstIdx_spec h
    exact hpre _ pre h1 h2
  · omega

/-- A body statement reads a body-driven name: below. -/
theorem lt_body_body (hT : Acyclic T) (hpre : ∀ pre ∈ pres, pre <+: T) {l x : String} {r : Expr}
    (hm : Stmt.assign l r ∈ T) (hx : x ∈ refsOf r) (hw : x ∈ writesOf T) :
    rho T pres letNames instNames cs x < rho T pres letNames instNames cs l := by
  rw [rho_body hw, rho_body (mem_writes_assign hm)]
  refine block_le_lt ?_ (pos_lt_of_read hT hm hx hw)
  have : firstIdx pres x ≤ firstIdx pres l := by
    by_cases h : firstIdx pres l < pres.length
    · obtain ⟨pre, h1, h2⟩ := firstIdx_spec h
      exact firstIdx_le h1 (prefix_closed hT (hpre pre (List.mem_of_getElem? h1)) hm h2 hx hw)
    · have := firstIdx_le_length pres x
      omega
  omega

/-- A body statement of field `≥ n + 1` (for a `let` port: `n = a`)… the
generic comparison: a name of block `b` is below a body-driven name whose
field is `f` when `b < 4f + 2`. -/
theorem lt_block_body (hT : Acyclic T) {l : String} {b : Nat} (hl : l ∈ writesOf T)
    (hb : b < 4 * firstIdx pres l + 2) :
    b * (T.length + 1) < rho T pres letNames instNames cs l := by
  rw [rho_body hl]
  have := block_lt (r1 := 0) (r2 := posOf (writesOf T) l) (M := T.length + 1) hb (Nat.succ_pos _)
  simpa using this

/-- A body-driven name whose field is at most `f` is below block `b` when
`4f + 2 < b`. -/
theorem lt_body_block (hT : Acyclic T) {x : String} {b f : Nat} (hx : x ∈ writesOf T)
    (hf : firstIdx pres x ≤ f) (hb : 4 * f + 2 < b) :
    rho T pres letNames instNames cs x < b * (T.length + 1) := by
  rw [rho_body hx]
  have := block_lt (c1 := 4 * firstIdx pres x + 2) (c2 := b) (r1 := posOf (writesOf T) x) (r2 := 0)
    (M := T.length + 1) (by omega) (pos_lt_M hT hx)
  simpa using this

end Tools.ShippingRankNames
