import Sparkle.IR.Machine

/-! # `topoBody` succeeds on an orderable body

`closeInsts` puts the combinational statements (assignments and instances) of
the closed module in dependency order with `topoBody` — Kahn's algorithm, the
first ready statement at each round — and returns nothing when it gets stuck.
Here: it does not get stuck when SOME order of those statements is a
dependency order (`Ordered`), and what it returns is one.

Pure statements about lists; no run, no module. Where an ordered witness or
a rank comes from is not here. -/
namespace Tools.ShippingTopoBody
open Sparkle.IR.AST Sparkle.IR.Machine

/-- Every name the statement reads is settled, or driven by nothing. -/
abbrev readyB (A D S : List String) (st : Stmt) : Bool :=
  (combReads A st).all fun n => S.contains n || !D.contains n

theorem readyB_mono {A D S S' : List String} {st : Stmt} (h : ∀ n, n ∈ S → n ∈ S')
    (hr : readyB A D S st = true) : readyB A D S' st = true := by
  simp only [readyB, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
    Bool.not_eq_true'] at hr ⊢
  intro n hn
  rcases hr n hn with hs | hd
  · exact Or.inl (h n hs)
  · exact Or.inr hd

/-- A dependency order from the settled names `S`: each statement is ready
once the ones before it have written. -/
def Ordered (A D : List String) : List String → List Stmt → Prop
  | _, [] => True
  | S, st :: L => readyB A D S st = true ∧ Ordered A D (combWrites A st ++ S) L

theorem Ordered.mono {A D : List String} :
    ∀ (L : List Stmt) {S S' : List String}, (∀ n, n ∈ S → n ∈ S') →
      Ordered A D S L → Ordered A D S' L
  | [], _, _, _, _ => trivial
  | st :: L, S, S', h, ho =>
    ⟨readyB_mono h ho.1, Ordered.mono L (by
      intro n hn
      rcases List.mem_append.mp hn with hw | hs
      · exact List.mem_append_left _ hw
      · exact List.mem_append_right _ (h n hs)) ho.2⟩

/-- Taking a statement out of a dependency order, its writes settled. -/
theorem Ordered.remove {A D : List String} (st : Stmt) :
    ∀ (pre post : List Stmt) (S : List String), Ordered A D S (pre ++ st :: post) →
      Ordered A D (combWrites A st ++ S) (pre ++ post)
  | [], _, _, h => h.2
  | p :: pre, post, S, h => by
    refine ⟨readyB_mono (fun n hn => List.mem_append_right _ hn) h.1, ?_⟩
    refine Ordered.mono _ ?_ (Ordered.remove st pre post _ h.2)
    intro n hn
    rcases List.mem_append.mp hn with h1 | h2
    · exact List.mem_append_right _ (List.mem_append_left _ h1)
    · rcases List.mem_append.mp h2 with h3 | h4
      · exact List.mem_append_left _ h3
      · exact List.mem_append_right _ (List.mem_append_right _ h4)

/-! ## One round -/

theorem pickReady_some (A D S : List String) :
    ∀ (pending : List Stmt) (st : Stmt), st ∈ pending → readyB A D S st = true →
      ∃ st' rest, pickReady A D S pending = some (st', rest)
  | [], _, h, _ => absurd h List.not_mem_nil
  | p :: ps, st, h, hr => by
    unfold pickReady
    by_cases hp : readyB A D S p = true
    · rw [if_pos hp]
      exact ⟨_, _, rfl⟩
    · rw [if_neg hp]
      have hst : st ∈ ps := by
        rcases List.mem_cons.mp h with e | h
        · subst e
          exact absurd hr hp
        · exact h
      obtain ⟨st', rest, e⟩ := pickReady_some A D S ps st hst hr
      rw [e]
      exact ⟨_, _, rfl⟩

theorem pickReady_spec (A D S : List String) :
    ∀ (pending : List Stmt) (st : Stmt) (rest : List Stmt),
      pickReady A D S pending = some (st, rest) →
      readyB A D S st = true ∧ ∃ pre post, pending = pre ++ st :: post ∧ rest = pre ++ post
  | [], _, _, h => by
    unfold pickReady at h
    cases h
  | p :: ps, st, rest, h => by
    unfold pickReady at h
    by_cases hp : readyB A D S p = true
    · rw [if_pos hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1; subst e2
      exact ⟨hp, [], ps, rfl, rfl⟩
    · rw [if_neg hp] at h
      cases e : pickReady A D S ps with
      | none =>
        rw [e] at h
        cases h
      | some q =>
        obtain ⟨st', rest'⟩ := q
        rw [e] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨e1, e2⟩ := h
        subst e1; subst e2
        obtain ⟨hr, pre, post, e1, e2⟩ := pickReady_spec A D S ps st' rest' e
        exact ⟨hr, p :: pre, post, by rw [e1]; rfl, by rw [e2]; rfl⟩

/-! ## The loop -/

/-- **The loop does not get stuck on an orderable list**, and what it returns
is a dependency order of the same statements. -/
theorem go_some (A D : List String) :
    ∀ (fuel : Nat) (S : List String) (pending acc L : List Stmt),
      pending.length < fuel → L.Perm pending → Ordered A D S L →
      ∃ picked, topoBody.go A D fuel S pending acc = some (acc.reverse ++ picked) ∧
        picked.Perm pending ∧ Ordered A D S picked
  | 0, _, _, _, _, hf, _, _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, S, [], acc, _, _, _, _ => by
    refine ⟨[], ?_, List.Perm.refl _, trivial⟩
    unfold topoBody.go
    simp
  | fuel + 1, S, p :: ps, acc, L, hf, hperm, hord => by
    -- the witness' head is ready and pending
    obtain ⟨hd, tl, hL⟩ : ∃ hd tl, L = hd :: tl := by
      cases L with
      | nil => exact absurd hperm.length_eq (by simp)
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    subst hL
    obtain ⟨st, rest, hpick⟩ := pickReady_some A D S (p :: ps) hd
      (hperm.subset (List.mem_cons_self ..)) hord.1
    obtain ⟨hready, pre, post, hpend, hrest⟩ := pickReady_spec A D S _ _ _ hpick
    -- the picked statement, taken out of the witness
    have hmem : st ∈ hd :: tl := hperm.symm.subset (by rw [hpend]; simp)
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hmem
    have hord' : Ordered A D (combWrites A st ++ S) (l1 ++ l2) := by
      rw [hsplit] at hord
      exact Ordered.remove st l1 l2 S hord
    have hperm' : (l1 ++ l2).Perm rest := by
      rw [hrest]
      have h1 : (st :: (l1 ++ l2)).Perm (st :: (pre ++ post)) := by
        refine (List.perm_middle.symm.trans ?_).trans List.perm_middle
        rw [← hsplit, ← hpend]
        exact hperm
      exact h1.cons_inv
    have hlen : rest.length < fuel := by
      have : (p :: ps).length = rest.length + 1 := by
        rw [hpend, hrest]
        simp only [List.length_append, List.length_cons]
        omega
      simp only [List.length_cons] at this hf
      omega
    obtain ⟨picked, hgo, hpp, hpo⟩ :=
      go_some A D fuel (combWrites A st ++ S) rest (st :: acc) (l1 ++ l2) hlen hperm' hord'
    refine ⟨st :: picked, ?_, ?_, hready, hpo⟩
    · unfold topoBody.go
      simp only [hpick]
      rw [hgo]
      simp
    · rw [hpend]
      refine List.Perm.trans ?_ List.perm_middle.symm
      rw [hrest] at hpp
      exact hpp.cons st

/-! ## From a rank

An ordered witness need not be exhibited: a RANK on the statements under
which every driven name a statement reads is written by a statement of
smaller rank is enough (the pending statement of least rank is ready). -/

theorem exists_min_rank (rank : Stmt → Nat) :
    ∀ (l : List Stmt), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, rank x ≤ rank y
  | [], h => absurd rfl h
  | [x], _ => ⟨x, List.mem_cons_self .., fun y hy => by
      rcases List.mem_cons.mp hy with e | e
      · rw [e]; exact Nat.le_refl _
      · cases e⟩
  | x :: y :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_rank rank (y :: l) (List.cons_ne_nil _ _)
    by_cases hx : rank x ≤ rank m
    · refine ⟨x, List.mem_cons_self .., fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with e | e
      · rw [e]; exact Nat.le_refl _
      · exact Nat.le_trans hx (hmin z e)
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with e | e
      · rw [e]; omega
      · exact hmin z e

/-- **The loop does not get stuck when a rank exists.** `comb`: all the
statements; the invariant: a statement no longer pending has its writes
settled. -/
theorem go_some_rank (A D : List String) (comb : List Stmt) (rank : Stmt → Nat)
    (hrank : ∀ st ∈ comb, ∀ r ∈ combReads A st, r ∈ D →
      ∃ st' ∈ comb, r ∈ combWrites A st' ∧ rank st' < rank st) :
    ∀ (fuel : Nat) (S : List String) (pending acc : List Stmt),
      pending.length < fuel → (∀ st ∈ pending, st ∈ comb) →
      (∀ st' ∈ comb, st' ∉ pending → ∀ n ∈ combWrites A st', n ∈ S) →
      ∃ picked, topoBody.go A D fuel S pending acc = some (acc.reverse ++ picked) ∧
        picked.Perm pending ∧ Ordered A D S picked
  | 0, _, _, _, hf, _, _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, S, [], acc, _, _, _ => by
    refine ⟨[], ?_, List.Perm.refl _, trivial⟩
    unfold topoBody.go
    simp
  | fuel + 1, S, p :: ps, acc, hf, hsub, hinv => by
    -- the pending statement of least rank is ready
    obtain ⟨mn, hmn, hmin⟩ := exists_min_rank rank (p :: ps) (List.cons_ne_nil _ _)
    have hmr : readyB A D S mn = true := by
      simp only [readyB, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
        Bool.not_eq_true']
      intro r hr
      by_cases hd : r ∈ D
      · obtain ⟨st', hc', hw', hlt⟩ := hrank mn (hsub mn hmn) r hr hd
        refine Or.inl (hinv st' hc' (fun hp => ?_) r hw')
        have := hmin st' hp
        omega
      · exact Or.inr (by simpa using hd)
    obtain ⟨st, rest, hpick⟩ := pickReady_some A D S (p :: ps) mn hmn hmr
    obtain ⟨hready, pre, post, hpend, hrest⟩ := pickReady_spec A D S _ _ _ hpick
    have hlen : rest.length < fuel := by
      have : (p :: ps).length = rest.length + 1 := by
        rw [hpend, hrest]
        simp only [List.length_append, List.length_cons]
        omega
      simp only [List.length_cons] at this hf
      omega
    have hsub' : ∀ s ∈ rest, s ∈ comb := by
      intro s hs
      refine hsub s ?_
      rw [hpend]
      rw [hrest] at hs
      rcases List.mem_append.mp hs with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hinv' : ∀ st' ∈ comb, st' ∉ rest → ∀ n ∈ combWrites A st', n ∈ combWrites A st ++ S := by
      intro st' hc' hnr n hn
      by_cases he : st' = st
      · subst he
        exact List.mem_append_left _ hn
      · refine List.mem_append_right _ (hinv st' hc' (fun hp => hnr ?_) n hn)
        rw [hpend] at hp
        rw [hrest]
        rcases List.mem_append.mp hp with h | h
        · exact List.mem_append_left _ h
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h he
          · exact List.mem_append_right _ h
    obtain ⟨picked, hgo, hpp, hpo⟩ :=
      go_some_rank A D comb rank hrank fuel (combWrites A st ++ S) rest (st :: acc) hlen hsub' hinv'
    refine ⟨st :: picked, ?_, ?_, hready, hpo⟩
    · unfold topoBody.go
      simp only [hpick]
      rw [hgo]
      simp
    · rw [hpend]
      refine List.Perm.trans ?_ List.perm_middle.symm
      rw [hrest] at hpp
      exact hpp.cons st

/-! ## `topoBody` -/

/-- The combinational statements of a body. -/
def combOf (body : List Stmt) : List Stmt :=
  body.filter fun st => match st with
    | .assign .. | .inst .. => true
    | _ => false

/-- The others (registers, memories). -/
def othersOf (body : List Stmt) : List Stmt :=
  body.filter fun st => match st with
    | .assign .. | .inst .. => false
    | _ => true

/-- The names an assignment of the body drives. -/
def byAssignOf (body : List Stmt) : List String :=
  (combOf body).flatMap Sparkle.IR.Reorder.stmtWrites

/-- The names a combinational statement of the body drives. -/
def drivenOf (body : List Stmt) : List String :=
  byAssignOf body ++ (combOf body).flatMap (combWrites (byAssignOf body))

/-- **`topoBody` succeeds when the combinational statements can be ordered**:
it returns a dependency order of them, the other statements after. -/
theorem topoBody_some {body L : List Stmt} (hperm : L.Perm (combOf body))
    (hord : Ordered (byAssignOf body) (drivenOf body) [] L) :
    ∃ sorted, topoBody body = some (sorted ++ othersOf body) ∧ sorted.Perm (combOf body) ∧
      Ordered (byAssignOf body) (drivenOf body) [] sorted := by
  obtain ⟨picked, hgo, hpp, hpo⟩ := go_some (byAssignOf body) (drivenOf body)
    ((combOf body).length + 1) [] (combOf body) [] L (Nat.lt_succ_self _) hperm hord
  refine ⟨picked, ?_, hpp, hpo⟩
  unfold topoBody
  simp only []
  show (topoBody.go (byAssignOf body) (drivenOf body) ((combOf body).length + 1) []
    (combOf body) []).map (· ++ othersOf body) = _
  rw [hgo]
  simp

/-- **`topoBody` succeeds when the combinational statements have a rank.** -/
theorem topoBody_some_rank {body : List Stmt} (rank : Stmt → Nat)
    (hrank : ∀ st ∈ combOf body, ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body →
      ∃ st' ∈ combOf body, r ∈ combWrites (byAssignOf body) st' ∧ rank st' < rank st) :
    ∃ sorted, topoBody body = some (sorted ++ othersOf body) ∧ sorted.Perm (combOf body) ∧
      Ordered (byAssignOf body) (drivenOf body) [] sorted := by
  obtain ⟨picked, hgo, hpp, hpo⟩ := go_some_rank (byAssignOf body) (drivenOf body) (combOf body)
    rank hrank ((combOf body).length + 1) [] (combOf body) [] (Nat.lt_succ_self _)
    (fun _ h => h) (fun st' hc hn => absurd hc hn)
  refine ⟨picked, ?_, hpp, hpo⟩
  unfold topoBody
  simp only []
  show (topoBody.go (byAssignOf body) (drivenOf body) ((combOf body).length + 1) []
    (combOf body) []).map (· ++ othersOf body) = _
  rw [hgo]
  simp

/-! ## A rank from a rank on names

Every combinational statement here drives one name (an assignment its
target; an instance its output wire). A rank `ρ` on NAMES under which each
statement's driven reads rank below the name it drives gives the rank on
statements `topoBody_some_rank` asks. -/

/-- The rank of a statement: the rank of the (first) name it drives. -/
def rankOf (A : List String) (ρ : String → Nat) (st : Stmt) : Nat :=
  match combWrites A st with
  | n :: _ => ρ n
  | [] => 0

theorem mem_driven {body : List Stmt} {r : String} (h : r ∈ drivenOf body) :
    ∃ st' ∈ combOf body, r ∈ combWrites (byAssignOf body) st' := by
  unfold drivenOf at h
  rcases List.mem_append.mp h with h | h
  · unfold byAssignOf at h
    obtain ⟨st', hs, hw⟩ := List.mem_flatMap.mp h
    refine ⟨st', hs, ?_⟩
    cases st' <;> first | exact hw | (simp [Sparkle.IR.Reorder.stmtWrites] at hw)
  · exact List.mem_flatMap.mp h

theorem rank_of_names {body : List Stmt} (ρ : String → Nat)
    (hsingle : ∀ st ∈ combOf body, ∃ l, combWrites (byAssignOf body) st = [l])
    (hρ : ∀ st ∈ combOf body, ∀ l, combWrites (byAssignOf body) st = [l] →
      ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body → ρ r < ρ l) :
    ∀ st ∈ combOf body, ∀ r ∈ combReads (byAssignOf body) st, r ∈ drivenOf body →
      ∃ st' ∈ combOf body, r ∈ combWrites (byAssignOf body) st' ∧
        rankOf (byAssignOf body) ρ st' < rankOf (byAssignOf body) ρ st := by
  intro st hs r hr hd
  obtain ⟨st', hs', hw'⟩ := mem_driven hd
  obtain ⟨l, hl⟩ := hsingle st hs
  obtain ⟨l', hl'⟩ := hsingle st' hs'
  refine ⟨st', hs', hw', ?_⟩
  have e : r = l' := by
    rw [hl'] at hw'
    simpa using hw'
  unfold rankOf
  rw [hl, hl']
  exact e ▸ hρ st hs l hl r hr hd

end Tools.ShippingTopoBody
