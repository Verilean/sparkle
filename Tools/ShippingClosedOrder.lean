import Tools.ShippingMachineClose
import Tools.ShippingAssignmentOrder

/-! # The let-closed body is in dependency order

`closeLets` builds, from a transition body `B ++ [assign out = w]`, the list

  `frontAliases aliases B ++ insertAliases aliases B ++ [assign out = core]`

— every alias `assign p = a[…]` right after the statement that drives its
operand `a`, or at the front when nothing drives `a` — and accepts it only if
it passes `assignmentOrderCheck`, i.e. is `Acyclic`. This file proves that it
is (`closed_acyclic`), from facts about `B` and the aliases only:

* `B ++ [assign out = w]` is `Acyclic` (the harness' order invariant);
* the ports are distinct, driven by no statement of `B`, and not `out`;
* no operand is a port, or `out`;
* **every statement that reads a port comes after the driver of that port's
  operand** (or the operand is driven by nothing).

No assumption that the check passed. -/
namespace Tools.ShippingClosedOrder
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingSettledSoundness (Acyclic)

theorem mem_writes_right {X Y : List Stmt} {x : String} (h : x ∈ writesOf Y) :
    x ∈ writesOf (X ++ Y) := by rw [writesOf_append]; exact List.mem_append_right _ h

theorem Acyclic.suffix : ∀ {X Y : List Stmt}, Acyclic (X ++ Y) → Acyclic Y
  | [], _, h => h
  | _ :: X, Y, h => by
    cases h with
    | cons _ _ ht => exact Acyclic.suffix (X := X) ht

/-- In an ordered list a name written early is not written later. -/
theorem Acyclic.writes_disjoint : ∀ {X Y : List Stmt}, Acyclic (X ++ Y) →
    ∀ x ∈ writesOf X, x ∉ writesOf Y
  | [], _, _, x, hx => by simp [writesOf] at hx
  | st :: X, Y, h, x, hx => by
    cases h with
    | @cons l r _ ht _ htl =>
      change x ∈ l :: writesOf X at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · intro hy
        exact ht (mem_writes_right hy)
      · exact Acyclic.writes_disjoint (X := X) htl x hx

/-- In an ordered list a statement does not read what is written later. -/
theorem Acyclic.reads_disjoint : ∀ {X Y : List Stmt}, Acyclic (X ++ Y) →
    ∀ l r, Stmt.assign l r ∈ X → ∀ x ∈ refsOf r, x ∉ writesOf Y
  | [], _, _, _, _, hm => by cases hm
  | st :: X, Y, h, l, r, hm => by
    cases h with
    | cons _ hr htl =>
      rcases List.mem_cons.mp hm with heq | hin
      · cases heq
        intro x hx hy
        exact (hr x hx).2 (mem_writes_right hy)
      · exact Acyclic.reads_disjoint (X := X) htl l r hin

/-- Every statement of an ordered list is an assignment. -/
theorem Acyclic.assign : ∀ {X : List Stmt}, Acyclic X → ∀ st ∈ X, ∃ l r, st = .assign l r
  | _, .cons _ _ ht, st, hm => by
    rcases List.mem_cons.mp hm with rfl | hin
    · exact ⟨_, _, rfl⟩
    · exact Acyclic.assign ht st hin

theorem writes_aliasBlock (L : List (Port × String)) :
    writesOf (L.map fun pa => aliasStmt pa.1 pa.2) = L.map (·.1.name) := by
  induction L with
  | nil => rfl
  | cons pa rest ih =>
    rw [List.map_cons, List.map_cons, ← ih]
    rfl

/-- A block of aliases in front of an ordered list: distinct ports written
nowhere after; each operand written nowhere after, not its own port, and not
the port of a LATER alias of the block (it may be an earlier one's: `let y :=
x` after `let x := input`). -/
theorem acyclic_aliasBlock : ∀ (L : List (Port × String)) (T : List Stmt), Acyclic T →
    (L.map (·.1.name)).Nodup → (∀ pa ∈ L, pa.1.name ∉ writesOf T) →
    (∀ pa ∈ L, pa.2 ∉ writesOf T ∧ pa.2 ≠ pa.1.name) →
    L.Pairwise (fun pa pb => pa.2 ≠ pb.1.name) →
    Acyclic ((L.map fun pa => aliasStmt pa.1 pa.2) ++ T)
  | [], T, hT, _, _, _, _ => hT
  | pa :: rest, T, hT, hnd, hp, ha, hpw => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have ih := acyclic_aliasBlock rest T hT hnd.2 (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      (fun q hq => ha q (List.mem_cons_of_mem _ hq)) hpw.2
    show Acyclic (.assign pa.1.name (.slice (.ref pa.2) (pa.1.ty.bitWidth - 1) 0) :: _)
    have hw : writesOf ((rest.map fun pa => aliasStmt pa.1 pa.2) ++ T) =
        rest.map (·.1.name) ++ writesOf T := by rw [writesOf_append, writes_aliasBlock]
    have key : ∀ x, x ∈ writesOf ((rest.map fun pa => aliasStmt pa.1 pa.2) ++ T) →
        x ∈ rest.map (·.1.name) ∨ x ∈ writesOf T := by
      intro x hx; rw [hw] at hx; exact List.mem_append.mp hx
    refine .cons ?_ ?_ ih
    · intro h0
      rcases key _ h0 with h | h
      · exact hnd.1 h
      · exact hp pa List.mem_cons_self h
    · intro x hx
      have hxa : x = pa.2 := by simpa [refsOf] using hx
      subst hxa
      refine ⟨(ha pa List.mem_cons_self).2, ?_⟩
      intro h0
      rcases key _ h0 with h | h
      · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp h
        exact hpw.1 q hq hqn.symm
      · exact (ha pa List.mem_cons_self).1 h

/-- What the alias insertion writes: what the body writes, and the ports of
aliases whose operand the body drives. -/
theorem writes_insertAliases (aliases : List (Port × String)) :
    ∀ (B : List Stmt) (x : String), x ∈ writesOf (insertAliases aliases B) →
      x ∈ writesOf B ∨ ∃ pa ∈ aliases, pa.1.name = x ∧ pa.2 ∈ writesOf B
  | [], x, h => by simp [insertAliases, writesOf] at h
  | st :: rest, x, h => by
    have hsplit : writesOf (insertAliases aliases (st :: rest)) =
        writesOf [st] ++ (writesOf (aliasesOf aliases st) ++ writesOf (insertAliases aliases rest)) := by
      show writesOf (st :: (aliasesOf aliases st ++ insertAliases aliases rest)) = _
      rw [show st :: (aliasesOf aliases st ++ insertAliases aliases rest) =
        [st] ++ (aliasesOf aliases st ++ insertAliases aliases rest) from rfl,
        writesOf_append, writesOf_append]
    have hB : writesOf (st :: rest) = writesOf [st] ++ writesOf rest := by
      rw [show st :: rest = [st] ++ rest from rfl, writesOf_append]
    rw [hsplit] at h
    rw [hB]
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (List.mem_append_left _ h)
    · rcases List.mem_append.mp h with h | h
      · -- an alias placed after `st`: its operand is what `st` drives
        cases st with
        | assign l r =>
          simp only [aliasesOf] at h
          rw [writes_aliasBlock] at h
          obtain ⟨pa, hpa, hn⟩ := List.mem_map.mp h
          obtain ⟨hmem, hop⟩ := List.mem_filter.mp hpa
          refine Or.inr ⟨pa, hmem, hn, List.mem_append_left _ ?_⟩
          have : pa.2 = l := by simpa using hop
          rw [this]
          simp [writesOf, stmtWrites]
        | _ => simp [aliasesOf, writesOf] at h
      · rcases writes_insertAliases aliases rest x h with h | ⟨pa, hpa, hn, hw⟩
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr ⟨pa, hpa, hn, List.mem_append_right _ hw⟩

theorem eq_of_map_nodup {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | a :: l, hnd, x, y, hx, hy, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with hxa | hx <;> rcases List.mem_cons.mp hy with hya | hy
    · rw [hxa, hya]
    · exact absurd (List.mem_map.mpr ⟨y, hy, by rw [← h, hxa]⟩) hnd.1
    · exact absurd (List.mem_map.mpr ⟨x, hx, by rw [h, hya]⟩) hnd.1
    · exact eq_of_map_nodup hnd.2 hx hy h

theorem mem_writes_left {X Y : List Stmt} {x : String} (h : x ∈ writesOf X) :
    x ∈ writesOf (X ++ Y) := by rw [writesOf_append]; exact List.mem_append_left _ h

theorem Acyclic.prefix : ∀ {X Y : List Stmt}, Acyclic (X ++ Y) → Acyclic X
  | [], _, _ => .nil
  | _ :: X, Y, h => by
    cases h with
    | @cons l r _ ht hr htl =>
      exact .cons (fun h => ht (mem_writes_left h))
        (fun x hx => ⟨(hr x hx).1, fun h => (hr x hx).2 (mem_writes_left h)⟩)
        (Acyclic.prefix (X := X) htl)

theorem pairwise_of_all {α : Type} {R : α → α → Prop} : ∀ {l : List α},
    (∀ a ∈ l, ∀ b ∈ l, R a b) → l.Pairwise R
  | [], _ => .nil
  | a :: l, h => List.pairwise_cons.mpr
    ⟨fun b hb => h a List.mem_cons_self b (List.mem_cons_of_mem _ hb),
      pairwise_of_all (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩

theorem mem_writes_assign {l : String} {r : Expr} {X : List Stmt} (h : Stmt.assign l r ∈ X) :
    l ∈ writesOf X := by
  unfold writesOf
  exact List.mem_flatMap.mpr ⟨_, h, by simp [stmtWrites]⟩

/-- **The alias insertion keeps the order**, for a suffix `B` of the body
after a prefix `pre`, in front of any ordered `T` it does not interfere with. -/
theorem acyclic_insert (aliases : List (Port × String))
    (hnd : (aliases.map (·.1.name)).Nodup) :
    ∀ (B pre T : List Stmt), Acyclic (pre ++ B) → Acyclic T →
      (∀ pa ∈ aliases, pa.1.name ∉ writesOf (pre ++ B)) →
      (∀ pa ∈ aliases, ∀ pre1 l r post, B = pre1 ++ Stmt.assign l r :: post →
        pa.1.name ∈ refsOf r → pa.2 ∈ writesOf (pre ++ pre1) ∨ pa.2 ∉ writesOf (pre ++ B)) →
      (∀ x ∈ writesOf T, x ∉ writesOf B ∧ (∀ pa ∈ aliases, pa.1.name ≠ x ∧ pa.2 ≠ x) ∧
        ∀ l r, Stmt.assign l r ∈ B → x ∉ refsOf r) →
      Acyclic (insertAliases aliases B ++ T)
  | [], _, _, _, hT, _, _, _ => hT
  | st :: rest, pre, T, hacy, hT, hports, hread, hTc => by
    obtain ⟨l, r, rfl⟩ := Acyclic.assign (Acyclic.suffix hacy) st List.mem_cons_self
    have hsuf := Acyclic.suffix hacy
    have htgt : l ∉ writesOf rest := by cases hsuf with | cons h _ _ => exact h
    have hrd : ∀ x ∈ refsOf r, x ≠ l ∧ x ∉ writesOf rest := by cases hsuf with | cons _ h _ => exact h
    have happ : (pre ++ [Stmt.assign l r]) ++ rest = pre ++ Stmt.assign l r :: rest := by
      rw [List.append_assoc]; rfl
    have hlB : l ∈ writesOf (pre ++ Stmt.assign l r :: rest) :=
      mem_writes_right (mem_writes_assign List.mem_cons_self)
    have hl_pre : l ∉ writesOf pre := fun h =>
      Acyclic.writes_disjoint hacy l h (mem_writes_assign List.mem_cons_self)
    have hrestB : ∀ x, x ∈ writesOf rest → x ∈ writesOf (pre ++ Stmt.assign l r :: rest) :=
      fun x hx => mem_writes_right (by
        rw [show Stmt.assign l r :: rest = [Stmt.assign l r] ++ rest from rfl]
        exact mem_writes_right hx)
    have hpre_rest : ∀ x, x ∈ writesOf pre → x ∉ writesOf rest := fun x hx hr' =>
      Acyclic.writes_disjoint hacy x hx (by
        rw [show Stmt.assign l r :: rest = [Stmt.assign l r] ++ rest from rfl]
        exact mem_writes_right hr')
    have ih : Acyclic (insertAliases aliases rest ++ T) := by
      refine acyclic_insert aliases hnd rest (pre ++ [Stmt.assign l r]) T (happ ▸ hacy) hT
        (fun pa hpa => happ ▸ hports pa hpa) ?_ ?_
      · intro pa hpa pre1 l' r' post hB hx
        have := hread pa hpa (Stmt.assign l r :: pre1) l' r' post (by rw [hB]; rfl) hx
        rw [happ]
        rw [show pre ++ [Stmt.assign l r] ++ pre1 = pre ++ Stmt.assign l r :: pre1 by
          rw [List.append_assoc]; rfl]
        exact this
      · intro x hx
        obtain ⟨h1, h2, h3⟩ := hTc x hx
        exact ⟨fun h => h1 (by
            rw [show Stmt.assign l r :: rest = [Stmt.assign l r] ++ rest from rfl]
            exact mem_writes_right h), h2, fun l' r' hm => h3 l' r' (List.mem_cons_of_mem _ hm)⟩
    have key : ∀ x, x ∈ writesOf (insertAliases aliases rest ++ T) →
        x ∈ writesOf rest ∨ (∃ pa ∈ aliases, pa.1.name = x ∧ pa.2 ∈ writesOf rest) ∨
          x ∈ writesOf T := by
      intro x hx
      rw [writesOf_append] at hx
      rcases List.mem_append.mp hx with h | h
      · rcases writes_insertAliases aliases rest x h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hTl : l ∉ writesOf T := fun h => (hTc l h).1 (mem_writes_assign List.mem_cons_self)
    have hblock : Acyclic (((aliases.filter fun pa => pa.2 == l).map fun pa => aliasStmt pa.1 pa.2) ++
        (insertAliases aliases rest ++ T)) := by
      refine acyclic_aliasBlock _ _ ih (hnd.sublist (List.filter_sublist.map _)) ?_ ?_ ?_
      · intro pa hpa hw
        obtain ⟨hmem, hop⟩ := List.mem_filter.mp hpa
        have hpl : pa.2 = l := by simpa using hop
        rcases key _ hw with h | ⟨pa', hpa', hn, hw'⟩ | h
        · exact hports pa hmem (hrestB _ h)
        · have := eq_of_map_nodup hnd hpa' hmem hn
          subst this
          exact htgt (hpl ▸ hw')
        · exact ((hTc _ h).2.1 pa hmem).1 rfl
      · intro pa hpa
        obtain ⟨hmem, hop⟩ := List.mem_filter.mp hpa
        have hpl : pa.2 = l := by simpa using hop
        refine ⟨fun hw => ?_, fun h => hports pa hmem (by rw [← h, hpl]; exact hlB)⟩
        rw [hpl] at hw
        rcases key _ hw with h | ⟨pa', hpa', hn, -⟩ | h
        · exact htgt h
        · exact hports pa' hpa' (hn ▸ hlB)
        · exact hTl h
      · -- the operands of this block are all `l`, a driven wire: no port
        refine pairwise_of_all (fun pa hpa pb hpb h => ?_)
        have hpl : pa.2 = l := by simpa using (List.mem_filter.mp hpa).2
        exact hports pb (List.mem_filter.mp hpb).1 (by rw [← h, hpl]; exact hlB)
    show Acyclic (Stmt.assign l r :: (((aliases.filter fun pa => pa.2 == l).map
      fun pa => aliasStmt pa.1 pa.2) ++ insertAliases aliases rest) ++ T)
    rw [show (Stmt.assign l r :: (((aliases.filter fun pa => pa.2 == l).map
        fun pa => aliasStmt pa.1 pa.2) ++ insertAliases aliases rest) ++ T) =
      Stmt.assign l r :: (((aliases.filter fun pa => pa.2 == l).map
        fun pa => aliasStmt pa.1 pa.2) ++ (insertAliases aliases rest ++ T)) by
      simp [List.append_assoc]]
    have key2 : ∀ x, x ∈ writesOf (((aliases.filter fun pa => pa.2 == l).map
        fun pa => aliasStmt pa.1 pa.2) ++ (insertAliases aliases rest ++ T)) →
        (∃ pa ∈ aliases, pa.2 = l ∧ pa.1.name = x) ∨ x ∈ writesOf rest ∨
          (∃ pa ∈ aliases, pa.1.name = x ∧ pa.2 ∈ writesOf rest) ∨ x ∈ writesOf T := by
      intro x hx
      rw [writesOf_append, writes_aliasBlock] at hx
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨pa, hpa, hn⟩ := List.mem_map.mp h
        obtain ⟨hmem, hop⟩ := List.mem_filter.mp hpa
        exact Or.inl ⟨pa, hmem, by simpa using hop, hn⟩
      · exact Or.inr (key x h)
    refine .cons ?_ ?_ hblock
    · intro h0
      rcases key2 _ h0 with ⟨pa, hpa, -, hn⟩ | h | ⟨pa, hpa, hn, -⟩ | h
      · exact hports pa hpa (hn ▸ hlB)
      · exact htgt h
      · exact hports pa hpa (hn ▸ hlB)
      · exact hTl h
    · intro x hx
      refine ⟨(hrd x hx).1, fun h0 => ?_⟩
      rcases key2 _ h0 with ⟨pa, hpa, hpl, hn⟩ | h | ⟨pa, hpa, hn, hw⟩ | h
      · -- the statement reads a port whose operand it drives itself
        rcases hread pa hpa [] l r rest rfl (hn ▸ hx) with h | h
        · rw [List.append_nil, hpl] at h; exact hl_pre h
        · exact h (hpl ▸ hlB)
      · exact (hrd x hx).2 h
      · -- the statement reads a port whose operand is driven later
        rcases hread pa hpa [] l r rest rfl (hn ▸ hx) with h | h
        · rw [List.append_nil] at h; exact hpre_rest _ h hw
        · exact h (hrestB _ hw)
      · exact (hTc x h).2.2 l r List.mem_cons_self hx

/-- **The let-closed body is in dependency order.** An operand may be an
EARLIER alias' port (`let y := x`) provided that alias' own operand is driven
by nothing (so both go to the front, in order); an operand that is the port of
an alias placed after a driver is what the real `closeLets` refuses. -/
theorem closed_acyclic {B : List Stmt} {w core : String} (aliases : List (Port × String))
    (hacy : Acyclic (B ++ [Stmt.assign "out" (.ref w)]))
    (hnd : (aliases.map (·.1.name)).Nodup)
    (hports : ∀ pa ∈ aliases, pa.1.name ∉ writesOf B ∧ pa.1.name ≠ "out")
    (hops : ∀ pa ∈ aliases, pa.2 ≠ "out" ∧ pa.2 ≠ pa.1.name)
    (hpair : aliases.Pairwise (fun pa pb => pa.2 ≠ pb.1.name))
    (hfront : ∀ pa ∈ aliases, ∀ pa' ∈ aliases, pa.2 = pa'.1.name → pa'.2 ∉ writesOf B)
    (hcore : core ≠ "out")
    (hread : ∀ pa ∈ aliases, ∀ pre l r post, B = pre ++ Stmt.assign l r :: post →
      pa.1.name ∈ refsOf r → pa.2 ∈ writesOf pre ∨ pa.2 ∉ writesOf B) :
    Acyclic (frontAliases aliases B ++ insertAliases aliases B ++ [Stmt.assign "out" (.ref core)]) := by
  have hB : Acyclic B := Acyclic.prefix hacy
  have hT : Acyclic [Stmt.assign "out" (.ref core)] :=
    .cons (by simp [writesOf]) (fun x hx => by
      have : x = core := by simpa [refsOf] using hx
      subst this
      exact ⟨hcore, by simp [writesOf]⟩) .nil
  have hout : ∀ x, x ∈ writesOf [Stmt.assign "out" (Expr.ref core)] → x = "out" := by
    intro x hx; simpa [writesOf, stmtWrites] using hx
  have hins : Acyclic (insertAliases aliases B ++ [Stmt.assign "out" (.ref core)]) := by
    refine acyclic_insert aliases hnd B [] _
      hB hT (fun pa hpa => (hports pa hpa).1) (fun pa hpa pre l r post h hx => by
        simpa using hread pa hpa pre l r post h hx) ?_
    intro x hx
    obtain rfl := hout x hx
    refine ⟨fun h => Acyclic.writes_disjoint hacy _ h (by simp [writesOf, stmtWrites]),
      fun pa hpa => ⟨(hports pa hpa).2, (hops pa hpa).1⟩, fun l r hm hx' => ?_⟩
    exact Acyclic.reads_disjoint hacy l r hm _ hx' (by simp [writesOf, stmtWrites])
  rw [List.append_assoc]
  unfold frontAliases
  refine acyclic_aliasBlock _ _ hins (hnd.sublist (List.filter_sublist.map _)) ?_ ?_
    (hpair.sublist List.filter_sublist)
  · intro pa hpa hw
    obtain ⟨hmem, hfr⟩ := List.mem_filter.mp hpa
    have hnotw : pa.2 ∉ writesOf B := by simpa using hfr
    rw [writesOf_append] at hw
    rcases List.mem_append.mp hw with h | h
    · rcases writes_insertAliases aliases B _ h with h | ⟨pa', hpa', hn, hw'⟩
      · exact (hports pa hmem).1 h
      · have := eq_of_map_nodup hnd hpa' hmem hn
        subst this
        exact hnotw hw'
    · exact (hports pa hmem).2 (hout _ h)
  · intro pa hpa
    obtain ⟨hmem, hfr⟩ := List.mem_filter.mp hpa
    have hnotw : pa.2 ∉ writesOf B := by simpa using hfr
    refine ⟨fun hw => ?_, (hops pa hmem).2⟩
    rw [writesOf_append] at hw
    rcases List.mem_append.mp hw with h | h
    · rcases writes_insertAliases aliases B _ h with h | ⟨pa', hpa', hn, hw'⟩
      · exact hnotw h
      · exact hfront pa hmem pa' hpa' hn.symm hw'
    · exact (hops pa hmem).1 (hout _ h)

end Tools.ShippingClosedOrder
