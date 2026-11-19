import Tools.VedMem

/-!
# A kernel-cheap `OrderOkM` (`sparkle-ved-memory-rest`)

`OrderOkM` (`Tools/VedMem.lean`) is a Bool of list `contains` / `isPermOf` / `woCheck` over `String` names; the
entry proves it by `decide +kernel`, and on a body of ~1000 statements that is quadratic String / `Stmt` equality in
the kernel (23 GB, > 900 s on the SoC; measured in the report of unit ved-memr4).

`OrderOkM'` is a SOUND SUFFICIENT condition for `OrderOkM` (only `OrderOkM' m b = true → OrderOkM m b = true` is proved;
it may refuse what `OrderOkM` accepts, e.g. on a collision of the cheap statement keys or the table keys), and the entry
keeps the old `decide` as the fallback when it is false.  It was measured much cheaper in the kernel on the memory rows
(ved-memr4/5 reports); the search tree is not balanced, so there is no general near-linear bound:

* a name is turned into the Nat `ncode name` (an exact positional code of its characters, injective: `ncode_inj`);
  from then on only Nat arithmetic and comparison is used (GMP-accelerated in the kernel; evaluating a String literal
  costs the kernel ~1 ms per character and is done once per distinct name).
* the NAMES (inputs, `nextKeys`, written names) are entered ONCE in a search tree (keyed by a scrambled copy of the code,
  so that consecutive names do not give a list); every entry carries its kind (input / state key / written), the index
  of the statement that writes it and its place in the entry list.  Each entry is looked up again (`chkE`): then two
  entries with the same name are one entry, which every conjunct is derived from.
* the permutation of the statements is a one-pass search on pairs (cheap key, statement): the key rejects most
  candidates by a Nat comparison before the structural `Stmt` equality runs.

`OrderOkM'_sound` : `OrderOkM' m b = true → OrderOkM m b = true`.  No axiom, no `native_decide`.
-/

namespace Tools.VedMemOrder

open Sparkle.IR.AST Sparkle.IR.Reorder Tools.VedMem

/-! ## 1. Name codes and the search tree -/

/-- positional code of a list of characters (base `0x110001`, digits `1 .. 0x110000`) -/
def ncodeL : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat + 1) + 1114113 * ncodeL cs

theorem char_lt (c : Char) : c.toNat < 0x110000 := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  show c.val.toNat < _
  omega

theorem ncodeL_inj : ∀ (l₁ l₂ : List Char), ncodeL l₁ = ncodeL l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], c :: cs, h => by simp only [ncodeL] at h; omega
  | c :: cs, [], h => by simp only [ncodeL] at h; omega
  | c :: cs, d :: ds, h => by
    simp only [ncodeL] at h
    have hc := char_lt c
    have hd := char_lt d
    have h1 : c.toNat = d.toNat := by omega
    have h2 : ncodeL cs = ncodeL ds := by omega
    rw [ncodeL_inj cs ds h2, Char.ext (UInt32.toNat_inj.mp h1)]

/-- the exact Nat code of a name -/
def ncode (s : String) : Nat := ncodeL s.toList

theorem ncode_inj {a b : String} (h : ncode a = ncode b) : a = b :=
  String.ext (ncodeL_inj _ _ h)

/-- a scrambled copy of a code: the key of the tree (a collision only makes `chkE` fail) -/
def skey (c : Nat) : Nat := (c * 1442695040888963407) % 2305843009213693951

/-- an entry of the name table -/
structure Ent where
  code : Nat   -- `ncode` of the name
  kind : Nat   -- 0 input, 1 state key (`nextKeys`), 2 written name
  sidx : Nat   -- index of the writing statement (kind 2)
  gidx : Nat   -- place in the entry list

inductive NT (α : Type) where
  | leaf : NT α
  | node : NT α → Nat → α → NT α → NT α

def NT.ins {α : Type} : NT α → Nat → α → NT α
  | .leaf, k, v => .node .leaf k v .leaf
  | .node l k' v' r, k, v =>
    if Nat.blt k k' then .node (l.ins k v) k' v' r
    else if Nat.blt k' k then .node l k' v' (r.ins k v)
    else .node l k' v r

def NT.find {α : Type} : NT α → Nat → Option α
  | .leaf, _ => none
  | .node l k' v r, k =>
    if Nat.blt k k' then l.find k
    else if Nat.blt k' k then r.find k
    else some v

def NT.vals {α : Type} : NT α → List α
  | .leaf => []
  | .node l _ v r => l.vals ++ v :: r.vals

theorem NT.vals_ins {α : Type} (t : NT α) (k : Nat) (v : α) : ∀ e ∈ (t.ins k v).vals, e = v ∨ e ∈ t.vals := by
  induction t with
  | leaf => intro e he; simpa [NT.ins, NT.vals] using he
  | node l k' v' r ihl ihr =>
    intro e he
    simp only [NT.ins] at he
    split at he
    · simp only [NT.vals, List.mem_append, List.mem_cons] at he ⊢
      rcases he with h | h | h
      · rcases ihl e h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · split at he
      · simp only [NT.vals, List.mem_append, List.mem_cons] at he ⊢
        rcases he with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · rcases ihr e h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
      · simp only [NT.vals, List.mem_append, List.mem_cons] at he ⊢
        rcases he with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))

theorem NT.find_mem {α : Type} (t : NT α) (k : Nat) (e : α) : t.find k = some e → e ∈ t.vals := by
  induction t with
  | leaf => intro h; simp [NT.find] at h
  | node l k' v r ihl ihr =>
    intro h
    simp only [NT.find] at h
    split at h
    · simp only [NT.vals, List.mem_append]; exact Or.inl (ihl h)
    · split at h
      · simp only [NT.vals, List.mem_append, List.mem_cons]; exact Or.inr (Or.inr (ihr h))
      · cases h; simp [NT.vals]

/-- the tree of a list, keyed by `key` -/
def NT.build {α : Type} (key : α → Nat) (l : List α) : NT α := l.foldl (fun t e => t.ins (key e) e) .leaf

theorem NT.vals_build {α : Type} (key : α → Nat) (l : List α) : ∀ e ∈ (NT.build key l).vals, e ∈ l := by
  have h : ∀ (l0 l : List α) (t : NT α), (∀ e ∈ t.vals, e ∈ l0) → (∀ e ∈ l, e ∈ l0) →
      ∀ e ∈ (l.foldl (fun t e => t.ins (key e) e) t).vals, e ∈ l0 := by
    intro l0 l
    induction l with
    | nil => intro t ht _ e he; exact ht e he
    | cons a rest ih =>
      intro t ht hl
      apply ih
      · intro e he
        rcases NT.vals_ins t _ a e he with h | h
        · exact h ▸ hl a (List.mem_cons_self ..)
        · exact ht e h
      · intro e he; exact hl e (List.mem_cons_of_mem _ he)
  intro e he
  exact h l l .leaf (fun e he => by simp [NT.vals] at he) (fun e he => he) e he

/-! ## 2. The entry list -/

/-- `(code, 2, statement index)` of every written name -/
def tagW : List Stmt → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | s :: rest, n => (stmtWrites s).map (fun w => (ncode w, 2, n)) ++ tagW rest (n + 1)

def numberE : Nat → List (Nat × Nat × Nat) → List Ent
  | _, [] => []
  | g, (c, k, s) :: rest => ⟨c, k, s, g⟩ :: numberE (g + 1) rest

def rawE (m : Module) (b : List Stmt) : List (Nat × Nat × Nat) :=
  (m.inputs.map (fun p => (ncode p.name, 0, 0))) ++ (nextKeys b).map (fun k => (ncode k, 1, 0)) ++ tagW b 0

def entsOf (m : Module) (b : List Stmt) : List Ent := numberE 0 (rawE m b)

/-- the tree key of an entry -/
def Ent.key (e : Ent) : Nat := skey e.code

/-- every entry is looked up again and sits at its own place -/
def chkE (T : NT Ent) : Nat → List Ent → Bool
  | _, [] => true
  | g, e :: rest =>
    (match T.find (skey e.code) with
      | none => false
      | some e' => Nat.beq e'.code e.code && Nat.beq e'.kind e.kind && Nat.beq e'.sidx e.sidx && Nat.beq e'.gidx e.gidx) &&
    Nat.beq e.gidx g && chkE T (g + 1) rest

theorem numberE_mem_of (l : List (Nat × Nat × Nat)) :
    ∀ (g : Nat), ∀ t ∈ l, ∃ g', (⟨t.1, t.2.1, t.2.2, g'⟩ : Ent) ∈ numberE g l := by
  induction l with
  | nil => intro g t ht; simp at ht
  | cons h rest ih =>
    intro g t ht
    obtain ⟨c, k, s⟩ := h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨g, by simp [numberE]⟩
    · obtain ⟨g', hg'⟩ := ih (g + 1) t ht
      exact ⟨g', by simp [numberE, hg']⟩

theorem numberE_mem_to (l : List (Nat × Nat × Nat)) :
    ∀ (g : Nat), ∀ e ∈ numberE g l, (e.code, e.kind, e.sidx) ∈ l := by
  induction l with
  | nil => intro g e he; simp [numberE] at he
  | cons h rest ih =>
    intro g e he
    obtain ⟨c, k, s⟩ := h
    simp only [numberE, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · exact List.mem_cons_of_mem _ (ih (g + 1) e he)

theorem numberE_code (l : List (Nat × Nat × Nat)) :
    ∀ (g : Nat), (numberE g l).map Ent.code = l.map (·.1) := by
  induction l with
  | nil => intro g; rfl
  | cons h rest ih => intro g; obtain ⟨c, k, s⟩ := h; simp [numberE, ih]

theorem chkE_sound (T : NT Ent) : ∀ (l : List Ent) (g : Nat), chkE T g l = true →
    (∀ e ∈ l, T.find (skey e.code) = some e) ∧ (∀ e ∈ l, g ≤ e.gidx) ∧ (l.map Ent.code).Nodup := by
  intro l
  induction l with
  | nil => intro g _; simp
  | cons e rest ih =>
    intro g h
    simp only [chkE, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hf, hg, hnd⟩ := ih (g + 1) h3
    have hgi : e.gidx = g := Nat.eq_of_beq_eq_true h2
    have hfe : T.find (skey e.code) = some e := by
      cases hfd : T.find (skey e.code) with
      | none => rw [hfd] at h1; simp at h1
      | some e' =>
        rw [hfd] at h1
        simp only [Bool.and_eq_true] at h1
        obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h1
        have := Nat.eq_of_beq_eq_true a1
        have := Nat.eq_of_beq_eq_true a2
        have := Nat.eq_of_beq_eq_true a3
        have := Nat.eq_of_beq_eq_true a4
        cases e'; cases e; simp_all
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfe
      · exact hf x hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := hg x hx; omega
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hmem
      obtain ⟨x, hx, hxc⟩ := List.mem_map.mp hmem
      have h4 := hf x hx
      rw [hxc, hfe] at h4
      have h5 : e = x := Option.some.inj h4
      have := hg x hx
      rw [← h5] at this
      omega

/-! ## 3. The checks -/

/-- the order check of `woCheck`'s reads: a name written by a statement in the table is written at or before `i` -/
def rdOk (T : NT Ent) (i : Nat) (n : String) : Bool :=
  match T.find (skey (ncode n)) with
  | none => true
  | some e => !Nat.beq e.kind 2 || Nat.ble e.sidx i

def rdOrd (T : NT Ent) : Nat → List Stmt → Bool
  | _, [] => true
  | i, s :: rest => (stmtReads s).all (rdOk T i) && rdOrd T (i + 1) rest

/-- a read name is in the table (input, key or written) -/
def exOk (T : NT Ent) (n : String) : Bool :=
  match T.find (skey (ncode n)) with
  | none => false
  | some e => Nat.beq e.code (ncode n)

def rdEx (T : NT Ent) : List Stmt → Bool
  | [] => true
  | s :: rest => (allReadsM s).all (exOk T) && rdEx T rest

/-- an output is a key or a written name -/
def outOk (T : NT Ent) (n : String) : Bool :=
  match T.find (skey (ncode n)) with
  | none => false
  | some e => Nat.beq e.code (ncode n) && !Nat.beq e.kind 0

/-- a cheap key of a statement -/
def stmtKey : Stmt → Nat
  | .assign l _ => skey (ncode l)
  | .register o .. => skey (ncode o)
  | .memory n .. => skey (ncode n)
  | .inst _ i _ => skey (ncode i)

theorem nodup_of_map' {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup) : l.Nodup := by
  unfold List.Nodup at h ⊢
  rw [List.pairwise_map] at h
  exact h.imp (fun hne e => hne (congrArg f e))

/-- statements numbered by their place -/
def numberS : Nat → List Stmt → List (Nat × Stmt)
  | _, [] => []
  | g, s :: rest => (g, s) :: numberS (g + 1) rest

/-- the tree key of a numbered statement -/
def psKey (p : Nat × Stmt) : Nat := stmtKey p.2

/-- the keys of the statements are looked up again and found at their own place -/
def chkS (T : NT (Nat × Stmt)) : Nat → List Stmt → Bool
  | _, [] => true
  | g, s :: rest =>
    (match T.find (stmtKey s) with
      | none => false
      | some p => Nat.beq p.1 g) && chkS T (g + 1) rest

/-- every statement of `l` is the one the table holds under its key -/
def inclS (T : NT (Nat × Stmt)) (l : List Stmt) : Bool :=
  l.all (fun s => match T.find (stmtKey s) with
    | none => false
    | some p => decide (p.2 = s))

/-- `l₁` and `l₂` are permutations of each other: the statements' keys are distinct in each list and each statement
of one list is, by its key, the statement of the other (no quadratic search) -/
def permT (l₁ l₂ : List Stmt) : Bool :=
  chkS (NT.build psKey (numberS 0 l₁)) 0 l₁ && chkS (NT.build psKey (numberS 0 l₂)) 0 l₂ &&
  inclS (NT.build psKey (numberS 0 l₂)) l₁ && inclS (NT.build psKey (numberS 0 l₁)) l₂

theorem numberS_mem_to : ∀ (l : List Stmt) (g : Nat), ∀ p ∈ numberS g l, p.2 ∈ l := by
  intro l
  induction l with
  | nil => intro g p hp; simp [numberS] at hp
  | cons s rest ih =>
    intro g p hp
    simp only [numberS, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · exact List.mem_cons_of_mem _ (ih (g + 1) p hp)

theorem chkS_sound (T : NT (Nat × Stmt)) : ∀ (l : List Stmt) (g : Nat), chkS T g l = true →
    (∀ s ∈ l, ∃ p, T.find (stmtKey s) = some p ∧ g ≤ p.1) ∧ (l.map stmtKey).Nodup := by
  intro l
  induction l with
  | nil => intro g _; simp
  | cons s rest ih =>
    intro g h
    simp only [chkS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hf, hnd⟩ := ih (g + 1) h2
    cases hfd : T.find (stmtKey s) with
    | none => rw [hfd] at h1; simp at h1
    | some p =>
      rw [hfd] at h1
      have hp : p.1 = g := Nat.eq_of_beq_eq_true h1
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨p, hfd, by omega⟩
        · obtain ⟨q, hq, hq2⟩ := hf x hx
          exact ⟨q, hq, by omega⟩
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hnd⟩
        intro hmem
        obtain ⟨x, hx, hxk⟩ := List.mem_map.mp hmem
        obtain ⟨q, hq, hq2⟩ := hf x hx
        rw [hxk, hfd] at hq
        have := Option.some.inj hq
        subst this
        omega

theorem inclS_sound (T : NT (Nat × Stmt)) (l0 : List Stmt) (hv : ∀ p ∈ T.vals, p.2 ∈ l0) (l : List Stmt)
    (h : inclS T l = true) : ∀ s ∈ l, s ∈ l0 := by
  intro s hs
  simp only [inclS, List.all_eq_true] at h
  have h1 := h s hs
  cases hfd : T.find (stmtKey s) with
  | none => rw [hfd] at h1; simp at h1
  | some p =>
    rw [hfd] at h1
    have h2 : p.2 = s := of_decide_eq_true h1
    exact h2 ▸ hv p (NT.find_mem _ _ _ hfd)

theorem perm_of_nodup_mem [DecidableEq α] : ∀ (l₁ l₂ : List α), l₁.Nodup → l₂.Nodup → (∀ a, a ∈ l₁ ↔ a ∈ l₂) →
    l₁.Perm l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ h
    cases l₂ with
    | nil => exact List.Perm.refl _
    | cons b t => exact absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | cons a t ih =>
    intro l₂ h1 h2 h
    rw [List.nodup_cons] at h1
    have hmem : a ∈ l₂ := (h a).mp (List.mem_cons_self ..)
    have hperm : t.Perm (l₂.erase a) := by
      refine ih _ h1.2 (List.Nodup.erase a h2) ?_
      intro x
      rw [List.Nodup.mem_erase_iff h2]
      constructor
      · intro hx
        refine ⟨fun hxa => h1.1 (hxa ▸ hx), (h x).mp (List.mem_cons_of_mem _ hx)⟩
      · rintro ⟨hne, hx⟩
        rcases List.mem_cons.mp ((h x).mpr hx) with rfl | hx'
        · exact absurd rfl hne
        · exact hx'
    exact (hperm.cons a).trans (List.perm_cons_erase hmem).symm

theorem permT_sound (l₁ l₂ : List Stmt) (h : permT l₁ l₂ = true) : l₁.Perm l₂ := by
  simp only [permT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hn1 := nodup_of_map' stmtKey _ (chkS_sound _ _ _ h1).2
  have hn2 := nodup_of_map' stmtKey _ (chkS_sound _ _ _ h2).2
  have hv : ∀ l : List Stmt, ∀ p ∈ (NT.build psKey (numberS 0 l)).vals, p.2 ∈ l :=
    fun l p hp => numberS_mem_to l 0 p (NT.vals_build _ _ p hp)
  exact perm_of_nodup_mem _ _ hn1 hn2 (fun a => ⟨inclS_sound _ _ (hv l₂) _ h3 a, inclS_sound _ _ (hv l₁) _ h4 a⟩)

theorem isPermOf_complete [DecidableEq α] : ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → isPermOf l₁ l₂ = true := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; obtain rfl := List.Perm.nil_eq h; rfl
  | cons a rest ih =>
    intro l₂ h
    have hmem : a ∈ l₂ := h.subset (List.mem_cons_self ..)
    simp only [isPermOf, if_pos hmem]
    exact ih (List.Perm.cons_inv (h.trans (List.perm_cons_erase hmem)))

/-- the permutation part is `permT b m.body`; the name-table part and the local part are separate so that the entry
checks them in separate kernel runs (the caches of a run are freed at its end) -/
def OrderTab (m : Module) (b : List Stmt) : Bool :=
  chkE (NT.build Ent.key (entsOf m b)) 0 (entsOf m b) && rdOrd (NT.build Ent.key (entsOf m b)) 0 b &&
  rdEx (NT.build Ent.key (entsOf m b)) b && m.outputs.all (fun p => outOk (NT.build Ent.key (entsOf m b)) p.name)

def OrderLoc (b : List Stmt) : Bool :=
  decide (b.filterMap stmtMemName).Nodup &&
  b.all (fun s => (stmtReads s).all (fun n => !(stmtWrites s).contains n))

/-- `OrderOkM` with the quadratic parts replaced: a sufficient condition (`OrderOkM_of_parts`; the converse is not claimed) -/
def OrderOkM' (m : Module) (b : List Stmt) : Bool := permT b m.body && OrderTab m b && OrderLoc b

/-! ## 4. Soundness -/

theorem tagW_mem (b : List Stmt) :
    ∀ (n : Nat), ∀ t ∈ tagW b n, t.2.1 = 2 ∧ n ≤ t.2.2 ∧ ∃ w ∈ writesOf b, ncode w = t.1 := by
  induction b with
  | nil => intro n t ht; simp [tagW] at ht
  | cons s rest ih =>
    intro n t ht
    simp only [tagW, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨w, hw, rfl⟩ | ht
    · exact ⟨rfl, Nat.le_refl _, w, by simp [writesOf, hw], rfl⟩
    · obtain ⟨h1, h2, w, hw, h4⟩ := ih (n + 1) t ht
      exact ⟨h1, by omega, w, by simp only [writesOf, List.flatMap_cons, List.mem_append]; exact Or.inr hw, h4⟩

theorem mem_tagW (b : List Stmt) :
    ∀ (n : Nat), ∀ w ∈ writesOf b, ∃ j, n ≤ j ∧ (ncode w, 2, j) ∈ tagW b n := by
  induction b with
  | nil => intro n w hw; simp [writesOf] at hw
  | cons s rest ih =>
    intro n w hw
    simp only [writesOf, List.flatMap_cons, List.mem_append] at hw
    rcases hw with hw | hw
    · exact ⟨n, Nat.le_refl _, by simp only [tagW, List.mem_append, List.mem_map]; exact Or.inl ⟨w, hw, rfl⟩⟩
    · obtain ⟨j, hj, hm⟩ := ih (n + 1) w hw
      exact ⟨j, by omega, by simp only [tagW, List.mem_append]; exact Or.inr hm⟩

theorem not_contains_of {l : List String} {x : String} (h : x ∉ l) : (!l.contains x) = true := by
  simp [List.contains_iff_mem, h]

/-- the order part of `woCheck` from the table -/
theorem wo_aux (E : List Ent) (T : NT Ent) (hf : ∀ e ∈ E, T.find (skey e.code) = some e) :
    ∀ (b : List Stmt) (n : Nat) (done : List String),
    (∀ t ∈ tagW b n, ∃ g, (⟨t.1, t.2.1, t.2.2, g⟩ : Ent) ∈ E) →
    (∀ d ∈ done, ∃ g j, j < n ∧ (⟨ncode d, 2, j, g⟩ : Ent) ∈ E) →
    rdOrd T n b = true → woCheck done b = true := by
  have uniq : ∀ e1 ∈ E, ∀ e2 ∈ E, e1.code = e2.code → e1 = e2 := by
    intro e1 h1 e2 h2 hc
    have a := hf e1 h1
    have b := hf e2 h2
    rw [hc] at a
    rw [a] at b
    exact Option.some.inj b
  intro b
  induction b with
  | nil => intro n done _ _ _; rfl
  | cons s rest ih =>
    intro n done hE hdone hrd
    simp only [rdOrd, Bool.and_eq_true, List.all_eq_true] at hrd
    obtain ⟨hrd1, hrd2⟩ := hrd
    have hHead : ∀ w ∈ stmtWrites s, ∃ g, (⟨ncode w, 2, n, g⟩ : Ent) ∈ E := by
      intro w hw
      exact hE (ncode w, 2, n) (by simp only [tagW, List.mem_append, List.mem_map]; exact Or.inl ⟨w, hw, rfl⟩)
    have hTail : ∀ t ∈ tagW rest (n + 1), ∃ g, (⟨t.1, t.2.1, t.2.2, g⟩ : Ent) ∈ E :=
      fun t ht => hE t (by simp only [tagW, List.mem_append]; exact Or.inr ht)
    have hRest : ∀ w ∈ writesOf rest, ∃ j g, n + 1 ≤ j ∧ (⟨ncode w, 2, j, g⟩ : Ent) ∈ E := by
      intro w hw
      obtain ⟨j, hj, hm⟩ := mem_tagW rest (n + 1) w hw
      obtain ⟨g, hg⟩ := hTail _ hm
      exact ⟨j, g, hj, hg⟩
    have hrest : woCheck (done ++ stmtWrites s) rest = true := by
      refine ih (n + 1) (done ++ stmtWrites s) hTail ?_ hrd2
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨g, j, hj, he⟩ := hdone d hd
        exact ⟨g, j, by omega, he⟩
      · obtain ⟨g, he⟩ := hHead d hd
        exact ⟨g, n, by omega, he⟩
    simp only [woCheck, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨?_, ?_⟩, hrest⟩
    · intro x hx
      apply not_contains_of
      intro hin
      obtain ⟨j, g, hj, he⟩ := hRest x hin
      have hr := hrd1 x hx
      have hfe : T.find (skey (ncode x)) = some ⟨ncode x, 2, j, g⟩ := by
        have h := hf ⟨ncode x, 2, j, g⟩ he
        dsimp only at h
        exact h
      simp [rdOk, hfe] at hr
      omega
    · intro x hx
      obtain ⟨g0, he0⟩ := hHead x hx
      refine ⟨not_contains_of ?_, not_contains_of ?_⟩
      · intro hin
        obtain ⟨g, j, hj, he⟩ := hdone x hin
        have := uniq _ he0 _ he rfl
        simp only [Ent.mk.injEq] at this
        omega
      · intro hin
        obtain ⟨j, g, hj, he⟩ := hRest x hin
        have := uniq _ he0 _ he rfl
        simp only [Ent.mk.injEq] at this
        omega

theorem rdEx_all (T : NT Ent) : ∀ (b : List Stmt), rdEx T b = true → ∀ s ∈ b, ∀ n ∈ allReadsM s, exOk T n = true := by
  intro b
  induction b with
  | nil => intro _ s hs; simp at hs
  | cons a rest ih =>
    intro h s hs n hn
    simp only [rdEx, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1 n hn
    · exact ih h.2 s hs n hn

theorem contains_false_of {l : List String} {x : String} (h : x ∉ l) : l.contains x = false := by
  cases hc : l.contains x
  · rfl
  · exact absurd (List.contains_iff_mem.mp hc) h

theorem OrderOkM_of_parts (m : Module) (b : List Stmt) (hperm : permT b m.body = true)
    (h2 : OrderTab m b = true) (h3 : OrderLoc b = true) : OrderOkM m b = true := by
  simp only [OrderTab, OrderLoc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h2 h3
  obtain ⟨⟨⟨hchk, hrdo⟩, hrdx⟩, hout⟩ := h2
  obtain ⟨hmem, hloc⟩ := h3
  have hP : b.Perm m.body := by
    exact permT_sound _ _ hperm
  obtain ⟨hf, hg, hnd⟩ := chkE_sound _ _ _ hchk
  have hpos : ∀ k e, (NT.build Ent.key (entsOf m b)).find k = some e → e ∈ entsOf m b :=
    fun k e h => NT.vals_build _ _ _ (NT.find_mem _ _ _ h)
  have hEtag : ∀ t ∈ tagW b 0, ∃ g, (⟨t.1, t.2.1, t.2.2, g⟩ : Ent) ∈ entsOf m b := by
    intro t ht
    exact numberE_mem_of (rawE m b) 0 t (by simp only [rawE, List.mem_append]; exact Or.inr ht)
  have hEI : ∀ x ∈ m.inputs.map (·.name), ∃ g, (⟨ncode x, 0, 0, g⟩ : Ent) ∈ entsOf m b := by
    intro x hx
    exact numberE_mem_of (rawE m b) 0 (ncode x, 0, 0) (by
      simp only [rawE, List.mem_append]
      refine Or.inl (Or.inl ?_)
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hEK : ∀ x ∈ nextKeys b, ∃ g, (⟨ncode x, 1, 0, g⟩ : Ent) ∈ entsOf m b := by
    intro x hx
    exact numberE_mem_of (rawE m b) 0 (ncode x, 1, 0) (by
      simp only [rawE, List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩)))
  have hEW : ∀ x ∈ writesOf b, ∃ j g, (⟨ncode x, 2, j, g⟩ : Ent) ∈ entsOf m b := by
    intro x hx
    obtain ⟨j, _, hm⟩ := mem_tagW b 0 x hx
    obtain ⟨g, hg⟩ := hEtag _ hm
    exact ⟨j, g, hg⟩
  have hEpos : ∀ e ∈ entsOf m b,
      (e.kind = 0 ∧ ∃ x ∈ m.inputs.map (·.name), ncode x = e.code) ∨
      (e.kind = 1 ∧ ∃ x ∈ nextKeys b, ncode x = e.code) ∨
      (e.kind = 2 ∧ ∃ x ∈ writesOf b, ncode x = e.code) := by
    intro e he
    have := numberE_mem_to (rawE m b) 0 e he
    simp only [rawE, List.mem_append, List.mem_map] at this
    rcases this with (⟨p, hp, h1⟩ | ⟨k, hk, h1⟩) | ht
    · have h1 := Prod.mk.inj h1
      have h2 := Prod.mk.inj h1.2
      exact Or.inl ⟨h2.1.symm, p.name, List.mem_map.mpr ⟨p, hp, rfl⟩, h1.1⟩
    · have h1 := Prod.mk.inj h1
      have h2 := Prod.mk.inj h1.2
      exact Or.inr (Or.inl ⟨h2.1.symm, k, hk, h1.1⟩)
    · obtain ⟨h1, _, w, hw, h4⟩ := tagW_mem b 0 _ ht
      exact Or.inr (Or.inr ⟨h1, w, hw, h4⟩)
  have uniq : ∀ e1 ∈ entsOf m b, ∀ e2 ∈ entsOf m b, e1.code = e2.code → e1 = e2 := by
    intro e1 h1 e2 h2 hc
    have a := hf e1 h1
    have b := hf e2 h2
    rw [hc] at a
    rw [a] at b
    exact Option.some.inj b
  have hkeys : (nextKeys b).Nodup := by
    have h1 : ((entsOf m b).map Ent.code).Nodup := hnd
    rw [entsOf, numberE_code] at h1
    simp only [rawE, List.map_append, List.map_map] at h1
    have h2 : ((nextKeys b).map ncode).Nodup := by
      refine List.Nodup.sublist ?_ h1
      refine List.Sublist.trans ?_ (List.sublist_append_left _ (List.map (fun x => x.1) (tagW b 0)))
      exact List.sublist_append_right _ _
    exact nodup_of_map' ncode _ h2
  have hwo : woCheck [] b = true := by
    refine wo_aux (entsOf m b) _ hf b 0 [] hEtag (by intro d hd; simp at hd) hrdo
  -- membership in the table
  have hex : ∀ n, exOk (NT.build Ent.key (entsOf m b)) n = true →
      n ∈ m.inputs.map (·.name) ∨ n ∈ nextKeys b ∨ n ∈ writesOf b := by
    intro n hn
    unfold exOk at hn
    cases hfd : (NT.build Ent.key (entsOf m b)).find (skey (ncode n)) with
    | none => rw [hfd] at hn; simp at hn
    | some e =>
      rw [hfd] at hn
      have hc : e.code = ncode n := Nat.eq_of_beq_eq_true hn
      rcases hEpos e (hpos _ _ hfd) with ⟨_, x, hx, hxc⟩ | ⟨_, x, hx, hxc⟩ | ⟨_, x, hx, hxc⟩
      · exact Or.inl (ncode_inj (hxc.trans hc) ▸ hx)
      · exact Or.inr (Or.inl (ncode_inj (hxc.trans hc) ▸ hx))
      · exact Or.inr (Or.inr (ncode_inj (hxc.trans hc) ▸ hx))
  have hdisj : ∀ x e1 e2 (_ : e1 ∈ entsOf m b) (_ : e2 ∈ entsOf m b), e1.code = ncode x → e2.code = ncode x →
      e1.kind ≠ e2.kind → False := by
    intro x e1 e2 h1 h2 c1 c2 hk
    have := uniq e1 h1 e2 h2 (c1.trans c2.symm)
    exact hk (by rw [this])
  simp only [OrderOkM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
    Bool.not_eq_true', Bool.not_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨isPermOf_complete hP, hwo⟩, hkeys⟩, hmem⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro s hs x hx
    have := hloc s hs x hx
    simpa using this
  · intro s hs x hx
    rcases hex x (rdEx_all _ b hrdx s hs x hx) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · intro p hp
    have hn := hout p hp
    unfold outOk at hn
    cases hfd : (NT.build Ent.key (entsOf m b)).find (skey (ncode p.name)) with
    | none => rw [hfd] at hn; simp at hn
    | some e =>
      rw [hfd] at hn
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
      have hc : e.code = ncode p.name := Nat.eq_of_beq_eq_true hn.1
      have hk : e.kind ≠ 0 := by
        intro h0; rw [h0] at hn; simp at hn
      rcases hEpos e (hpos _ _ hfd) with ⟨h0, _⟩ | ⟨_, x, hx, hxc⟩ | ⟨_, x, hx, hxc⟩
      · exact absurd h0 hk
      · exact Or.inl (ncode_inj (hxc.trans hc) ▸ hx)
      · exact Or.inr (ncode_inj (hxc.trans hc) ▸ hx)
  · intro x hx
    obtain ⟨j, g, hW⟩ := hEW x hx
    constructor
    · apply contains_false_of
      intro hI
      obtain ⟨g', hI'⟩ := hEI x (by simpa using hI)
      exact hdisj x _ _ hW hI' rfl rfl (by simp)
    · apply contains_false_of
      intro hK
      obtain ⟨g', hK'⟩ := hEK x hK
      exact hdisj x _ _ hW hK' rfl rfl (by simp)
  · intro x hx
    apply contains_false_of
    intro hI
    obtain ⟨g, hK⟩ := hEK x hx
    obtain ⟨g', hI'⟩ := hEI x (by simpa using hI)
    exact hdisj x _ _ hK hI' rfl rfl (by simp)

theorem OrderOkM'_sound (m : Module) (b : List Stmt) (h : OrderOkM' m b = true) : OrderOkM m b = true := by
  simp only [OrderOkM', Bool.and_eq_true] at h
  exact OrderOkM_of_parts m b h.1.1 h.1.2 h.2

end Tools.VedMemOrder
