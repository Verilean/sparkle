import Tools.VedU2HierOrder

/-!
# VED compose: a fast equivalent of the acceptance check `OrderOkHS` (new path only)

`OrderOkHS d m b` (Tools/VedU2HierOrder.lean) is a closed `Bool`; the generated parent proof evaluates it in the kernel.  Its
cost is quadratic in the number of statements / wires, with a String comparison as the unit step: `WOH` scans the writes of the
rest for every read, the read-definedness conjunct scans `inNames`, `regOuts b`, `wrsH d b` for every read, `isPermOf` erases.

`OrderOkFast d m b` is ONE pass over the arrangement with a hashed binary search tree of the names defined so far
(`NTree`: keys are a 32-bit mix of the name, a node keeps the names of its key, the final test is the exact String compare), so
a lookup / insertion costs O(log n) key comparisons (Nat comparisons, kernel GMP) and a name is read by the kernel once per
occurrence.  `orderOkFast_sound : OrderOkFast d m b = true → OrderOkHS d m b = true` is proved from two facts about the tree
only (`has_empty`, `has_ins1`), so the hash is never trusted: a bad hash can only cost time or refuse, never accept.
-/

namespace Tools.VedCompose

open Sparkle.IR.AST Sparkle.IR.Reorder Tools.VedU1Hier Tools.VedU2Hier Tools.VedU1Contract

/-- A 32-bit finaliser (murmur3 `fmix32`); consecutive keys must not stay consecutive (the tree is unbalanced). -/
def mix32 (x : Nat) : Nat :=
  let x := x ^^^ (x >>> 16)
  let x := (x * 2246822507) % 4294967296
  let x := x ^^^ (x >>> 13)
  let x := (x * 3266489909) % 4294967296
  x ^^^ (x >>> 16)

/-- The search key of an exact key `k` (any function would do for soundness: it only places the node). -/
def hsh (k : Nat) : Nat := mix32 (k % 4294967296)

/-- The exact key of a list of bytes: base 257 with digits `b + 1 ∈ [1, 256]` (so injective). -/
def keyList (l : List UInt8) : Nat := l.foldr (fun b acc => (b.toNat + 1) + 257 * acc) 0

theorem keyList_inj : ∀ (l₁ l₂ : List UInt8), keyList l₁ = keyList l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons b l => simp only [keyList, List.foldr_nil, List.foldr_cons] at h; omega
  | cons a l₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp only [keyList, List.foldr_nil, List.foldr_cons] at h; omega
    | cons b l₂ =>
      simp only [keyList, List.foldr_cons] at h
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      have h1 : a.toNat = b.toNat := by omega
      have h2 : keyList l₁ = keyList l₂ := by simp only [keyList]; omega
      have := ih l₂ h2
      have h3 : a = b := UInt8.toNat_inj.mp h1
      rw [h3, this]

/-- The exact key of a name: its UTF-8 bytes (reading the bytes of a literal costs the kernel next to nothing; a character
list or a `String` compare costs milliseconds). -/
def nameKey (s : String) : Nat := keyList s.toByteArray.data.toList

theorem nameKey_inj {s t : String} (h : nameKey s = nameKey t) : s = t := by
  have h1 := keyList_inj _ _ h
  have h2 : s.toByteArray.data = t.toByteArray.data := Array.toList_inj.mp h1
  have h3 : s.toByteArray = t.toByteArray := ByteArray.ext h2
  cases s; cases t
  simp_all

/-- A binary search tree on the search keys; a node keeps the exact keys that have its search key. -/
inductive NTree where
  | leaf : NTree
  | node (k : Nat) (names : List Nat) (l r : NTree) : NTree

def NTree.mem (h : Nat) (s : Nat) : NTree → Bool
  | .leaf => false
  | .node k ns l r =>
    if h = k then ns.contains s else if h < k then l.mem h s else r.mem h s

def NTree.ins (h : Nat) (s : Nat) : NTree → NTree
  | .leaf => .node h [s] .leaf .leaf
  | .node k ns l r =>
    if h = k then .node k (s :: ns) l r
    else if h < k then .node k ns (l.ins h s) r else .node k ns l (r.ins h s)

theorem NTree.mem_ins (h h' : Nat) (s s' : Nat) (t : NTree) :
    (t.ins h' s').mem h s = true ↔ (h = h' ∧ s = s') ∨ t.mem h s = true := by
  induction t with
  | leaf =>
    simp only [NTree.ins, NTree.mem]
    by_cases hh : h = h'
    · simp [hh, List.contains_iff_mem]
    · by_cases hlt : h < h' <;> simp [hh, hlt]
  | node k ns l r ihl ihr =>
    simp only [NTree.ins]
    by_cases hk : h' = k
    · subst hk
      by_cases hh : h = h'
      · subst hh
        simp only [NTree.mem, if_true]
        simp [List.contains_iff_mem]
      · by_cases hlt : h < h' <;> simp [NTree.mem, hh, hlt]
    · by_cases hlt' : h' < k
      · simp only [hk, hlt', if_true, if_false, NTree.mem]
        by_cases hh : h = k
        · simp [hh, Ne.symm hk]
        · by_cases hlt : h < k
          · simp [hh, hlt, ihl]
          · simp [hh, hlt]
            intro e; omega
      · simp only [hk, hlt', if_false, NTree.mem]
        by_cases hh : h = k
        · simp [hh, Ne.symm hk]
        · by_cases hlt : h < k
          · simp [hh, hlt]
            intro e; omega
          · simp [hh, hlt, ihr]

def hasK (t : NTree) (k : Nat) : Bool := t.mem (hsh k) k
def insK (t : NTree) (k : Nat) : NTree := t.ins (hsh k) k

theorem hasK_insK (t : NTree) (k' k : Nat) : hasK (insK t k') k = true ↔ k = k' ∨ hasK t k = true := by
  unfold hasK insK
  rw [NTree.mem_ins]
  constructor
  · rintro (⟨_, h⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨by rw [h], h⟩
    · exact Or.inr h

def has (t : NTree) (n : String) : Bool := hasK t (nameKey n)
def ins1 (t : NTree) (n : String) : NTree := insK t (nameKey n)

theorem has_empty (n : String) : has .leaf n = false := rfl

theorem has_ins1 (t : NTree) (s n : String) :
    has (ins1 t s) n = true ↔ n = s ∨ has t n = true := by
  unfold has ins1
  rw [hasK_insK]
  constructor
  · rintro (h | h)
    · exact Or.inl (nameKey_inj h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr h

theorem has_foldl (l : List String) : ∀ (t : NTree) (n : String),
    has (l.foldl ins1 t) n = true ↔ n ∈ l ∨ has t n = true := by
  induction l with
  | nil => intro t n; simp
  | cons a l ih =>
    intro t n
    simp only [List.foldl_cons, ih, has_ins1, List.mem_cons]
    constructor
    · rintro (h | h | h) <;> simp [h]
    · rintro ((h | h) | h) <;> simp [h]

/-- Insert the names, each of which must be new (this also forces them to be distinct). -/
def insAll : List String → NTree → Option NTree
  | [], t => some t
  | w :: ws, t => if has t w then none else insAll ws (ins1 t w)

theorem insAll_sound : ∀ (ws : List String) (t t' : NTree), insAll ws t = some t' →
    ws.Nodup ∧ (∀ w ∈ ws, has t w = false) ∧ ∀ n, has t' n = true ↔ has t n = true ∨ n ∈ ws := by
  intro ws
  induction ws with
  | nil =>
    intro t t' h
    simp only [insAll, Option.some.injEq] at h
    subst h; simp
  | cons w ws ih =>
    intro t t' h
    simp only [insAll] at h
    by_cases hw : has t w = true
    · simp [hw] at h
    · simp only [hw, Bool.false_eq_true, if_false] at h
      obtain ⟨hnd, hfresh, hiff⟩ := ih _ _ h
      have hw' : has t w = false := by simpa using hw
      refine ⟨?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, hnd⟩
        intro hmem
        have := hfresh w hmem
        have h2 : has (ins1 t w) w = true := (has_ins1 t w w).mpr (Or.inl rfl)
        rw [h2] at this; exact absurd this (by simp)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hw'
        · have := hfresh x hx
          cases hh : has t x
          · rfl
          · have h2 : has (ins1 t w) x = true := (has_ins1 t w x).mpr (Or.inr hh)
            rw [h2] at this; exact absurd this (by simp)
      · intro n
        rw [hiff, has_ins1, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h

/-- The reads of a register's input expression (deferred to the end: they may read a later wire). -/
def regReads : Stmt → Option (List String)
  | .register _ _ _ e _ => some (refsOf e)
  | _ => none

theorem regReads_some {d : Design} {s : Stmt} {rr : List String} (h : regReads s = some rr) :
    allReadsHS d s = rr ∧ rdH d s = [] ∧ wrH d s = [] := by
  cases s <;> simp_all [regReads, allReadsHS, rdH, wrH]

theorem regReads_none {d : Design} {s : Stmt} (h : regReads s = none) : allReadsHS d s = rdH d s := by
  cases s <;> simp_all [regReads, allReadsHS, rdH, wrH]

/-- One pass in arrangement order: a non-register statement reads only names already defined and defines new ones. -/
def pass (d : Design) : List Stmt → NTree → List String → Option (NTree × List String)
  | [], t, R => some (t, R)
  | s :: rest, t, R =>
    match regReads s with
    | some rr => pass d rest t (rr ++ R)
    | none =>
      if (rdH d s).all (has t) then
        match insAll (wrH d s) t with
        | some t' => pass d rest t' R
        | none => none
      else none

theorem pass_sound (d : Design) : ∀ (b : List Stmt) (t : NTree) (R : List String) (t' : NTree) (R' : List String),
    pass d b t R = some (t', R') →
    WOH d b ∧ (∀ n ∈ wrsH d b, has t n = false) ∧
    (∀ n, has t' n = true → has t n = true ∨ n ∈ wrsH d b) ∧
    (∀ n, has t n = true → has t' n = true) ∧
    (∀ n ∈ wrsH d b, has t' n = true) ∧
    (∀ s ∈ b, ∀ n ∈ allReadsHS d s, has t' n = true ∨ n ∈ R') ∧
    (∀ n ∈ R, n ∈ R') := by
  intro b
  induction b with
  | nil =>
    intro t R t' R' h
    simp only [pass, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [WOH, wrsH]
  | cons s rest ih =>
    intro t R t' R' h
    simp only [pass] at h
    cases hr : regReads s with
    | some rr =>
      rw [hr] at h
      simp only at h
      obtain ⟨hw, hdis, hsub, hmono, hwr, hrd, hR⟩ := ih _ _ _ _ h
      obtain ⟨hall, hrd0, hwr0⟩ := regReads_some (d := d) hr
      simp only [wrsH, List.flatMap_cons, hwr0, List.nil_append] at hdis hsub hwr ⊢
      refine ⟨?_, hdis, hsub, hmono, hwr, ?_, fun n hn => hR n (List.mem_append_right _ hn)⟩
      · simp only [WOH, hrd0, hwr0]
        refine ⟨by simp, by simp, List.nodup_nil, ?_⟩
        simpa [wrsH] using hw
      · intro s' hs' n hn
        rcases List.mem_cons.mp hs' with rfl | hs'
        · right; rw [hall] at hn; exact hR n (List.mem_append_left _ hn)
        · exact hrd s' hs' n hn
    | none =>
      rw [hr] at h
      simp only at h
      by_cases hrd1 : (rdH d s).all (has t) = true
      · rw [if_pos hrd1] at h
        cases hi : insAll (wrH d s) t with
        | none => rw [hi] at h; simp at h
        | some t1 =>
          rw [hi] at h
          simp only at h
          obtain ⟨hnd, hfresh, hiff⟩ := insAll_sound _ _ _ hi
          obtain ⟨hw, hdis, hsub, hmono, hwr, hrd, hR⟩ := ih _ _ _ _ h
          have hrd2 : ∀ n ∈ rdH d s, has t n = true := fun n hn => List.all_eq_true.mp hrd1 n hn
          have hwsH : wrsH d (s :: rest) = wrH d s ++ wrsH d rest := by simp [wrsH, List.flatMap_cons]
          have hin1 : ∀ n ∈ wrH d s, has t1 n = true := fun n hn => (hiff n).mpr (Or.inr hn)
          have ht1 : ∀ n, has t n = true → has t1 n = true := fun n hn => (hiff n).mpr (Or.inl hn)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hR⟩
          · refine ⟨?_, ?_, hnd, hw⟩
            · intro n hn
              have h1 := hrd2 n hn
              refine ⟨fun hm => ?_, fun hm => ?_⟩
              · have := hdis n hm
                have := ht1 n h1
                simp_all
              · have := hfresh n hm
                simp_all
            · intro n hn hm
              have := hdis n hm
              have := hin1 n hn
              simp_all
          · intro n hn
            rw [hwsH] at hn
            rcases List.mem_append.mp hn with hn | hn
            · exact hfresh n hn
            · cases hh : has t n
              · rfl
              · have := hdis n hn
                have := ht1 n hh
                simp_all
          · intro n hn
            rw [hwsH]
            rcases hsub n hn with h2 | h2
            · rcases (hiff n).mp h2 with h3 | h3
              · exact Or.inl h3
              · exact Or.inr (List.mem_append_left _ h3)
            · exact Or.inr (List.mem_append_right _ h2)
          · intro n hn; exact hmono n (ht1 n hn)
          · intro n hn
            rw [hwsH] at hn
            rcases List.mem_append.mp hn with hn | hn
            · exact hmono n (hin1 n hn)
            · exact hwr n hn
          · intro s' hs' n hn
            rcases List.mem_cons.mp hs' with rfl | hs'
            · rw [regReads_none (d := d) hr] at hn
              exact Or.inl (hmono n (ht1 n (hrd2 n hn)))
            · exact hrd s' hs' n hn
      · rw [if_neg hrd1] at h; simp at h

/-- Insert the keys, each of which must be new (so the list has no duplicate). -/
def insAllK : List Nat → NTree → Option NTree
  | [], t => some t
  | k :: ks, t => if hasK t k then none else insAllK ks (insK t k)

theorem insAllK_sound : ∀ (ks : List Nat) (t t' : NTree), insAllK ks t = some t' →
    ks.Nodup ∧ (∀ k ∈ ks, hasK t k = false) ∧ ∀ n, hasK t' n = true ↔ hasK t n = true ∨ n ∈ ks := by
  intro ks
  induction ks with
  | nil =>
    intro t t' h
    simp only [insAllK, Option.some.injEq] at h
    subst h; simp
  | cons w ws ih =>
    intro t t' h
    simp only [insAllK] at h
    by_cases hw : hasK t w = true
    · simp [hw] at h
    · simp only [hw, Bool.false_eq_true, if_false] at h
      obtain ⟨hnd, hfresh, hiff⟩ := ih _ _ h
      have hw' : hasK t w = false := by simpa using hw
      have hin : hasK (insK t w) w = true := (hasK_insK t w w).mpr (Or.inl rfl)
      refine ⟨?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩
        have := hfresh w hmem
        rw [hin] at this; exact absurd this (by simp)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hw'
        · have := hfresh x hx
          cases hh : hasK t x
          · rfl
          · have h2 : hasK (insK t w) x = true := (hasK_insK t w x).mpr (Or.inr hh)
            rw [h2] at this; exact absurd this (by simp)
      · intro n
        rw [hiff, hasK_insK, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h

/-- The arrangement is the body read at the indices `σ`. -/
def permBy (σ : List Nat) (body : List Stmt) : List Stmt :=
  σ.map fun i => body.getD i (.assign "" (.ref ""))

/-- Generator side (not trusted): the indices of the body that give the arrangement `b` (each body statement used once). -/
def permIdx (body b : List Stmt) : List Nat := Id.run do
  let arr := body.toArray
  let mut used : Array Bool := Array.replicate arr.size false
  let mut out : Array Nat := #[]
  for s in b do
    let mut found : Option Nat := none
    for i in [0:arr.size] do
      if found.isNone && !(used.getD i true) then
        match arr[i]? with
        | some t => if decide (t = s) then found := some i
        | none => pure ()
    if let some i := found then
      used := used.set! i true
      out := out.push i
  return out.toList

/-- `σ` lists each index below `n` exactly once. -/
def permOk (σ : List Nat) (n : Nat) : Bool :=
  match insAllK σ .leaf with
  | none => false
  | some t => σ.all (· < n) && (List.range n).all (hasK t)

theorem permBy_perm {σ : List Nat} {body : List Stmt} (h : permOk σ body.length = true) :
    (permBy σ body).Perm body := by
  unfold permOk at h
  cases hi : insAllK σ .leaf with
  | none => rw [hi] at h; simp at h
  | some t =>
    rw [hi] at h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
    obtain ⟨hlt, hcov⟩ := h
    obtain ⟨hnd, -, hiff⟩ := insAllK_sound _ _ _ hi
    have hmem : ∀ i, i ∈ σ ↔ i < body.length := by
      intro i
      constructor
      · exact hlt i
      · intro hi'
        have := (hiff i).mp (hcov i hi')
        rcases this with h1 | h1
        · simp [hasK, NTree.mem] at h1
        · exact h1
    have hp : σ.Perm (List.range body.length) := by
      rw [List.perm_iff_count]
      intro a
      rw [hnd.count, (List.nodup_range).count]
      simp only [hmem a, List.mem_range]
    have hmap : (List.range body.length).map (fun i => body.getD i (.assign "" (.ref ""))) = body := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp at h1
        simp [List.getD_eq_getElem?_getD, h1]
    have := hp.map (fun i => body.getD i (.assign "" (.ref "")))
    rw [hmap] at this
    exact this

theorem isPermOf_complete [DecidableEq α] : ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → isPermOf l₁ l₂ = true := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons _ _ => exact absurd h.length_eq (by simp)
  | cons a rest ih =>
    intro l₂ h
    have hmem : a ∈ l₂ := h.subset (List.mem_cons_self)
    simp only [isPermOf, if_pos hmem]
    exact ih (List.cons_perm_iff_perm_erase.mp h).2

/-- The fast check: the same verdict as `OrderOkHS` is implied (`orderOkFast_sound`). -/
def OrderOkFast (d : Design) (m : Module) (b : List Stmt) : Bool :=
  b.all isAsgInstReg &&
  (let I0 := (inNames m).foldl ins1 .leaf
   match insAll (regOuts b) I0 with
   | none => false
   | some t0 =>
     match pass d b t0 [] with
     | none => false
     | some (t, R) => R.all (has t) && m.outputs.all (fun p => !has I0 p.name && has t p.name))

theorem orderOkFast_sound {d : Design} {m : Module} {b : List Stmt} {σ : List Nat}
    (hb : b = permBy σ m.body) (hσ : permOk σ m.body.length = true) (h : OrderOkFast d m b = true) :
    OrderOkHS d m b = true := by
  have hperm : isPermOf b m.body = true := isPermOf_complete (hb ▸ permBy_perm hσ)
  unfold OrderOkFast at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hai, hrest⟩ := h
  generalize hI0 : (inNames m).foldl ins1 .leaf = I0 at hrest
  cases hg : insAll (regOuts b) I0 with
  | none => rw [hg] at hrest; simp at hrest
  | some t0 =>
    rw [hg] at hrest
    simp only at hrest
    cases hp : pass d b t0 [] with
    | none => rw [hp] at hrest; simp at hrest
    | some p =>
      obtain ⟨t, R⟩ := p
      rw [hp] at hrest
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hrest
      obtain ⟨hR, hout⟩ := hrest
      obtain ⟨hgnd, hgfresh, hgiff⟩ := insAll_sound _ _ _ hg
      obtain ⟨hw, hdis, hsub, hmono, hwr, hrd, -⟩ := pass_sound d b t0 [] t R hp
      have hI : ∀ n, has I0 n = true ↔ n ∈ inNames m := by
        intro n; rw [← hI0, has_foldl]; simp [has_empty]
      have h0 : ∀ n, has t0 n = true ↔ n ∈ inNames m ∨ n ∈ regOuts b := by
        intro n; rw [hgiff, hI]
      -- membership in the final set is membership in inputs, register outputs or writes
      have hfin : ∀ n, has t n = true → n ∈ inNames m ∨ n ∈ regOuts b ∨ n ∈ wrsH d b := by
        intro n hn
        rcases hsub n hn with h1 | h1
        · rcases (h0 n).mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h1)
      unfold OrderOkHS
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨⟨⟨hperm, hw⟩, hai⟩, hgnd⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · -- every read is an input, a register output or a write
        refine List.all_eq_true.mpr fun s hs => List.all_eq_true.mpr fun n hn => ?_
        have hn' : has t n = true := by
          rcases hrd s hs n hn with h1 | h1
          · exact h1
          · exact hR n h1
        simp only [Bool.or_eq_true, List.contains_iff_mem]
        rcases hfin n hn' with h1 | h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
      · -- every output is driven
        refine List.all_eq_true.mpr fun p hp => ?_
        have ⟨hni, hmemt⟩ := hout p hp
        simp only [Bool.or_eq_true, List.contains_iff_mem]
        have hni' : p.name ∉ inNames m := fun hh => by
          have := (hI p.name).mpr hh; simp_all
        rcases hfin p.name hmemt with h1 | h1 | h1
        · exact absurd h1 hni'
        · exact Or.inl h1
        · exact Or.inr h1
      · -- no write is an input or a register output
        refine List.all_eq_true.mpr fun n hn => ?_
        have h1 := hdis n hn
        have hi : (inNames m).contains n = false := by
          cases hh : (inNames m).contains n
          · rfl
          · have := (h0 n).mpr (Or.inl (List.contains_iff_mem.mp hh)); simp_all
        have hr : (regOuts b).contains n = false := by
          cases hh : (regOuts b).contains n
          · rfl
          · have := (h0 n).mpr (Or.inr (List.contains_iff_mem.mp hh)); simp_all
        rw [hi, hr]; rfl
      · -- no register output is an input
        refine List.all_eq_true.mpr fun n hn => ?_
        have h1 := hgfresh n hn
        cases hh : (inNames m).contains n
        · rfl
        · have := (hI n).mpr (List.contains_iff_mem.mp hh); simp_all

/-! ## Measurement only: the conjuncts of `OrderOkHS` as separate closed checks (`VED_COMPOSE_FACT_ONLY`) -/

def ordP1 (_d : Design) (m : Module) (b : List Stmt) : Bool := isPermOf b m.body
def ordP2 (d : Design) (_m : Module) (b : List Stmt) : Bool := decide (WOH d b)
def ordP3 (_d : Design) (_m : Module) (b : List Stmt) : Bool := b.all isAsgInstReg
def ordP4 (_d : Design) (_m : Module) (b : List Stmt) : Bool := decide (regOuts b).Nodup
def ordP5 (d : Design) (m : Module) (b : List Stmt) : Bool :=
  b.all (fun s => (allReadsHS d s).all (fun n =>
    (inNames m).contains n || (regOuts b).contains n || (wrsH d b).contains n))
def ordP6 (d : Design) (m : Module) (b : List Stmt) : Bool :=
  m.outputs.all (fun p => (regOuts b).contains p.name || (wrsH d b).contains p.name)
def ordP7 (d : Design) (m : Module) (b : List Stmt) : Bool :=
  (wrsH d b).all (fun n => !(inNames m).contains n && !(regOuts b).contains n)
def ordP8 (_d : Design) (m : Module) (b : List Stmt) : Bool := (regOuts b).all (fun n => !(inNames m).contains n)

end Tools.VedCompose
