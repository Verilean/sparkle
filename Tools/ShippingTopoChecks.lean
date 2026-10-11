import Tools.ShippingTopoBody
import Sparkle.IR.ReorderInvariance

/-! # The order checks of `closeInsts` hold of `topoBody`'s result

`closeInsts` keeps the reordered body only if `woCheck`, `isPermOf` and the
equality of the register / memory statements hold of it. Here they follow
from what `topoBody_some` returns (a dependency order of the combinational
statements, the others after), for a body whose assignments drive distinct
names and whose other statements are registers. Pure statements about
lists. -/
namespace Tools.ShippingTopoChecks
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingTopoBody

/-! ## Permutations -/

theorem isPermOf_complete {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → isPermOf l₁ l₂ = true
  | [], l₂, h => by
    have := h.length_eq
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at this
  | a :: rest, l₂, h => by
    have hmem : a ∈ l₂ := h.subset (List.mem_cons_self ..)
    simp only [isPermOf, if_pos hmem]
    exact isPermOf_complete ((h.trans (List.perm_cons_erase hmem)).cons_inv)

/-- A combinational statement. -/
def isComb : Stmt → Bool
  | .assign .. | .inst .. => true
  | _ => false

theorem combOf_eq (body : List Stmt) : combOf body = body.filter isComb := by
  unfold combOf
  congr 1
  try (funext st; cases st <;> rfl)

theorem othersOf_eq (body : List Stmt) : othersOf body = body.filter (fun st => !isComb st) := by
  unfold othersOf
  congr 1
  try (funext st; cases st <;> rfl)

/-- The body is its combinational statements and the others. -/
theorem perm_split (body : List Stmt) : body.Perm (combOf body ++ othersOf body) := by
  rw [combOf_eq, othersOf_eq]
  exact (List.filter_append_perm isComb body).symm

theorem seqOf_comb : ∀ (l : List Stmt), (∀ st ∈ l, isComb st = true) → seqOf l = []
  | [], _ => rfl
  | st :: l, h => by
    have h1 := h st (List.mem_cons_self ..)
    have ih := seqOf_comb l (fun s hs => h s (List.mem_cons_of_mem _ hs))
    unfold seqOf at ih ⊢
    cases st <;> simp_all [isComb]

theorem seqOf_append (a b : List Stmt) : seqOf (a ++ b) = seqOf a ++ seqOf b := by
  unfold seqOf
  exact List.filter_append ..

/-- The register and memory statements of a body are those of its
non-combinational part, in order. -/
theorem seqOf_others : ∀ (body : List Stmt), seqOf body = seqOf (othersOf body)
  | [] => rfl
  | st :: body => by
    have ih := seqOf_others body
    rw [othersOf_eq] at ih ⊢
    unfold seqOf at ih ⊢
    cases st <;> simp_all [isComb]

/-- The register / memory statements are unchanged by the reordering. -/
theorem seqOf_sorted {body sorted : List Stmt} (hperm : sorted.Perm (combOf body)) :
    seqOf body = seqOf (sorted ++ othersOf body) := by
  rw [seqOf_append, seqOf_comb sorted (by
    intro st hs
    have := hperm.subset hs
    rw [combOf_eq] at this
    exact (List.mem_filter.mp this).2), List.nil_append]
  exact seqOf_others body

/-! ## `woCheck` -/

/-- A register. -/
def isReg : Stmt → Bool
  | .register .. => true
  | _ => false

theorem woCheck_regs : ∀ (l : List Stmt) (done : List String), (∀ st ∈ l, isReg st = true) →
    woCheck done l = true
  | [], _, _ => rfl
  | st :: l, done, h => by
    have h1 := h st (List.mem_cons_self ..)
    have ih := woCheck_regs l (done ++ stmtWrites st) (fun s hs => h s (List.mem_cons_of_mem _ hs))
    cases st <;> simp_all [isReg, woCheck, stmtReads, stmtWrites]

theorem writesOf_regs : ∀ (l : List Stmt), (∀ st ∈ l, isReg st = true) → writesOf l = []
  | [], _ => rfl
  | st :: l, h => by
    have h1 := h st (List.mem_cons_self ..)
    have ih := writesOf_regs l (fun s hs => h s (List.mem_cons_of_mem _ hs))
    unfold writesOf at ih ⊢
    cases st <;> simp_all [isReg, stmtWrites]

theorem writesOf_append (a b : List Stmt) : writesOf (a ++ b) = writesOf a ++ writesOf b := by
  unfold writesOf
  exact List.flatMap_append ..

/-- The reads of a combinational statement the order tracks include the
reads `woCheck` looks at. -/
theorem stmtReads_comb (A : List String) : ∀ (st : Stmt), isComb st = true →
    ∀ n ∈ stmtReads st, n ∈ combReads A st
  | .assign _ _, _, n, h => h
  | .inst _ _ _, _, n, h => by simp [stmtReads] at h
  | .register .., h, _, _ => by simp [isComb] at h
  | .memory .., h, _, _ => by simp [isComb] at h

/-- What an assignment writes is what the order settles; an instance writes
nothing `woCheck` sees, and settles names no assignment drives. -/
theorem combWrites_spec (A : List String) : ∀ (st : Stmt), isComb st = true →
    (∀ n ∈ stmtWrites st, n ∈ combWrites A st) ∧
    (∀ n ∈ combWrites A st, n ∈ stmtWrites st ∨ n ∉ A)
  | .assign _ _, _ => ⟨fun _ h => h, fun _ h => Or.inl h⟩
  | .inst _ _ conns, _ => by
    refine ⟨fun n h => by simp [stmtWrites] at h, fun n h => Or.inr ?_⟩
    simp only [combWrites, List.mem_filterMap] at h
    obtain ⟨⟨p, e⟩, _, he⟩ := h
    cases e <;> simp only [] at he <;> try cases he
    split at he
    · cases he
    · rename_i hn
      cases he
      simpa using hn
  | .register .., h => by simp [isComb] at h
  | .memory .., h => by simp [isComb] at h

/-- **`woCheck` of a dependency order**: from settled names `S` no later
assignment drives, evaluated names `done` likewise, assignments driving
distinct names, all of them in `A ⊆ D`. -/
theorem woCheck_ordered (A D : List String) (hAD : ∀ n, n ∈ A → n ∈ D)
    (others : List Stmt) (hreg : ∀ st ∈ others, isReg st = true) :
    ∀ (L : List Stmt) (S done : List String), (∀ st ∈ L, isComb st = true) →
      Ordered A D S L → (writesOf L).Nodup → (∀ n ∈ writesOf L, n ∈ A) →
      (∀ n ∈ S, n ∉ writesOf L) → (∀ n ∈ done, n ∉ writesOf L) →
      woCheck done (L ++ others) = true
  | [], _, done, _, _, _, _, _, _ => woCheck_regs others done hreg
  | st :: L, S, done, hc, ho, hnd, hA, hS, hdone => by
    have hcs := hc st (List.mem_cons_self ..)
    have hw : writesOf (st :: L) = stmtWrites st ++ writesOf L := rfl
    rw [hw] at hnd hA hS hdone
    obtain ⟨hnd1, hnd2, hdisj⟩ := List.nodup_append.mp hnd
    have hready := ho.1
    simp only [readyB, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
      Bool.not_eq_true'] at hready
    have hrest : writesOf (L ++ others) = writesOf L := by
      rw [writesOf_append, writesOf_regs others hreg, List.append_nil]
    show woCheck done (st :: (L ++ others)) = true
    simp only [woCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', hrest]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro n hn
      have hn' := stmtReads_comb A st hcs n hn
      rcases hready n hn' with hs | hd
      · have := hS n hs
        simpa using fun h => this (List.mem_append_right _ h)
      · have : n ∉ A := fun h => by
          have := hAD n h
          simp_all
        simpa using fun h => this (hA n (List.mem_append_right _ h))
    · intro n hn
      refine ⟨?_, ?_⟩
      · simpa using fun h => hdone n h (List.mem_append_left _ hn)
      · simpa using fun h => hdisj n hn n h rfl
    · refine woCheck_ordered A D hAD others hreg L (combWrites A st ++ S) (done ++ stmtWrites st)
        (fun s hs => hc s (List.mem_cons_of_mem _ hs)) ho.2 hnd2
        (fun n hn => hA n (List.mem_append_right _ hn)) ?_ ?_
      · intro n hn hL
        rcases List.mem_append.mp hn with h1 | h2
        · rcases (combWrites_spec A st hcs).2 n h1 with h3 | h3
          · exact hdisj n h3 n hL rfl
          · exact h3 (hA n (List.mem_append_right _ hL))
        · exact hS n h2 (List.mem_append_right _ hL)
      · intro n hn hL
        rcases List.mem_append.mp hn with h1 | h2
        · exact hdone n h1 (List.mem_append_right _ hL)
        · exact hdisj n h2 n hL rfl

end Tools.ShippingTopoChecks
