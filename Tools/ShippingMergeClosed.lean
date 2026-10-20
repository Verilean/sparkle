import Tools.ShippingPostSoundness
import Tools.ShippingTypedPostSoundness
import Sparkle.IR.Machine

/-! # The duplicate merge keeps the reads closed (K2)

The full entry returns the core module after the zero-width cleanup and the
checked merge. On an assignment-only body the merge is kept only if
`validateMerge` accepts it, statement by statement; from that check: the new
body drives the same names in the same order, and each of its statements
reads names the old statement read, or — where a reference was replaced by
its representative, or the statement became an alias — a name DEFINED
earlier (the check's own `defined` list). So a body closed over a set of
names stays closed over it: no statement is left reading a wire whose
driver the merge removed. -/
namespace Tools.ShippingMergeClosed
open Sparkle.IR.AST Sparkle.IR.RegDedup Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingPostSoundness (refs_renameE)

theorem lookup_mem : ∀ (A : List (String × String)) (x y : String),
    A.lookup x = some y → (x, y) ∈ A
  | [], _, _, h => by simp at h
  | (a, b) :: A, x, y, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i heq
      cases h
      have : x = a := by simpa using heq
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem A x y h)

/-- A substituted reference is a substitution's target or the reference. -/
theorem aliasOf_cases (A : List (String × String)) (x : String) :
    aliasOf A x = x ∨ (x, aliasOf A x) ∈ A := by
  unfold aliasOf
  cases h : A.lookup x with
  | none => exact Or.inl rfl
  | some y => exact Or.inr (lookup_mem A x y h)

/-- **One validated statement.** With the substitution's targets and the
defined names in `Sacc`, and the old statement reading names of `Sacc`: the
new statement reads names of `Sacc`, drives the same name, and the state's
targets and defined names are in `Sacc` plus that name. -/
theorem validateStep_closed {wOf : String → Nat} {allLhs : List String} {st st' : MergeCheck}
    {a b : Stmt} {Sacc : List String}
    (h : validateStep wOf allLhs st a b = some st')
    (hS : ∀ l y, (l, y) ∈ st.S → y ∈ Sacc) (hD : ∀ y ∈ st.defined, y ∈ Sacc)
    (hr : ∀ x ∈ stmtReads a, x ∈ Sacc) :
    (∀ x ∈ stmtReads b, x ∈ Sacc) ∧ stmtWrites b = stmtWrites a ∧
      (∀ l y, (l, y) ∈ st'.S → y ∈ Sacc ++ stmtWrites a) ∧
      (∀ y ∈ st'.defined, y ∈ Sacc ++ stmtWrites a) := by
  cases a with
  | assign l e =>
    cases b with
    | assign l' e' =>
      simp only [validateStep] at h
      split at h
      · cases h
      · rename_i h1
        have hl : l' = l := by
          by_cases hne : l' = l
          · exact hne
          · exact absurd (Or.inl hne) h1
        subst hl
        split at h
        · cases h
        · split at h
          · rename_i he
            cases h
            refine ⟨?_, rfl, fun l y hm => List.mem_append_left _ (hS l y hm), ?_⟩
            · intro x hx
              have hx' : x ∈ refsOf (renameE (aliasOf st.S) e) := he ▸ hx
              obtain ⟨z, hz, rfl⟩ := refs_renameE _ e x hx'
              rcases aliasOf_cases st.S z with h0 | h0
              · rw [h0]; exact hr z hz
              · exact hS _ _ h0
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact List.mem_append_right _ (by simp [stmtWrites])
              · exact List.mem_append_left _ (hD y hy)
          · split at h
            · rename_i y _
              split at h
              · rename_i hcond
                cases h
                have hy : y ∈ st.defined := by simpa using hcond.2.1
                refine ⟨?_, rfl, ?_, ?_⟩
                · intro x hx
                  have : x = y := by simpa [stmtReads, refsOf] using hx
                  exact this ▸ hD y hy
                · intro l1 y1 hm
                  rcases List.mem_cons.mp hm with e1 | hm
                  · cases e1
                    exact List.mem_append_left _ (hD _ hy)
                  · exact List.mem_append_left _ (hS l1 y1 hm)
                · intro y1 hy1
                  rcases List.mem_cons.mp hy1 with rfl | hy1
                  · exact List.mem_append_right _ (by simp [stmtWrites])
                  · exact List.mem_append_left _ (hD y1 hy1)
              · cases h
            · cases h
    | _ => simp [validateStep] at h
  | _ => simp [validateStep] at h

theorem validateMerge_go_closed {wOf : String → Nat} {allLhs : List String} :
    ∀ (old new : List Stmt) (st : MergeCheck) (Sacc : List String),
      validateMerge.go wOf allLhs st old new = true →
      (∀ l y, (l, y) ∈ st.S → y ∈ Sacc) → (∀ y ∈ st.defined, y ∈ Sacc) →
      readsClosedB Sacc old = true →
      readsClosedB Sacc new = true ∧ writesOf new = writesOf old
  | [], [], _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _, _, _ => by simp [validateMerge.go] at h
  | _ :: _, [], _, _, h, _, _, _ => by simp [validateMerge.go] at h
  | a :: as, b :: bs, st, Sacc, h, hS, hD, hc => by
    simp only [validateMerge.go] at h
    split at h
    · rename_i st' hstep
      simp only [readsClosedB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨hrb, hw, hS', hD'⟩ := validateStep_closed hstep hS hD hc.1
      obtain ⟨ih1, ih2⟩ := validateMerge_go_closed as bs st' (Sacc ++ stmtWrites a) h hS' hD' hc.2
      refine ⟨?_, ?_⟩
      · simp only [readsClosedB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
        exact ⟨hrb, by rw [hw]; exact ih1⟩
      · show stmtWrites b ++ writesOf bs = stmtWrites a ++ writesOf as
        rw [hw, ih2]
    · cases h

/-- **A validated merge keeps the reads closed and the driven names.** -/
theorem validateMerge_closed {wOf : String → Nat} {old new : List Stmt} {S : List String}
    (h : validateMerge wOf old new = true) (hc : readsClosedB S old = true) :
    readsClosedB S new = true ∧ writesOf new = writesOf old :=
  validateMerge_go_closed old new {} S h (fun _ _ hm => by cases hm) (fun _ hm => by cases hm) hc

theorem mergeDuplicates_closed {m : Module} {S : List String}
    (hall : m.body.all isAssign = true) (hc : readsClosedB S m.body = true) :
    readsClosedB S (mergeDuplicates m).body = true ∧
      writesOf (mergeDuplicates m).body = writesOf m.body := by
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv
    exact validateMerge_closed hv hc
  · exact ⟨hc, rfl⟩

/-- The checked merge of an assignment-only body. -/
theorem mergeChecked_closed {m : Module} {S : List String}
    (hall : m.body.all isAssign = true) (hc : readsClosedB S m.body = true) :
    readsClosedB S (Sparkle.IR.RefineCheck.mergeChecked m).body = true ∧
      writesOf (Sparkle.IR.RefineCheck.mergeChecked m).body = writesOf m.body := by
  have : Sparkle.IR.RefineCheck.mergeChecked m = mergeDuplicates m := by
    unfold Sparkle.IR.RefineCheck.mergeChecked
    simp only [hall, if_true]
  rw [this]
  exact mergeDuplicates_closed hall hc

end Tools.ShippingMergeClosed
