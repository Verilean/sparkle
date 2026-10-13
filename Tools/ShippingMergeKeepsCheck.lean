import Tools.ShippingMergeKeeps

/-! # `LastNonAssign`, decided (round par/a-30)

A Boolean form of the hypothesis of `Tools/ShippingMergeKeeps.lean`, for
hand-written modules: `lastNonAssignB body = true ↔ LastNonAssign body`
(the two directions are `lastNonAssignB_sound` and
`lastNonAssign_checked`). Used by the test to show that the probe module
`mergeCex` is OUTSIDE the hypothesis. Nothing in the leaf chain uses this
file.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMergeKeeps
open Sparkle.IR.AST Std
open Sparkle.IR.RegDedup (definedNode isAssign)

/-- The statement is not an assignment to the name `st` defines. -/
def notTarget (st : Stmt) : Stmt → Bool
  | .assign l _ => definedNode st != some l
  | _ => true

/-- Some non-assignment statement is followed by no assignment to its name. -/
def lastNonAssignB : List Stmt → Bool
  | [] => false
  | st :: post => (!isAssign st && post.all (notTarget st)) || lastNonAssignB post

theorem notTarget_all {st : Stmt} {post : List Stmt}
    (hp : ∀ l r, Stmt.assign l r ∈ post → definedNode st ≠ some l) :
    post.all (notTarget st) = true := by
  rw [List.all_eq_true]
  intro s hs
  cases s with
  | assign l r =>
    have h := hp l r hs
    show (definedNode st != some l) = true
    simpa using h
  | _ => rfl

/-- **Completeness of the check**: a body with the hypothesis passes. -/
theorem lastNonAssign_checked : ∀ (pre : List Stmt) (st : Stmt) (post : List Stmt),
    isAssign st = false → (∀ l r, Stmt.assign l r ∈ post → definedNode st ≠ some l) →
    lastNonAssignB (pre ++ st :: post) = true
  | [], st, post, hs, hp => by
    show ((!isAssign st && post.all (notTarget st)) || lastNonAssignB post) = true
    rw [hs, notTarget_all hp]
    first
      | done
      | rfl
  | a :: pre, st, post, hs, hp => by
    have ih := lastNonAssign_checked pre st post hs hp
    show ((!isAssign a && (pre ++ st :: post).all (notTarget a)) ||
      lastNonAssignB (pre ++ st :: post)) = true
    rw [ih]
    first
      | done
      | exact Bool.or_true _
      | simp

theorem lastNonAssignB_of {body : List Stmt} (h : LastNonAssign body) :
    lastNonAssignB body = true := by
  obtain ⟨pre, st, post, hb, hs, hp⟩ := h
  rw [hb]
  exact lastNonAssign_checked pre st post hs hp

/-- A body the check refuses does not have the hypothesis. -/
theorem not_lastNonAssign {body : List Stmt} (h : lastNonAssignB body = false) :
    ¬ LastNonAssign body := by
  intro hL
  have h2 := lastNonAssignB_of hL
  rw [h] at h2
  cases h2

/-- **Soundness of the check**: a body that passes has the hypothesis. -/
theorem lastNonAssignB_sound : ∀ (body : List Stmt), lastNonAssignB body = true →
    LastNonAssign body
  | [], h => by
    have h' : false = true := h
    cases h'
  | st :: post, h => by
    have h' : ((!isAssign st && post.all (notTarget st)) || lastNonAssignB post) = true := h
    cases hrest : lastNonAssignB post with
    | true =>
      obtain ⟨pre, s, po, hb, hs, hp⟩ := lastNonAssignB_sound post hrest
      refine ⟨st :: pre, s, po, ?_, hs, hp⟩
      rw [hb]
      first
        | done
        | rfl
    | false =>
      rw [hrest, Bool.or_false, Bool.and_eq_true] at h'
      obtain ⟨h1, h2⟩ := h'
      have hs : isAssign st = false := by
        cases hq : isAssign st with
        | true =>
          rw [hq] at h1
          simp at h1
        | false => rfl
      refine ⟨[], st, post, rfl, hs, ?_⟩
      intro l r hm hdn
      have h3 := List.all_eq_true.mp h2 _ hm
      have h4 : (definedNode st != some l) = true := h3
      rw [hdn] at h4
      simp at h4

end Tools.ShippingMergeKeeps
