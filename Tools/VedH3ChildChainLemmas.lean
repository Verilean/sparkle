import Tools.DeepElab

/-!
# VED compose, multi-circuit parent (unit 23): a dead trailing register of the open parent's deep circuit

The open parent's deep circuit `Cdo (Γp ++ ex) Γi w` may keep registers the synthesized design does not have (R220: hftStrategy's counter,
read only by an output the declaration drops).  The generator (option `ved.compose.multiCircuit`) then states the register invariant
and the register-step facts over the first `n = |Γp|` slots only.  What makes that sound is this closed check:

* `CExpr.usesIn lo hi e`: some variable of `e` has context index in `[lo, hi)`.
* `slotUnused c n`: no next-state cone of a register `i < n`, and not the output cone, reads a register slot `j` with
  `n ≤ j < |Γr|` (the extra slots; a slot's own next-state cone is not checked: a counter may read itself).  Only a TRAILING block of
  slots is covered: slot `j ≥ n` of a circuit whose dead register is in the middle is read by a live cone (or not a prefix match), and the check
  is false there.
* `CExpr.denote_irrel`: a cone that does not read `[lo, hi)` has the same value under two environments that agree off `[lo, hi)`.
* `Cdo.next_prefix_irrel`, `Cdo.out_prefix_irrel`: under `slotUnused c n` the next value of a register `i < n` and the output of the
  joined environment do not depend on the extra slots' values.

Nothing here is a statement of the final contract; `U2HRStmt` is untouched.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics

namespace Tools.VedH3ChildChain

/-- Some variable of the cone has context index in `[lo, hi)`. -/
def usesIn (lo hi : Nat) : {Γ : List Nat} → {w : Nat} → CExpr Γ w → Bool
  | _, _, .const _ _ => false
  | _, _, .var i => decide (lo ≤ i.val ∧ i.val < hi)
  | _, _, .add a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .sub a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .mux c t e => usesIn lo hi c || usesIn lo hi t || usesIn lo hi e
  | _, _, .eq a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .and a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .or a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .xor a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .mul a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .shl a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .shr a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .lt a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .le a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .cat a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .slt a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .sle a b => usesIn lo hi a || usesIn lo hi b
  | _, _, .slice a _ _ => usesIn lo hi a
  | _, _, .not a => usesIn lo hi a
  | _, _, .neg a => usesIn lo hi a

/-- The closed check: the registers `i < n` and the output do not read the extra register slots `[n, |Γr|)`. -/
def slotUnused {Γr Γi : List Nat} {wOut : Nat} (c : Cdo Γr Γi wOut) (n : Nat) : Bool :=
  (List.range Γr.length).all (fun i =>
    decide (n ≤ i) || (if h : i < Γr.length then !usesIn n Γr.length (c.next ⟨i, h⟩) else true)) &&
    !usesIn n Γr.length c.out

/-- A cone that does not read `[lo, hi)` is insensitive to the values there. -/
theorem CExpr.denote_irrel {Γ : List Nat} {w : Nat} (lo hi : Nat) (e : CExpr Γ w) (h : usesIn lo hi e = false)
    (ρ ρ' : CEnv Γ) (hag : ∀ i : Fin Γ.length, ¬ (lo ≤ i.val ∧ i.val < hi) → ρ i = ρ' i) :
    e.denote ρ = e.denote ρ' := by
  induction e with
  | const _ _ => rfl
  | var i =>
    simp only [usesIn, decide_eq_false_iff_not] at h
    exact hag i h
  | mux c t e ihc iht ihe =>
    simp only [usesIn, Bool.or_eq_false_iff] at h
    simp only [CExpr.denote, ihc h.1.1, iht h.1.2, ihe h.2]
  | slice a hi' lo' iha =>
    simp only [usesIn] at h
    simp only [CExpr.denote, iha h]
  | not a iha =>
    simp only [usesIn] at h
    simp only [CExpr.denote, iha h]
  | neg a iha =>
    simp only [usesIn] at h
    simp only [CExpr.denote, iha h]
  | _ a b iha ihb =>
    simp only [usesIn, Bool.or_eq_false_iff] at h
    simp only [CExpr.denote, iha h.1, ihb h.2]

/-- The joined environments of two register valuations that agree on the first `n` slots agree off `[n, |Γr|)`. -/
theorem join_agree {Γr Γi : List Nat} (n : Nat) (ρr ρr' : CEnv Γr) (ρi : CEnv Γi)
    (hr : ∀ j : Fin Γr.length, j.val < n → ρr j = ρr' j) :
    ∀ i : Fin (Γr ++ Γi).length, ¬ (n ≤ i.val ∧ i.val < Γr.length) →
      CEnv.join ρr ρi i = CEnv.join ρr' ρi i := by
  intro i hi
  unfold CEnv.join
  by_cases h : i.val < Γr.length
  · simp only [h, dite_true]
    have := hr ⟨i.val, h⟩ (by show i.val < n; omega)
    rw [this]
  · simp only [h, dite_false]

/-- **Register step over the first `n` slots**: under `slotUnused c n`, the next value of register `i < n` does not depend on the
values of the extra slots. -/
theorem Cdo.next_prefix_irrel {Γr Γi : List Nat} {wOut : Nat} (c : Cdo Γr Γi wOut) (n : Nat) (hu : slotUnused c n = true)
    (ρr ρr' : CEnv Γr) (ρi : CEnv Γi) (hr : ∀ j : Fin Γr.length, j.val < n → ρr j = ρr' j)
    (i : Fin Γr.length) (hi : i.val < n) :
    (c.next i).denote (CEnv.join ρr ρi) = (c.next i).denote (CEnv.join ρr' ρi) := by
  simp only [slotUnused, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hu
  have h1 := hu.1 i.val i.isLt
  simp only [Bool.or_eq_true, decide_eq_true_eq, i.isLt, dite_true, Bool.not_eq_true'] at h1
  rcases h1 with h | h
  · omega
  · exact CExpr.denote_irrel n Γr.length _ h _ _ (join_agree n ρr ρr' ρi hr)

/-- The output cone, likewise. -/
theorem Cdo.out_prefix_irrel {Γr Γi : List Nat} {wOut : Nat} (c : Cdo Γr Γi wOut) (n : Nat) (hu : slotUnused c n = true)
    (ρr ρr' : CEnv Γr) (ρi : CEnv Γi) (hr : ∀ j : Fin Γr.length, j.val < n → ρr j = ρr' j) :
    c.out.denote (CEnv.join ρr ρi) = c.out.denote (CEnv.join ρr' ρi) := by
  simp only [slotUnused, Bool.and_eq_true, Bool.not_eq_true'] at hu
  exact CExpr.denote_irrel n Γr.length _ hu.2 _ _ (join_agree n ρr ρr' ρi hr)

end Tools.VedH3ChildChain
