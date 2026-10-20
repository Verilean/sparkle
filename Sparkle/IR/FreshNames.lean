import Std.Data.HashSet.Lemmas
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas

/-! Total numeric-suffix allocation. At most `used.size + 1` consecutive
distinct candidates can be occupied by `used.size` names. The bound is proved,
so the computational default in `freshSuffix` is unreachable. No oracle or
unbounded loop is required, and the suffix cache can supply any starting index. -/

namespace Sparkle.IR.FreshNames

def numbered (base : String) (n : Nat) : String := base ++ "_" ++ toString n

theorem numbered_injective (base : String) {i j : Nat}
    (h : numbered base i = numbered base j) : i = j := by
  have hlist := congrArg String.toList h
  simp only [numbered, String.toList_append] at hlist
  have hd := List.append_cancel_left hlist
  have hnum := congrArg (fun ds => Nat.ofDigitChars 10 ds 0) hd
  simpa [Nat.toString_eq_ofList_toDigits] using hnum

def seek (used : Std.HashSet String) (base : String) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, start =>
    if used.contains (numbered base start) then seek used base fuel (start + 1)
    else some start

theorem seek_sound (used : Std.HashSet String) (base : String)
    (fuel start n : Nat) (h : seek used base fuel start = some n) :
    used.contains (numbered base n) = false ∧ start ≤ n := by
  induction fuel generalizing start with
  | zero => simp [seek] at h
  | succ fuel ih =>
    simp only [seek] at h
    split at h
    · obtain ⟨hu, hn⟩ := ih (start + 1) h
      exact ⟨hu, by omega⟩
    · have hn : start = n := Option.some.inj h
      rename_i hnot
      subst n
      exact ⟨by simpa using hnot, Nat.le_refl _⟩

theorem seek_none (used : Std.HashSet String) (base : String)
    (fuel start : Nat) (h : seek used base fuel start = none) :
    ∀ i, i < fuel → used.contains (numbered base (start + i)) = true := by
  induction fuel generalizing start with
  | zero => intro i hi; omega
  | succ fuel ih =>
    simp only [seek] at h
    split at h
    · rename_i hu
      intro i hi
      cases i with
      | zero => simpa using hu
      | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (ih (start + 1) h i (by omega))
    · contradiction

private theorem covered_length (base : String) (fuel : Nat) :
    ∀ (names : List String) (start : Nat),
      (∀ i, i < fuel → numbered base (start + i) ∈ names) → fuel ≤ names.length := by
  induction fuel with
  | zero => intros; omega
  | succ fuel ih =>
    intro names start h
    have hz : numbered base start ∈ names := by simpa using h 0 (by omega)
    have ht : ∀ i, i < fuel →
        numbered base (start + 1 + i) ∈ names.erase (numbered base start) := by
      intro i hi
      apply (List.mem_erase_of_ne ?_).mpr
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i + 1) (by omega)
      · intro he
        have := numbered_injective base he
        omega
    have hn := ih (names.erase (numbered base start)) (start + 1) ht
    rw [List.length_erase_of_mem hz] at hn
    have hp := List.length_pos_iff_exists_mem.mpr ⟨_, hz⟩
    omega

theorem seek_exists (used : Std.HashSet String) (base : String) (start : Nat) :
    ∃ n, seek used base (used.size + 1) start = some n := by
  cases h : seek used base (used.size + 1) start with
  | some n => exact ⟨n, rfl⟩
  | none =>
    have hc := seek_none used base (used.size + 1) start h
    have hl := covered_length base (used.size + 1) used.toList start (by
      intro i hi
      exact Std.HashSet.mem_toList.mpr (Std.HashSet.contains_iff_mem.mp (hc i hi)))
    rw [Std.HashSet.length_toList] at hl
    omega

def freshSuffix (used : Std.HashSet String) (base : String) (start : Nat) : Nat :=
  (seek used base (used.size + 1) start).getD start

theorem freshSuffix_spec (used : Std.HashSet String) (base : String) (start : Nat) :
    used.contains (numbered base (freshSuffix used base start)) = false ∧
      start ≤ freshSuffix used base start := by
  obtain ⟨n, hn⟩ := seek_exists used base start
  simpa [freshSuffix, hn] using seek_sound used base (used.size + 1) start n hn

end Sparkle.IR.FreshNames
