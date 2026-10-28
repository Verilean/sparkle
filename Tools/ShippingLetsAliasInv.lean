import Sparkle.Compiler.Elab

/-! # Unit LC2: the alias condition behind `letsClose_of_data`, at the reader

BUILT: lc2c exit 0 (Tools.ShippingLetsAliasInv); audit lc2d (ChildVertAuditTest). No sorry/axiom/native_decide.

`letsClose_of_data` consumes `letsAliasOk`: a `let` field that is the variable of another `let`
reads one whose field is a variable. The reader that makes the `let`s is `st.lets : MachLets`,
written ONLY by `machBindLet`, `machBindLetNamed`, `machBindLetAlias`, `machLetIndex`
(`Sparkle/Compiler/Elab.lean` 3619–3671, 3744–3750; call sites 4009, 4070, 4110, 4174, 4187–4190, 5130).
These four are NON-`partial` total functions, so their specification is provable directly.

PROVED here (pure, about those four functions only):
* `NoLetAlias lets`: no `let` value is itself a `_machLet` placeholder;
* it holds for `{}` and is kept by `machBindLet` and `machLetIndex` unconditionally, by `machBindLetNamed`
  when its value is not a `let` placeholder, by `machBindLetAlias` when a `let`-placeholder value is IN
  RANGE (`j < lets.size`);
* `machClose_bvar`: a value that is not a `let` placeholder (and not a loose `bvar`) is never closed to a
  `bvar` of index `< k + d`, i.e. a `let` field never points at a `let` (`machClose` writes `bvar (k-1-j+d)`
  only for `_machLet j`).

NOT proved (the missing reader lemma, see REPORT-LC2.md): the in-range premise of `machBindLetAlias`, i.e.
"a converted value `v'` that is a `_machLet j` has `j < st.lets.size`", for the results of the `partial`
readers `machConv`/`machChain`/`machLoopBody` (and "no loose `bvar` as a `let` value"). Also NOT proved: the
link from the Expr-level `let` values to the typed `d.letFields` / `quote` equation, which is on the
proof-generation side. -/
namespace Tools.ShippingLetsAliasInv
open Lean Sparkle.Compiler.Elab

/-- No `let` value is itself a `let` placeholder. -/
def NoLetAlias (lets : MachLets) : Prop := ∀ l ∈ lets.toList, machIsLetVar l.2.2 = false

theorem noLetAlias_empty : NoLetAlias (#[] : MachLets) := by
  intro l hl; simp at hl

theorem machIsLetVar_machIsVar {e : Lean.Expr} (h : machIsLetVar e = true) : machIsVar e = true := by
  unfold machIsLetVar at h
  split at h <;> first | (unfold machIsVar; simp) | cases h

theorem machIsLetVar_machLet (j : Nat) : machIsLetVar (machLet j) = true := by
  simp [machIsLetVar, machLet]

theorem machIsLetVar_iff {e : Lean.Expr} (h : machIsLetVar e = true) : ∃ j, e = machLet j := by
  unfold machIsLetVar at h
  split at h
  · next j => exact ⟨j, rfl⟩
  · cases h

private theorem noLetAlias_push {lets : MachLets} {nm : Name} {k : MixedGateBinder} {v : Lean.Expr}
    (H : NoLetAlias lets) (hv : machIsLetVar v = false) : NoLetAlias (lets.push (nm, k, v)) := by
  intro l hl
  rw [Array.toList_push] at hl
  rcases List.mem_append.mp hl with hl | hl
  · exact H l hl
  · rw [List.mem_singleton.mp hl]; exact hv

theorem machBindLet_noAlias {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} (H : NoLetAlias lets) :
    NoLetAlias (machBindLet nm ty v' lets).2 := by
  unfold machBindLet
  split
  · exact H
  · exact H
  · split
    · exact H
    · next hnv =>
      split
      · exact H
      · apply noLetAlias_push H
        cases h : machIsLetVar v'
        · rfl
        · exact absurd (machIsLetVar_machIsVar h) (by simpa using hnv)

theorem machBindLetNamed_noAlias {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (H : NoLetAlias lets) (hv : machIsLetVar v' = false) :
    NoLetAlias (machBindLetNamed nm ty v' lets).2 := by
  unfold machBindLetNamed
  split
  · exact H
  · exact H
  · split
    · exact H
    · exact noLetAlias_push H hv

theorem machLetIndex_noAlias {nm : Name} {k : MixedGateBinder} {v' : Lean.Expr} {lets : MachLets}
    (H : NoLetAlias lets) : NoLetAlias (machLetIndex nm k v' lets).2 := by
  unfold machLetIndex
  split
  · exact H
  · next hn =>
    split
    · exact H
    · apply noLetAlias_push H
      cases h : machIsLetVar v'
      · rfl
      · obtain ⟨j, rfl⟩ := machIsLetVar_iff h
        exact absurd rfl (hn j)

/-- The `resolve` of `machBindLetAlias` leaves a non-`let`-placeholder alone. -/
private theorem resolve_nonLetVar (lets : MachLets) :
    ∀ (fuel : Nat) (e : Lean.Expr), machIsLetVar e = false →
      machBindLetAlias.resolve lets fuel e = e := by
  intro fuel e he
  cases fuel with
  | zero => simp [machBindLetAlias.resolve]
  | succ f =>
    unfold machBindLetAlias.resolve
    split <;> first | rfl | (exfalso; simp_all [machIsLetVar])

/-- **`machBindLetAlias` keeps `NoLetAlias`**, provided a `let`-placeholder value is in range. -/
theorem machBindLetAlias_noAlias {nm : Name} {ty v' : Lean.Expr} {lets : MachLets}
    (H : NoLetAlias lets)
    (hr : ∀ j, v' = machLet j → j < lets.size) :
    NoLetAlias (machBindLetAlias nm ty v' lets).2 := by
  unfold machBindLetAlias
  have hval : machIsLetVar (machBindLetAlias.resolve lets lets.size v') = false := by
    cases hv : machIsLetVar v'
    · rw [resolve_nonLetVar lets _ _ hv]; exact hv
    · obtain ⟨j, rfl⟩ := machIsLetVar_iff hv
      have hj := hr j rfl
      have hpos : lets.size = (lets.size - 1) + 1 := by omega
      rw [hpos]
      unfold machBindLetAlias.resolve
      simp only [machLet]
      have hget : lets[j]? = some lets[j] := by simp [hj]
      rw [hget]
      dsimp only
      have hnl := H lets[j] (by simp [Array.getElem_mem_toList])
      cases hf : lets.size - 1 with
      | zero => simpa [machBindLetAlias.resolve] using hnl
      | succ f => rw [resolve_nonLetVar lets _ _ hnl]; exact hnl
  have hne : ¬ (machIsLetVar (machBindLetAlias.resolve lets lets.size v') = true) := by
    simp [hval]
  rw [if_neg hne]
  split
  · exact H
  · exact H
  · dsimp only
    split
    · exact H
    · exact noLetAlias_push H hval

/-- A `let` field after `machClose` is not a bound variable that points at a `let` — a bound variable is
below `k` only for a `let` placeholder (`bvar (k-1-j+d)`) and the other placeholders map to indices `≥ k + d`. -/
theorem machClose_bvar {kI n k d : Nat} {e : Lean.Expr} (he : machIsLetVar e = false)
    (hb : ∀ b, e ≠ .bvar b) :
    ∀ b, machClose kI n k d e = .bvar b → k + d ≤ b := by
  intro b h
  unfold machClose at h
  split at h
  · injection h with h; omega
  · injection h with h; omega
  · injection h with h; omega
  · exfalso; simp_all [machIsLetVar]
  · cases h
  · cases h
  · cases h
  · exact absurd h (hb b)

end Tools.ShippingLetsAliasInv
