import Tools.ShippingControlOptSoundness

/-! # A cast statement survives the validated merge (round par/b-33)

WRITTEN, NOT BUILT.

`Tools.ShippingControlOptSoundness` (BUILT) proves that a COMPARISON
statement survives `mergeDuplicates` on a simple assignment-only body
(`mergeDuplicates_hasControl`): `validateStep` accepts a new statement only
as the renamed old one or as an alias of an earlier representative with the
same canonical right-hand side, and renaming keeps the root of an
expression. The same holds, with the same proof, for the CAST roots
(`isCastExpr`: a part-select, a concatenation, a unary NOT) — the shapes on
which `checkedOptimize` keeps its input (`checkedOptimize_cast`).

`cast_rename` is new. Everything after it is the text of
`Tools/ShippingControlOptSoundness.lean` 107–199 (`NoControlDefs` …
`mergeDuplicates_hasControl`), produced by a script with exactly these
substitutions: `isControlExpr` ↦ `isCastExpr`, `control_rename` ↦
`cast_rename`, `NoControlDefs` ↦ `NoCastDefs`, `HasControl` ↦ `HasCast`, and
the four theorem names (`…noControl` ↦ `…noCast`, `…hasControl` ↦
`…hasCast`). No other change.

Use: the full entry's module of a slotless machine drives its output by a
part-select of the packed wire (`Sparkle.IR.Machine.outAssigns`), so its
body has a cast statement, and so has its merged form — hence
`checkedOptimize b = b` (`Tools/ShippingCombLeafShape.lean`). -/
namespace Tools.ShippingCastMerge
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck Sparkle.IR.RegDedup
open Sparkle.IR.ZeroWidth
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness
open Tools.ShippingTypedPostSoundness
open Tools.ShippingControlOptSoundness (isCastExpr HasCast)

/-- Renaming keeps the cast root of an expression. -/
theorem cast_rename (σ : String → String) (e : Expr) :
    isCastExpr (renameE σ e) = isCastExpr e := by
  cases e with
  | op op args =>
    cases args with
    | nil => cases op <;> first | rfl | simp [isCastExpr, renameE, renameE.renameL]
    | cons a rest =>
      cases rest with
      | nil => cases op <;> first | rfl | simp [isCastExpr, renameE, renameE.renameL]
      | cons b rest2 => cases op <;> first | rfl | simp [isCastExpr, renameE, renameE.renameL]
  | _ => first | rfl | simp [isCastExpr, renameE, renameE.renameL]

/-- The representative table contains no cast-root expressions. -/
def NoCastDefs (defs : List (String × Expr)) : Prop :=
  ∀ x e, defs.lookup x = some e → isCastExpr e = false

theorem NoCastDefs.cons {defs} (h : NoCastDefs defs) (x : String) (e : Expr)
    (he : isCastExpr e = false) : NoCastDefs ((x, e) :: defs) := by
  intro y r hr
  by_cases hy : y == x
  · simp [List.lookup_cons, hy] at hr
    subst r; exact he
  · simp [List.lookup_cons, hy] at hr
    exact h y r hr

/-- A cast-free proposed statement cannot hide a cast
behind an alias: an alias must name an earlier representative with the same
canonical RHS. -/
theorem validateStep_noCast {we allLhs st st' l e l' e'}
    (h : validateStep we allLhs st (.assign l e) (.assign l' e') = some st')
    (hn : isCastExpr e' = false) (hd : NoCastDefs st.R) :
    isCastExpr e = false ∧ NoCastDefs st'.R := by
  simp only [validateStep] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i he
        have hroot : isCastExpr e = false := by rw [he, cast_rename] at hn; exact hn
        cases h
        exact ⟨hroot, hd.cons _ _ (by rw [cast_rename]; exact hroot)⟩
      · cases e' with
        | ref y =>
          simp only at h
          split at h
          · rename_i hc
            obtain ⟨_, _, _, hr, _⟩ := hc
            have hroot := hd y _ hr
            rw [cast_rename] at hroot
            cases h
            exact ⟨hroot, hd⟩
          · cases h
        | _ => simp at h

theorem validateMerge_go_noCast {we allLhs} :
    ∀ old new st, validateMerge.go we allLhs st old new = true →
      SimpleStmts old → NoCastDefs st.R →
      (∀ l e, .assign l e ∈ new → isCastExpr e = false) →
      ∀ l e, .assign l e ∈ old → isCastExpr e = false
  | [], [], _, _, _, _, _, _, _, h => by cases h
  | [], _ :: _, _, h, _, _, _, _, _, _ => by simp [validateMerge.go] at h
  | _ :: _, [], _, h, _, _, _, _, _, _ => by simp [validateMerge.go] at h
  | a :: as, b :: bs, st, h, hs, hd, hn, l, e, hm => by
    obtain ⟨la, ea, rfl, _⟩ := hs a List.mem_cons_self
    simp only [validateMerge.go] at h
    split at h
    · rename_i st' hstep
      obtain ⟨eb, rfl, _⟩ := validateStep_shape hstep
      obtain ⟨ha, hd'⟩ := validateStep_noCast hstep (hn la eb (by simp)) hd
      rcases List.mem_cons.mp hm with heq | hm
      · cases heq; exact ha
      · exact validateMerge_go_noCast as bs st' h
          (fun s hm => hs s (List.mem_cons_of_mem _ hm)) hd'
          (fun l e hm => hn l e (List.mem_cons_of_mem _ hm)) l e hm
    · cases h

theorem validateMerge_hasCast {we old new}
    (hv : validateMerge we old new = true) (hs : SimpleStmts old) (hc : HasCast old) :
    HasCast new := by
  apply Classical.byContradiction
  intro hn
  have hn' : ∀ l e, .assign l e ∈ new → isCastExpr e = false := by
    intro l e he
    cases hh : isCastExpr e with
    | false => rfl
    | true => exact (hn ⟨l, e, he, hh⟩).elim
  have ho := validateMerge_go_noCast old new {} hv hs
    (by intro x e h; cases h) hn'
  obtain ⟨l, e, hm, he⟩ := hc
  rw [ho l e hm] at he
  cases he

theorem mergeDuplicates_hasCast (m : Sparkle.IR.AST.Module)
    (hs : SimpleStmts m.body) (hc : HasCast m.body) : HasCast (mergeDuplicates m).body := by
  have hall : m.body.all isAssign = true := by
    rw [List.all_eq_true]
    intro s hm
    obtain ⟨l, e, rfl, _⟩ := hs s hm
    rfl
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv; exact validateMerge_hasCast hv hs hc
  · exact hc

end Tools.ShippingCastMerge
