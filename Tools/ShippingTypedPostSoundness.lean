import Tools.ShippingTypedExprSoundness

/-! Mixed-width comparison/mux invariants through the shipping cleanup passes.
Widths are read from internal scalar declarations, with the single `out` port
kept explicit because it is not part of the internal width environment. -/
namespace Tools.ShippingTypedPostSoundness
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.IR.RegDedup Sparkle.IR.ZeroWidth
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness
open Tools.ShippingScalarSoundness Tools.ShippingTypedExprSoundness

/-- Per-assignment widths, rather than one width for the whole circuit. -/
def TypedStmts (we : WEnv) (body : List Stmt) : Prop :=
  ∀ st ∈ body, ∃ l e n, st = .assign l e ∧ TypedExpr we e n ∧ (we l = n ∨ l = "out")

theorem TypedStmts.isAssign {we body} (h : TypedStmts we body) :
    body.all isAssign = true := by
  rw [List.all_eq_true]
  intro st hs
  obtain ⟨l, e, n, rfl, _⟩ := h st hs
  rfl

theorem typed_rename {we e n} (h : TypedExpr we e n) (σ : String → String)
    (hw : ∀ x, we (σ x) = we x) : TypedExpr we (renameE σ e) n := by
  induction h with
  | ref x hn =>
    simpa only [renameE, hw] using TypedExpr.ref (we := we) (σ x) (by rw [hw]; exact hn)
  | const v n hn => exact .const v n hn
  | @bin op a b n ha hb hs ia ib =>
    have hs' : Sparkle.IR.PrintCheck.shiftShape op.operator (renameE σ b) = true := by
      cases op <;> cases b <;>
        simp_all only [Binary.operator, renameE, Sparkle.IR.PrintCheck.shiftShape]
    simpa only [renameE, renameE.renameL] using TypedExpr.bin op ia ib hs'
  | signedCompare a b ho hn he =>
    simpa only [renameE, renameE.renameL] using
      TypedExpr.signedCompare (we := we) (σ a) (σ b) ho (by simpa [hw] using hn) (by simpa [hw] using he)
  | compare ho _ _ ia ib =>
    simpa only [renameE, renameE.renameL] using TypedExpr.compare ho ia ib
  | mux _ _ _ ic it iff =>
    simpa only [renameE, renameE.renameL] using TypedExpr.mux ic it iff
  | zext x k hk hx =>
    have step := TypedExpr.zext (we := we) (σ x) k hk (by rw [hw]; exact hx)
    rw [hw] at step
    simpa only [renameE, renameE.renameL] using step
  | trunc x w hwid hwx =>
    have step := TypedExpr.trunc (we := we) (σ x) w hwid (by rw [hw]; exact hwx)
    simpa only [renameE, renameE.renameL] using step
  | slice x hi lo hle hhi =>
    simpa only [renameE] using
      TypedExpr.slice (we := we) (σ x) hi lo hle (by rw [hw]; exact hhi)
  | cat a b ha hb =>
    have step := TypedExpr.cat (we := we) (σ a) (σ b) (by rw [hw]; exact ha) (by rw [hw]; exact hb)
    simp only [hw] at step
    simpa only [renameE, renameE.renameL] using step

theorem validateStep_typed {we : WEnv} {n : Nat} {allLhs : List String}
    {st st' : MergeCheck} {l : String} {e : Expr} {new : Stmt}
    (hz : we "out" = 0)
    (h : validateStep we allLhs st (.assign l e) new = some st')
    (hs : TypedExpr we e n) (hl : we l = n ∨ l = "out")
    (hS : ∀ x, we (aliasOf st.S x) = we x)
    (hd : ∀ x ∈ st.defined, 0 < we x ∨ x = "out") :
    (∃ e', new = .assign l e' ∧ TypedExpr we e' n) ∧
    (∀ x, we (aliasOf st'.S x) = we x) ∧
    (∀ x ∈ st'.defined, 0 < we x ∨ x = "out") := by
  cases new with
  | assign l' e' =>
    simp only [validateStep] at h
    by_cases h1 : l' ≠ l ∨ l ∈ st.defined
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    have heq : l = l' := Classical.byContradiction fun hne => h1 (Or.inl (Ne.symm hne))
    subst heq
    by_cases h2 : (!(Sparkle.IR.Reorder.refsOf e).all (fun x => !allLhs.contains x || st.defined.contains x)) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    have hd' : ∀ x ∈ l :: st.defined, 0 < we x ∨ x = "out" := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases hl with hl | hl
        · exact Or.inl (hl ▸ hs.positive)
        · exact Or.inr hl
      · exact hd x hx
    by_cases h3 : e' = renameE (aliasOf st.S) e
    · rw [if_pos h3] at h
      cases h
      exact ⟨⟨_, rfl, h3 ▸ typed_rename hs _ hS⟩, hS, hd'⟩
    · rw [if_neg h3] at h
      cases e' with
      | ref y =>
        simp only at h
        split at h
        · rename_i hc
          obtain ⟨hne, hyd, _, _, hwy⟩ := hc
          cases h
          have hyd' : y ∈ st.defined := by simpa using hyd
          have hyn : we y = n := by
            rcases hl with hl | rfl
            · exact hwy.symm.trans hl
            · rcases hd y hyd' with hy | hy
              · rw [hz] at hwy; omega
              · exact False.elim (hne hy)
          refine ⟨⟨_, rfl, ?_⟩, ?_, hd'⟩
          · simpa only [hyn] using TypedExpr.ref (we := we) y (by rw [hyn]; exact hs.positive)
          · intro x
            rw [aliasOf_cons]
            split
            · rename_i hx; subst x; exact hwy.symm
            · exact hS x
        · cases h
      | _ => simp at h
  | _ => simp [validateStep] at h

theorem validateMerge_go_typed {we : WEnv} {allLhs : List String} (hz : we "out" = 0) :
    ∀ (old new : List Stmt) (st : MergeCheck),
      validateMerge.go we allLhs st old new = true → TypedStmts we old →
      (∀ x, we (aliasOf st.S x) = we x) →
      (∀ x ∈ st.defined, 0 < we x ∨ x = "out") → TypedStmts we new
  | [], [], _, _, _, _, _ => fun _ h => by cases h
  | [], _ :: _, _, h, _, _, _ => by simp [validateMerge.go] at h
  | _ :: _, [], _, h, _, _, _ => by simp [validateMerge.go] at h
  | a :: as, b :: bs, st, h, hs, hS, hd => by
    obtain ⟨l, e, n, rfl, he, hl⟩ := hs a List.mem_cons_self
    simp only [validateMerge.go] at h
    split at h
    · rename_i st' hstep
      obtain ⟨⟨e', rfl, he'⟩, hS', hd'⟩ := validateStep_typed hz hstep he hl hS hd
      have ht := validateMerge_go_typed hz as bs st' h
        (fun s hm => hs s (List.mem_cons_of_mem _ hm)) hS' hd'
      intro s hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨l, e', n, rfl, he', hl⟩
      · exact ht s hm
    · cases h

theorem validateMerge_typed {we : WEnv} {old new : List Stmt}
    (hz : we "out" = 0) (h : validateMerge we old new = true) (hs : TypedStmts we old) :
    TypedStmts we new :=
  validateMerge_go_typed hz old new {} h hs (fun _ => rfl) (fun _ hm => by cases hm)

theorem mergeDuplicates_typed {m : Sparkle.IR.AST.Module}
    (hz : weOf m "out" = 0) (hs : TypedStmts (weOf m) m.body) :
    TypedStmts (weOf (mergeDuplicates m)) (mergeDuplicates m).body := by
  have hall := hs.isAssign
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv
    exact validateMerge_typed hz hv hs
  · exact hs

/-- The distinguished output keeps its source width through merging. -/
def OutputTypedAt (outWidth : Nat) (we : WEnv) (body : List Stmt) : Prop :=
  ∀ e, Stmt.assign "out" e ∈ body → TypedExpr we e outWidth

abbrev OutputTyped := OutputTypedAt 1

theorem validateMerge_go_output {we : WEnv} {allLhs : List String} (hz : we "out" = 0) :
    ∀ (old new : List Stmt) (st : MergeCheck),
      validateMerge.go we allLhs st old new = true → TypedStmts we old → OutputTypedAt outWidth we old →
      (∀ x, we (aliasOf st.S x) = we x) →
      (∀ x ∈ st.defined, 0 < we x ∨ x = "out") → OutputTypedAt outWidth we new
  | [], [], _, _, _, _, _, _ => fun _ h => by cases h
  | [], _ :: _, _, h, _, _, _, _ => by simp [validateMerge.go] at h
  | _ :: _, [], _, h, _, _, _, _ => by simp [validateMerge.go] at h
  | a :: as, b :: bs, st, h, hs, ho, hS, hd => by
    obtain ⟨l, e, n, rfl, he, hl⟩ := hs a List.mem_cons_self
    simp only [validateMerge.go] at h
    split at h
    · rename_i st' hstep
      obtain ⟨⟨e', rfl, he'⟩, hS', hd'⟩ := validateStep_typed hz hstep he hl hS hd
      have ht := validateMerge_go_output hz as bs st' h
        (fun s hm => hs s (List.mem_cons_of_mem _ hm))
        (fun e hm => ho e (List.mem_cons_of_mem _ hm)) hS' hd'
      intro rhs hm
      rcases List.mem_cons.mp hm with eq | hm
      · cases eq
        have hn := he.width.symm.trans (ho e List.mem_cons_self).width
        exact hn ▸ he'
      · exact ht rhs hm
    · cases h

theorem mergeDuplicates_output {m : Sparkle.IR.AST.Module}
    (hz : weOf m "out" = 0) (hs : TypedStmts (weOf m) m.body)
    (ho : OutputTypedAt outWidth (weOf m) m.body) :
    OutputTypedAt outWidth (weOf (mergeDuplicates m)) (mergeDuplicates m).body := by
  unfold mergeDuplicates
  simp only [hs.isAssign, if_true]
  split
  · rename_i hv
    exact validateMerge_go_output hz _ _ {} hv hs ho (fun _ => rfl) (fun _ hm => by cases hm)
  · exact ho

theorem dzExpr_typed {we e n} (h : TypedExpr we e n) (wm : Sparkle.IR.Optimize.WidthMap)
    (hwm : ∀ x ∈ Sparkle.IR.Reorder.refsOf e, Sparkle.IR.ZeroWidth.exprWidth wm (.ref x) ≠ 0) :
    dzExpr wm e = e := by
  induction h with
  | ref | const => rfl
  | bin _ _ _ _ ia ib | compare _ _ _ ia ib =>
    have ia := ia (fun x hx => hwm x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have ib := ib (fun x hx => hwm x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    simp [dzExpr, dzList, ia, ib]
  | signedCompare => simp [dzExpr, dzList]
  | mux _ _ _ ic it iff =>
    have ic := ic (fun x hx => hwm x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have it := it (fun x hx => hwm x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have iff := iff (fun x hx => hwm x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    simp [dzExpr, dzList, ic, it, iff]
  | zext y k hk hy =>
    have hwy := hwm y (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have hyb : (Std.HashMap.getD wm y 0 != 0) = true := by
      simpa [Sparkle.IR.ZeroWidth.exprWidth, bne_iff_ne] using hwy
    have hk' : k ≠ 0 := by omega
    simp [dzExpr, dzList, Sparkle.IR.ZeroWidth.exprWidth, hk', hyb]
  | trunc y w hwid hwy' =>
    have hwy := hwm y (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have hyb : (Std.HashMap.getD wm y 0 != 0) = true := by
      simpa [Sparkle.IR.ZeroWidth.exprWidth, bne_iff_ne] using hwy
    have hw' : w ≠ 0 := by omega
    simp [dzExpr, dzList, Sparkle.IR.ZeroWidth.exprWidth, hw', hyb]
  | slice y hi lo hle hhi => simp [dzExpr]
  | cat a b ha hb =>
    have hwa := hwm a (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have hwb := hwm b (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have hab : (Std.HashMap.getD wm a 0 != 0) = true := by
      simpa [Sparkle.IR.ZeroWidth.exprWidth, bne_iff_ne] using hwa
    have hbb : (Std.HashMap.getD wm b 0 != 0) = true := by
      simpa [Sparkle.IR.ZeroWidth.exprWidth, bne_iff_ne] using hwb
    simp [dzExpr, dzList, Sparkle.IR.ZeroWidth.exprWidth, hab, hbb]

/-- Internal scalar declarations also occur in the cleanup width map.
In particular `bit` must be read as width one by both maps. -/
theorem widthMap_internal {m : Sparkle.IR.AST.Module} {x : String}
    (hnd : (m.wires.map (·.name)).Nodup) (hp : 0 < weOf m x) :
    (Sparkle.IR.Optimize.buildWidthMap m).get? x = some (weOf m x) := by
  unfold weOf at hp ⊢
  cases hf : m.wires.find? (fun p => p.name == x) with
  | none => simp [hf] at hp
  | some p =>
    have hm := List.mem_of_find?_eq_some hf
    have hx : p.name = x := by simpa using List.find?_some hf
    have hw := wmFold_mem m.wires
      ((m.inputs ++ m.outputs).foldl (fun acc p => acc.insert p.name p.ty.bitWidth) {}) p hnd hm
    rw [hx] at hw
    cases p with
    | mk name ty =>
      cases ty <;> simp_all [Sparkle.IR.Optimize.buildWidthMap, HWType.bitWidth]

/-- Structural premises for heterogeneous-width combinational cleanup.
The `out` port is intentionally absent from the internal width map. -/
structure TypedPostReady (m : Sparkle.IR.AST.Module) : Prop where
  wiresNodup : (m.wires.map (·.name)).Nodup
  outWidthZero : weOf m "out" = 0
  outNotZero : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" ≠ some 0
  typed : TypedStmts (weOf m) m.body

theorem dropZeroWidth_typed {m : Sparkle.IR.AST.Module} (h : TypedPostReady m) :
    (dropZeroWidthModule m).body = m.body ∧ weOf (dropZeroWidthModule m) = weOf m ∧
    (dropZeroWidthModule m).inputs = m.inputs ∧ (dropZeroWidthModule m).outputs = m.outputs ∧
    TypedStmts (weOf (dropZeroWidthModule m)) (dropZeroWidthModule m).body := by
  have hb : (dropZeroWidthModule m).body = m.body := by
    unfold dropZeroWidthModule
    split
    · rfl
    · apply filterMap_eq_self
      intro st hst
      obtain ⟨l, e, n, rfl, ht, hl⟩ := h.typed st hst
      have hnz : (Sparkle.IR.Optimize.buildWidthMap m).get? l ≠ some 0 := by
        rcases hl with hl | rfl
        · rw [widthMap_internal h.wiresNodup (by rw [hl]; exact ht.positive), hl]
          have := ht.positive
          simp only [ne_eq, Option.some.injEq]; omega
        · exact h.outNotZero
      have hwm : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
          Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m) (.ref x) ≠ 0 := by
        intro x hx
        have hpos := ht.refs_positive x hx
        have hg := widthMap_internal h.wiresNodup hpos
        simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
          ← Std.HashMap.get?_eq_getElem?, hg, Option.getD_some]
        omega
      simp only [dzStmt]
      rw [dzExpr_typed ht _ hwm]
  have hw : weOf (dropZeroWidthModule m) = weOf m := by
    unfold dropZeroWidthModule
    split
    · rfl
    · exact weOf_dropWires m h.wiresNodup
  have hi : (dropZeroWidthModule m).inputs = m.inputs := by unfold dropZeroWidthModule; split <;> rfl
  have ho : (dropZeroWidthModule m).outputs = m.outputs := by unfold dropZeroWidthModule; split <;> rfl
  exact ⟨hb, hw, hi, ho, by rw [hw, hb]; exact h.typed⟩

/-- Both actual post-processing choices preserve values and the per-assignment
width invariant. The source entry must still establish `TypedPostReady`. -/
theorem typed_postprocess_sound {m m' : Sparkle.IR.AST.Module}
    (h : TypedPostReady m)
    (hm : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m))
    (mems : MEnv) (initial result : Env)
    (heval : evalAssigns (weOf m) mems m.body initial = some result) :
    evalAssigns (weOf m') mems m'.body initial = some result ∧
    TypedStmts (weOf m') m'.body ∧ m'.inputs = m.inputs ∧ m'.outputs = m.outputs := by
  obtain ⟨hb, hw, hi, ho, ht⟩ := dropZeroWidth_typed h
  have hev : evalAssigns (weOf (dropZeroWidthModule m)) mems
      (dropZeroWidthModule m).body initial = some result := by rw [hw, hb]; exact heval
  rcases hm with rfl | rfl
  · exact ⟨hev, ht, hi, ho⟩
  · obtain ⟨hev', _, hi', ho'⟩ := mergeDuplicates_sound _ mems initial result ht.isAssign hev
    exact ⟨hev', mergeDuplicates_typed (by rw [hw]; exact h.outWidthZero) ht,
      hi'.trans hi, ho'.trans ho⟩

end Tools.ShippingTypedPostSoundness
