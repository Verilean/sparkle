import Tools.ShippingTypedPostSoundness

/-! Checked optimization for flat comparison/mux modules. The normalizer is
unchanged: these modules retain their postprocessed original. Control-node
presence is preserved through the actual checked merge, so the fallback
premise can be established before postprocessing. -/
namespace Tools.ShippingControlOptSoundness
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck Sparkle.IR.RegDedup
open Sparkle.IR.ZeroWidth
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness
open Tools.ShippingTypedPostSoundness

def isControlExpr : Expr → Bool
  | .op .mux _ => true
  | .op op _ => isControlBinOp op
  | _ => false

def HasControl (body : List Stmt) : Prop :=
  ∃ l e, .assign l e ∈ body ∧ isControlExpr e = true

theorem control_rename (σ : String → String) (e : Expr) :
    isControlExpr (renameE σ e) = isControlExpr e := by
  cases e with
  | op op _ => cases op <;> rfl
  | _ => rfl

theorem normE_control_none {e : Expr} (hc : isControlExpr e = true)
    (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    normE we ins defs e = none := by
  cases e with
  | op op args =>
    cases op <;> simp_all [isControlExpr, isControlBinOp]
    all_goals
      cases args with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b tail => cases tail <;> simp [normE, isBinOp]
  | _ => simp [isControlExpr] at hc

theorem normBody_control_none {body : List Stmt} (hc : HasControl body)
    (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    normBody we ins defs body = none := by
  obtain ⟨l, e, hm, he⟩ := hc
  induction body generalizing defs with
  | nil => cases hm
  | cons st rest ih =>
    rcases List.mem_cons.mp hm with hst | htail
    · subst st; simp [normBody, normE_control_none he]
    · cases st with
      | assign l r =>
        simp only [normBody]
        cases hr : normE we ins defs r with
        | none => rfl
        | some e => exact ih _ htail
      | _ => rfl

theorem checkedOptimize_control {m : Sparkle.IR.AST.Module}
    (hg : simpleBody m = true) (hc : HasControl m.body) : checkedOptimize m = m := by
  have hn := normBody_control_none hc (declWidth m) (m.inputs.map (·.name)) []
  simp [checkedOptimize, hg, optCheck, optCheckCore, hn]

/-- Width-cast roots (the zero-extension concat and the size-cast slice):
shapes the normalizing optimizer rejects outright. -/
def isCastExpr : Expr → Bool
  | .concat _ => true
  | .slice .. => true
  | _ => false

def HasCast (body : List Stmt) : Prop :=
  ∃ l e, .assign l e ∈ body ∧ isCastExpr e = true

theorem normE_cast_none {e : Expr} (hc : isCastExpr e = true)
    (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    normE we ins defs e = none := by
  cases e <;> simp_all [isCastExpr, normE]

theorem normBody_cast_none {body : List Stmt} (hc : HasCast body)
    (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    normBody we ins defs body = none := by
  obtain ⟨l, e, hm, he⟩ := hc
  induction body generalizing defs with
  | nil => cases hm
  | cons st rest ih =>
    rcases List.mem_cons.mp hm with hst | htail
    · subst st; simp [normBody, normE_cast_none he]
    · cases st with
      | assign l r =>
        simp only [normBody]
        cases hr : normE we ins defs r with
        | none => rfl
        | some e => exact ih _ htail
      | _ => rfl

/-- Like control roots, cast roots keep the postprocessed module unchanged
through the checked optimizer. -/
theorem checkedOptimize_cast {m : Sparkle.IR.AST.Module}
    (hg : simpleBody m = true) (hc : HasCast m.body) : checkedOptimize m = m := by
  have hn := normBody_cast_none hc (declWidth m) (m.inputs.map (·.name)) []
  simp [checkedOptimize, hg, optCheck, optCheckCore, hn]

/-- The representative table contains no control-root expressions. -/
def NoControlDefs (defs : List (String × Expr)) : Prop :=
  ∀ x e, defs.lookup x = some e → isControlExpr e = false

theorem NoControlDefs.cons {defs} (h : NoControlDefs defs) (x : String) (e : Expr)
    (he : isControlExpr e = false) : NoControlDefs ((x, e) :: defs) := by
  intro y r hr
  by_cases hy : y == x
  · simp [List.lookup_cons, hy] at hr
    subst r; exact he
  · simp [List.lookup_cons, hy] at hr
    exact h y r hr

/-- A control-free proposed statement cannot hide the first control operation
behind an alias: an alias must name an earlier representative with the same
canonical RHS. -/
theorem validateStep_noControl {we allLhs st st' l e l' e'}
    (h : validateStep we allLhs st (.assign l e) (.assign l' e') = some st')
    (hn : isControlExpr e' = false) (hd : NoControlDefs st.R) :
    isControlExpr e = false ∧ NoControlDefs st'.R := by
  simp only [validateStep] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i he
        have hroot : isControlExpr e = false := by rw [he, control_rename] at hn; exact hn
        cases h
        exact ⟨hroot, hd.cons _ _ (by rw [control_rename]; exact hroot)⟩
      · cases e' with
        | ref y =>
          simp only at h
          split at h
          · rename_i hc
            obtain ⟨_, _, _, hr, _⟩ := hc
            have hroot := hd y _ hr
            rw [control_rename] at hroot
            cases h
            exact ⟨hroot, hd⟩
          · cases h
        | _ => simp at h

theorem validateMerge_go_noControl {we allLhs} :
    ∀ old new st, validateMerge.go we allLhs st old new = true →
      SimpleStmts old → NoControlDefs st.R →
      (∀ l e, .assign l e ∈ new → isControlExpr e = false) →
      ∀ l e, .assign l e ∈ old → isControlExpr e = false
  | [], [], _, _, _, _, _, _, _, h => by cases h
  | [], _ :: _, _, h, _, _, _, _, _, _ => by simp [validateMerge.go] at h
  | _ :: _, [], _, h, _, _, _, _, _, _ => by simp [validateMerge.go] at h
  | a :: as, b :: bs, st, h, hs, hd, hn, l, e, hm => by
    obtain ⟨la, ea, rfl, _⟩ := hs a List.mem_cons_self
    simp only [validateMerge.go] at h
    split at h
    · rename_i st' hstep
      obtain ⟨eb, rfl, _⟩ := validateStep_shape hstep
      obtain ⟨ha, hd'⟩ := validateStep_noControl hstep (hn la eb (by simp)) hd
      rcases List.mem_cons.mp hm with heq | hm
      · cases heq; exact ha
      · exact validateMerge_go_noControl as bs st' h
          (fun s hm => hs s (List.mem_cons_of_mem _ hm)) hd'
          (fun l e hm => hn l e (List.mem_cons_of_mem _ hm)) l e hm
    · cases h

theorem validateMerge_hasControl {we old new}
    (hv : validateMerge we old new = true) (hs : SimpleStmts old) (hc : HasControl old) :
    HasControl new := by
  apply Classical.byContradiction
  intro hn
  have hn' : ∀ l e, .assign l e ∈ new → isControlExpr e = false := by
    intro l e he
    cases hh : isControlExpr e with
    | false => rfl
    | true => exact (hn ⟨l, e, he, hh⟩).elim
  have ho := validateMerge_go_noControl old new {} hv hs
    (by intro x e h; cases h) hn'
  obtain ⟨l, e, hm, he⟩ := hc
  rw [ho l e hm] at he
  cases he

theorem mergeDuplicates_hasControl (m : Sparkle.IR.AST.Module)
    (hs : SimpleStmts m.body) (hc : HasControl m.body) : HasControl (mergeDuplicates m).body := by
  have hall : m.body.all isAssign = true := by
    rw [List.all_eq_true]
    intro s hm
    obtain ⟨l, e, rfl, _⟩ := hs s hm
    rfl
  unfold mergeDuplicates
  simp only [hall, if_true]
  split
  · rename_i hv; exact validateMerge_hasControl hv hs hc
  · exact hc

/-- Control-bearing typed modules retain the same environment and typed body
through cleanup, optional checked merging, AND shipping optimizer selection.
Only the original module's shape/presence is required, not a certificate for
the selected optimized module. The source entry must still derive readiness. -/
theorem typed_postprocess_checked_control {m m' : Sparkle.IR.AST.Module}
    (h : TypedPostReady m) (hs : SimpleStmts m.body) (hc : HasControl m.body)
    (hm : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m))
    (mems : MEnv) (initial result : Env)
    (he : evalAssigns (weOf m) mems m.body initial = some result) :
    checkedOptimize m' = m' ∧
    evalAssigns (weOf (checkedOptimize m')) mems (checkedOptimize m').body initial = some result ∧
    TypedStmts (weOf (checkedOptimize m')) (checkedOptimize m').body ∧
    (checkedOptimize m').inputs = m.inputs ∧ (checkedOptimize m').outputs = m.outputs := by
  have hb := (dropZeroWidth_typed h).1
  have hs' : SimpleStmts (dropZeroWidthModule m).body := by rw [hb]; exact hs
  have hc' : HasControl (dropZeroWidthModule m).body := by rw [hb]; exact hc
  have hkeep : checkedOptimize m' = m' := by
    rcases hm with rfl | rfl
    · exact checkedOptimize_control (simpleBody_of _ hs') hc'
    · exact checkedOptimize_control (simpleBody_of _ (mergeDuplicates_simple _ hs'))
        (mergeDuplicates_hasControl _ hs' hc')
  rw [hkeep]
  exact ⟨rfl, typed_postprocess_sound h hm mems initial result he⟩

end Tools.ShippingControlOptSoundness
