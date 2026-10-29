import Sparkle.IR.ZeroWidth
import Tools.ShippingMergeKeepsBridge
set_option autoImplicit false
-- NOT BUILT (written without a build; G-POST step 7 of scripts/gen2/KEEPCHILD_POST_FREEZE.md §A).
-- SCOPE: PURE statement-list facts, independent of Tools.ShippingGen2Defs: an instance statement whose
-- TARGET module is `n` survives the two post-passes of the full entry (`dropZeroWidthModule`,
-- `mergeChecked`). Only the target occurrence is kept: the instance name is kept too, the
-- connections are rewritten (not whole-statement identity).
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingGen2InstKeep
open Sparkle.IR.AST

/-! ## Zero-width elimination -/

/-- `dzStmt` keeps an instance's module and instance names (ZeroWidth.lean `dzStmt`, `.inst` arm). -/
theorem dzStmt_inst (wm : Sparkle.IR.Optimize.WidthMap) (n i : String) (cs : List (String × Expr)) :
    Sparkle.IR.ZeroWidth.dzStmt wm (Stmt.inst n i cs) =
      some (Stmt.inst n i (cs.map fun p => (p.1, Sparkle.IR.ZeroWidth.dzExpr wm p.2))) := rfl

theorem inst_target_dropZW {n : String} {m : Module}
    (h : ∃ i cs, Stmt.inst n i cs ∈ m.body) :
    ∃ i cs, Stmt.inst n i cs ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body := by
  obtain ⟨i, cs, hm⟩ := h
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · exact ⟨i, cs, hm⟩
  · exact ⟨i, cs.map fun p => (p.1, Sparkle.IR.ZeroWidth.dzExpr (Sparkle.IR.Optimize.buildWidthMap m) p.2),
      List.mem_filterMap.mpr ⟨Stmt.inst n i cs, hm, dzStmt_inst _ n i cs⟩⟩

/-! ## The checked merge -/

/-- `rewriteStmt` keeps an instance's module and instance names: `definedNode (inst …) = none`,
so the statement goes through `mapStmtExprs`, which only renames the connections. -/
theorem rewriteStmt_inst (s : Std.HashMap String String) (n i : String) (cs : List (String × Expr)) :
    Tools.ShippingMergeKeeps.rewriteStmt s (Stmt.inst n i cs) =
      Sparkle.IR.Optimize.mapStmtExprs (Sparkle.IR.Optimize.renameRefs s) (Stmt.inst n i cs) := rfl

theorem inst_target_rewrite (s : Std.HashMap String String) {body : List Stmt} {n i : String}
    {cs : List (String × Expr)} (h : Stmt.inst n i cs ∈ body) :
    ∃ i' cs', Stmt.inst n i' cs' ∈ body.map (Tools.ShippingMergeKeeps.rewriteStmt s) := by
  first
    | exact ⟨i, _, List.mem_map.mpr ⟨Stmt.inst n i cs, h, (rewriteStmt_inst s n i cs).trans rfl⟩⟩
    | exact ⟨i, _, List.mem_map.mpr ⟨Stmt.inst n i cs, h,
        by rw [rewriteStmt_inst]; simp only [Sparkle.IR.Optimize.mapStmtExprs]⟩⟩

/-- copy of `Tools.ShippingSrm17Body.parts_shape` (ShippingSrm17Body.lean:221), kept here so this
file does not import the SRM17 chain. -/
theorem parts_shape (m : Module) :
    (Sparkle.IR.RegDedup.mergeDuplicatesParts m).1 = m.body ∨
    ∃ s, (Sparkle.IR.RegDedup.mergeDuplicatesParts m).1 =
      m.body.map (Tools.ShippingMergeKeeps.rewriteStmt s) := by
  rw [Tools.ShippingMergeKeeps.parts_eq_model, Tools.ShippingMergeKeeps.model_eq_rec]
  unfold Tools.ShippingMergeKeeps.partsRec
  split
  · left; rfl
  · unfold Tools.ShippingMergeKeeps.afterClasses
    split
    · left; rfl
    · unfold Tools.ShippingMergeKeeps.finish
      split
      · left; rfl
      · right; exact ⟨_, rfl⟩

/-- copy of `Tools.ShippingSrm17Body.mergeDuplicates_body` (ShippingSrm17Body.lean:210). -/
theorem mergeDuplicates_body (X : Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates X).body = X.body ∨
    (Sparkle.IR.RegDedup.mergeDuplicates X).body = (Sparkle.IR.RegDedup.mergeDuplicatesParts X).1 := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates Sparkle.IR.RegDedup.mergeDuplicatesRaw
  dsimp only
  split
  · split
    · right; rfl
    · left; rfl
  · right; rfl

theorem inst_target_mergeDuplicates {n : String} {m : Module}
    (h : ∃ i cs, Stmt.inst n i cs ∈ m.body) :
    ∃ i cs, Stmt.inst n i cs ∈ (Sparkle.IR.RegDedup.mergeDuplicates m).body := by
  have hparts : ∃ i cs, Stmt.inst n i cs ∈ (Sparkle.IR.RegDedup.mergeDuplicatesParts m).1 := by
    rcases parts_shape m with e | ⟨s, e⟩
    · rw [e]; exact h
    · rw [e]
      obtain ⟨i, cs, hm⟩ := h
      exact inst_target_rewrite s hm
  rcases mergeDuplicates_body m with e | e
  · rw [e]; exact h
  · rw [e]; exact hparts

theorem inst_target_mergeChecked {n : String} {m : Module}
    (h : ∃ i cs, Stmt.inst n i cs ∈ m.body) :
    ∃ i cs, Stmt.inst n i cs ∈ (Sparkle.IR.RefineCheck.mergeChecked m).body := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases m with e | e
  · rw [e]; exact inst_target_mergeDuplicates h
  · rw [e]; exact h

/-- both post-passes, in the full entry's order (Sparkle/Compiler/Elab.lean:5600-5606:
`mergeChecked (dropZeroWidthModule m)`, or `dropZeroWidthModule m` under `SPARKLE_NO_REGDEDUP`). -/
theorem inst_target_post {n : String} {m : Module}
    (h : ∃ i cs, Stmt.inst n i cs ∈ m.body) :
    ∃ i cs, Stmt.inst n i cs ∈
      (Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)).body :=
  inst_target_mergeChecked (inst_target_dropZW h)

/-- the full entry's module, in the disjunctive form `StepStmt`/`fullEntry_name` use
(Tools/ShippingDesignWriterRun.lean:79-80): an instance target of the core module is an instance
target of the full entry's module. -/
theorem inst_target_full {n : String} {raw b : Module}
    (hb : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (h : ∃ i cs, Stmt.inst n i cs ∈ raw.body) :
    ∃ i cs, Stmt.inst n i cs ∈ b.body := by
  rcases hb with rfl | rfl
  · exact inst_target_dropZW h
  · exact inst_target_post h

end Tools.ShippingGen2InstKeep
