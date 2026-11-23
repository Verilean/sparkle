import Tools.VedU2HierMultiOut
import Tools.VedU2HierStmt

/-!
# `U2HStmtK`: the register-free hierarchical statement for children with k ≥ 1 outputs
(CANDIDATE, not reviewed as code; the statement text was approved to be added exactly so)

`U2HStmt` (Tools/VedU2HierStmt.lean) is unchanged.  `U2HStmtK` is `U2HStmt` with ONLY
`HierShapeS d m = true` replaced by `HierShapeK d m = true`; `regsOf m.body = []` and every other
conjunct is the same definition.  Coincidence with `U2HStmt` for single-output designs.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- CANDIDATE statement for a register-free parent whose children have one or more outputs:
`U2HStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`. -/
def U2HStmtK (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeK d m = true ∧
  regsOf m.body = [] ∧ WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

theorem U2HStmtK_of_U2HStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (h : U2HStmt c m d f) : U2HStmtK c m d f := by
  obtain ⟨a, b, c', d', e, f', g, h, i, j⟩ := h
  exact ⟨a, b, c', HierShapeK_of_S d', e, f', g, h, i, j⟩

/-- COINCIDENCE: when every module of the design has exactly one output, `U2HStmtK` is `U2HStmt`. -/
theorem U2HStmtK_iff (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (h1 : ∀ x ∈ d.modules, x.outputs.length = 1) : U2HStmtK c m d f ↔ U2HStmt c m d f := by
  unfold U2HStmtK U2HStmt
  constructor
  · rintro ⟨a, b, c', d', e, f', g, h, i, j⟩
    exact ⟨a, b, c', HierShapeS_of_K h1 d', e, f', g, h, i, j⟩
  · rintro ⟨a, b, c', d', e, f', g, h, i, j⟩
    exact ⟨a, b, c', HierShapeK_of_S d', e, f', g, h, i, j⟩

end Tools.VedU2Hier
