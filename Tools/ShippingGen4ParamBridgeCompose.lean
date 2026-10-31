import Tools.ShippingGen4ParamBridgeShape
set_option autoImplicit false
-- NOT BUILT: no clean issue-linked build yet (coder runs it). Lean implementation of scripts/gen4/PARAMETRIC_BRIDGE_UNIT2_FREEZE.md §2.

/-! # M4 parametric, bridge unit 2 (D1 = B3', model side) (scripts/gen4/PARAMETRIC_BRIDGE_UNIT2_FREEZE.md §2)

Composes the C1 case split with `SliceOK` / `sliceOK_order` for the node `makeSliceFromStartLength` emits. Model level
only (`evalM`, not `DimExpr.evaluate`); the `.slice` disjunct says the frozen literal bounds are ordered in the model,
not that `specializeExpr` checks anything. B1-B4, T, FG remain unsupplied; no production edit, no new law / TRUSTED boundary.
The two helpers are the forward direction (components bound => combination bound), the reverse of
`Bound_mkAdd` / `Bound_mkSub` in Layer A. -/

namespace Tools.ShippingGen4ParamBridgeCompose
open Sparkle.IR.Type Sparkle.IR.AST Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape

theorem Bound_of_mkAdd {θ : Binding} {a b : DimExpr} (ha : Bound θ a) (hb : Bound θ b) :
    Bound θ (DimExpr.mkAdd a b) := by
  unfold DimExpr.mkAdd
  split <;> simp_all [Bound]

theorem Bound_of_mkSub {θ : Binding} {a b : DimExpr} (ha : Bound θ a) (hb : Bound θ b) :
    Bound θ (DimExpr.mkSub a b) := by
  unfold DimExpr.mkSub
  split <;> simp_all [Bound]

theorem startLength_node_ordered {θ : Binding} {src : Expr} {s l : DimExpr}
    (hs : NonNegDim s) (hl : PosDim l) (hb : Bound θ s ∧ Bound θ l) (ha : AllPos θ) :
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l =
        Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧
      ∃ h' l', evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = .ok h' ∧
        evalM θ s = .ok l' ∧ l' ≤ h') ∨
    (∃ a b, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Expr.slice src a b ∧
        evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = .ok a ∧
        evalM θ s = .ok b ∧ b ≤ a) := by
  have hok : SliceOK (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s := ⟨s, l, rfl, rfl, hs, hl⟩
  have hbd : Bound θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) :=
    Bound_of_mkSub (Bound_of_mkAdd hb.1 hb.2) (by simp [Bound])
  obtain ⟨h', l', he1, he2, hle⟩ := sliceOK_order hok ⟨hbd, hb.1⟩ ha
  rw [makeSliceFromStartLength_eq]
  rcases makeSliceExpr_sliceOK (src := src) hok with h | ⟨a, b, hia, hib, h⟩
  · exact Or.inl ⟨h, h', l', he1, he2, hle⟩
  · refine Or.inr ⟨a, b, h, ?_, ?_, ?_⟩
    · rw [hia] at he1 ⊢
      have : a = h' := by simpa [evalM] using he1
      simp [evalM, this]
    · rw [hib] at he2 ⊢
      have : b = l' := by simpa [evalM] using he2
      simp [evalM, this]
    · rw [hia] at he1; rw [hib] at he2
      have h1 : a = h' := by simpa [evalM] using he1
      have h2 : b = l' := by simpa [evalM] using he2
      omega

end Tools.ShippingGen4ParamBridgeCompose
