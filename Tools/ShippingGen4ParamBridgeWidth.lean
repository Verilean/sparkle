import Tools.ShippingGen4ParamBridgeShape
set_option autoImplicit false
-- BUILT: clean issue-linked build parv-d7892ef6 (Tests.Gen4.ParamBridgeWidthCheck, kjob lake incremental) exit 0, 229 jobs, approved at d7892ef6. Comment-only update. Implementation of scripts/gen4/PARAMETRIC_BRIDGE_UNIT3_FREEZE.md §2 (E1 = B2' model side).

/-! # M4 parametric, bridge unit 3 (E1 = B2', model side) (scripts/gen4/PARAMETRIC_BRIDGE_UNIT3_FREEZE.md §2)

Composes C2 (`hwTypeFromDim_literal` / `hwTypeFromDim_nonliteral`) with Layer A `evalM_pos`. Model level only
(`evalM`, not `DimExpr.evaluate`); positivity of `w` is the model analogue of the `requirePositive` test, not a
statement about `specializeType`. B1-B4, T, FG remain unsupplied; no production edit, no new law / TRUSTED boundary. -/

namespace Tools.ShippingGen4ParamBridgeWidth
open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape

theorem hwTypeFromDim_width_ok {θ : Binding} {d : DimExpr}
    (hp : PosDim d) (hb : Bound θ d) (ha : AllPos θ) :
    (∃ v, d = DimExpr.literal v ∧ 0 < v ∧ evalM θ d = .ok v ∧
        hwTypeFromDim d = hwTypeFromWidth v) ∨
    ((∀ v, d ≠ DimExpr.literal v) ∧ hwTypeFromDim d = HWType.bitVectorDim d ∧
        ∃ w, evalM θ d = .ok w ∧ 0 < w) := by
  by_cases h : ∃ v, d = DimExpr.literal v
  · obtain ⟨v, rfl⟩ := h
    refine Or.inl ⟨v, rfl, hp, rfl, hwTypeFromDim_literal v⟩
  · have h' : ∀ v, d ≠ DimExpr.literal v := fun v hv => h ⟨v, hv⟩
    exact Or.inr ⟨h', hwTypeFromDim_nonliteral h', evalM_pos hp hb ha⟩

end Tools.ShippingGen4ParamBridgeWidth
