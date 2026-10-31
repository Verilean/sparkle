import Tools.ShippingGen4ParamLayerA
import Sparkle.Compiler.Elab
set_option autoImplicit false
-- BUILT: clean issue-linked build par12v-2f421f4f (Tests.Gen4.ParamBridgeShapeCheck, kjob lake incremental) exit 0, 228 jobs, approved at 2f421f4f. Comment-only update.

/-! # M4 parametric, bridge shape C1-C3 (scripts/gen4/PARAMETRIC_BRIDGE_FREEZE.md §4)

Closes rows B5, B6, B8 of the bridge survey from public total definitions. C1 is a structural case split of
`makeSliceExpr`; it does not use the meaning of `SliceOK` (the hypothesis is carried only because the frozen type has it).
After B1 (`DimExpr.evaluate = evalM`, unsupplied) a link to `specializeType` / `specializeExpr` unfolding (B2, B3) still remains.
Nothing here is a production I5b supply, discharges T, changes FG, or adds a law / TRUSTED boundary. -/

namespace Tools.ShippingGen4ParamBridgeShape
open Sparkle.IR.Type Sparkle.IR.AST Tools.ShippingGen4ParamLayerA

-- C1 (B5)
theorem makeSliceExpr_sliceOK {src : Expr} {hi lo : DimExpr} (h : SliceOK hi lo) :
    Sparkle.Compiler.Elab.makeSliceExpr src hi lo = Expr.sliceDim src hi lo ∨
    ∃ a b, hi = DimExpr.literal a ∧ lo = DimExpr.literal b ∧
      Sparkle.Compiler.Elab.makeSliceExpr src hi lo = Expr.slice src a b := by
  clear h
  unfold Sparkle.Compiler.Elab.makeSliceExpr
  cases hi <;> cases lo <;> first
    | (right; exact ⟨_, _, rfl, rfl, rfl⟩)
    | (left; rfl)

theorem makeSliceFromStartLength_eq (src : Expr) (s l : DimExpr) :
    Sparkle.Compiler.Elab.makeSliceFromStartLength src s l =
      Sparkle.Compiler.Elab.makeSliceExpr src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s := rfl

-- C2 (B6)
theorem hwTypeFromDim_literal (v : Nat) : hwTypeFromDim (DimExpr.literal v) = hwTypeFromWidth v := rfl

theorem hwTypeFromDim_nonliteral {d : DimExpr} (h : ∀ v, d ≠ DimExpr.literal v) :
    hwTypeFromDim d = HWType.bitVectorDim d := by
  cases d with
  | literal v => exact absurd rfl (h v)
  | _ => rfl

attribute [local simp] Except.bind Except.pure Except.map Functor.map Bind.bind Pure.pure

-- C3 (B8)
theorem evalM_mkMul {θ : Binding} {a b : DimExpr} {x y : Nat}
    (ha : evalM θ a = .ok x) (hb : evalM θ b = .ok y) : evalM θ (DimExpr.mkMul a b) = .ok (x * y) := by
  unfold DimExpr.mkMul
  split
  · simp [evalM] at ha; subst ha; simp [evalM]
  · simp [evalM] at hb; subst hb; simp [evalM]
  · simp [evalM] at ha; subst ha; simpa using hb
  · simp [evalM] at hb; subst hb; simpa using ha
  · simp [evalM] at ha hb; subst ha; subst hb; simp [evalM]
  · simp [evalM, ha, hb]

end Tools.ShippingGen4ParamBridgeShape
