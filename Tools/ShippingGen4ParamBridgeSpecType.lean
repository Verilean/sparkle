import Tools.ShippingGen4ParamBridgeWidth
set_option autoImplicit false
-- BUILT: clean issue-linked build parv19-10e7df1e (Tests.Gen4.ParamBridgeSpecTypeCheck, kjob lake incremental) exit 0, 230 jobs, approved at 10e7df1e. Comment-only update. Implementation of scripts/gen4/PARAMETRIC_BRIDGE_UNIT4_FREEZE.md §2 (F1, approved freeze 4013f4b2).

/-! # M4 parametric, bridge unit 4 (F1: model-level lift of E1 to whole types) (scripts/gen4/PARAMETRIC_BRIDGE_UNIT4_FREEZE.md §2)

`specTypeM` is a total model copied from the text of `specializeType` (Specialize.lean:56-65) and `requirePositiveM`
from `requirePositive` (:42-44). It is NOT claimed equal to `specializeType` (that is B2, unsupplied). Nothing here is a
production I5b supply, discharges T, changes FG, or adds a law / TRUSTED boundary. B1-B4, T, FG remain unsupplied. -/

namespace Tools.ShippingGen4ParamBridgeSpecType
open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape Tools.ShippingGen4ParamBridgeWidth

def requirePositiveM (context : String) (value : Nat) : Except String Nat :=
  if value == 0 then .error s!"{context} specializes to zero width" else .ok value

def specTypeM (θ : Binding) (context : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector width => .ok (.bitVector width)
  | .bitVectorDim dimension =>
      (evalM θ dimension).bind fun width =>
        (requirePositiveM context width).bind fun w => .ok (hwTypeFromWidth w)
  | .array size elementType =>
      (specTypeM θ s!"{context} element" elementType).bind fun e => .ok (.array size e)

def TyPos : HWType → Prop
  | .bit => True
  | .bitVector _ => True
  | .bitVectorDim d => PosDim d
  | .array _ e => TyPos e

def TyBound (θ : Binding) : HWType → Prop
  | .bit => True
  | .bitVector _ => True
  | .bitVectorDim d => Bound θ d
  | .array _ e => TyBound θ e

theorem requirePositiveM_pos (context : String) {w : Nat} (h : 0 < w) :
    requirePositiveM context w = .ok w := by
  have : (w == 0) = false := by simp; omega
  simp [requirePositiveM, this]

-- F1a
theorem specTypeM_ok {θ : Binding} {t : HWType} (context : String)
    (hp : TyPos t) (hb : TyBound θ t) (ha : AllPos θ) :
    ∃ t', specTypeM θ context t = .ok t' := by
  induction t generalizing context with
  | bit => exact ⟨_, rfl⟩
  | bitVector w => exact ⟨_, rfl⟩
  | bitVectorDim d =>
      obtain ⟨w, hw, hpos⟩ := evalM_pos (show PosDim d from hp) (show Bound θ d from hb) ha
      refine ⟨hwTypeFromWidth w, ?_⟩
      simp [specTypeM, hw, requirePositiveM_pos context hpos, Except.bind]
  | array n e ih =>
      obtain ⟨e', he⟩ := ih (context := s!"{context} element") (show TyPos e from hp) (show TyBound θ e from hb)
      exact ⟨.array n e', by simp [specTypeM, he, Except.bind]⟩

-- F1b
theorem specTypeM_hwTypeFromDim {θ : Binding} {d : DimExpr} (context : String)
    (hp : PosDim d) (hb : Bound θ d) (ha : AllPos θ) :
    ∃ w, evalM θ d = .ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = .ok (hwTypeFromWidth w) := by
  rcases hwTypeFromDim_width_ok hp hb ha with ⟨v, _, hv, hev, hty⟩ | ⟨hn, hty, w, hw, hpos⟩
  · refine ⟨v, hev, hv, ?_⟩
    rw [hty]
    unfold hwTypeFromWidth
    by_cases h1 : (v == 1) = true
    · simp [h1, specTypeM]
    · simp [h1, specTypeM]
  · refine ⟨w, hw, hpos, ?_⟩
    rw [hty]
    simp [specTypeM, hw, requirePositiveM_pos context hpos, Except.bind]

end Tools.ShippingGen4ParamBridgeSpecType
