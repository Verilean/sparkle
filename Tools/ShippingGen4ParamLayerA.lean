import Sparkle.IR.Type
set_option autoImplicit false
-- NOT BUILT (clean issue-linked): new file. Pod build only: kjob lake build Tools.ShippingGen4ParamLayerA exit 0, 226 jobs (not clean issue-linked).

/-! # M4 parametric, Layer A: pure model of the DimExpr success condition (scripts/gen4/PARAMETRIC_LAYERA_FREEZE.md rev2)

`evalM` is a TOTAL MODEL copied from the text of `Sparkle.IR.Type.DimExpr.evaluate`; it is not `evaluate`
(which is `partial`), not `specializeType`/`specializeDesign`. Nothing here is a production I5b supply, discharges T,
or adds a law / TRUSTED boundary. -/

namespace Tools.ShippingGen4ParamLayerA
open Sparkle.IR.Type

abbrev Binding := List (String × Nat)

def clog2M (v : Nat) : Nat := if v == 1 then 0 else Nat.log2 (v - 1) + 1

def evalM (θ : Binding) : DimExpr → Except String Nat
  | .literal v => .ok v
  | .parameter n => match θ.lookup n with
      | some v => .ok v
      | none => .error s!"missing specialization binding for parameter '{n}'"
  | .add a b => do let x ← evalM θ a; let y ← evalM θ b; pure (x + y)
  | .sub a b => do let x ← evalM θ a; let y ← evalM θ b
                   if x < y then throw s!"hardware dimension subtraction underflow: {x} - {y}" else pure (x - y)
  | .mul a b => do let x ← evalM θ a; let y ← evalM θ b; pure (x * y)
  | .div a b => do let x ← evalM θ a; let y ← evalM θ b
                   if y == 0 then throw "hardware dimension division by zero" else pure (x / y)
  | .mod a b => do let x ← evalM θ a; let y ← evalM θ b
                   if y == 0 then throw "hardware dimension modulo by zero" else pure (x % y)
  | .pow a b => do let x ← evalM θ a; let y ← evalM θ b; pure (x ^ y)
  | .clog2 a => do let x ← evalM θ a
                   if x == 0 then throw "clog2 is undefined for hardware dimension 0" else pure (clog2M x)
  | .min a b => do let x ← evalM θ a; let y ← evalM θ b; pure (Nat.min x y)
  | .max a b => do let x ← evalM θ a; let y ← evalM θ b; pure (Nat.max x y)

def Bound (θ : Binding) : DimExpr → Prop
  | .literal _ => True
  | .parameter n => ∃ v, θ.lookup n = some v
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .pow a b | .min a b | .max a b => Bound θ a ∧ Bound θ b
  | .clog2 a => Bound θ a

def AllPos (θ : Binding) : Prop := ∀ p ∈ θ, 0 < p.2

def PosDim : DimExpr → Prop
  | .literal c => 0 < c
  | .parameter _ => True
  | .add a b | .mul a b | .pow a b | .min a b | .max a b => PosDim a ∧ PosDim b
  | .sub .. | .div .. | .mod .. | .clog2 _ => False

def NonNegDim (e : DimExpr) : Prop := e = .literal 0 ∨ PosDim e

def SliceOK (hi lo : DimExpr) : Prop :=
  ∃ s l, lo = s ∧ hi = DimExpr.mkSub (DimExpr.mkAdd s l) (.literal 1) ∧ NonNegDim s ∧ PosDim l

/-! ## helper lemmas (not in the freeze's theorem list) -/

attribute [local simp] Except.bind Except.pure Except.map Functor.map Bind.bind Pure.pure

theorem lookup_mem (θ : Binding) (n : String) (v : Nat) (h : θ.lookup n = some v) : (n, v) ∈ θ := by
  induction θ with
  | nil => simp [List.lookup] at h
  | cons p t ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      simp at h
      have : n = k := by simpa using hk
      subst this; subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem Bound_mkAdd {θ : Binding} {a b : DimExpr} (h : Bound θ (DimExpr.mkAdd a b)) : Bound θ a ∧ Bound θ b := by
  unfold DimExpr.mkAdd at h
  split at h <;> simp_all [Bound]

theorem Bound_mkSub {θ : Binding} {a b : DimExpr} (h : Bound θ (DimExpr.mkSub a b)) : Bound θ a ∧ Bound θ b := by
  unfold DimExpr.mkSub at h
  split at h <;> simp_all [Bound]

/-! ## frozen theorems -/

theorem evalM_mkAdd (θ : Binding) (a b : DimExpr) :
    evalM θ (DimExpr.mkAdd a b) = evalM θ (.add a b) := by
  unfold DimExpr.mkAdd
  split
  · cases h : evalM θ b <;> simp [evalM, h]
  · cases h : evalM θ a <;> simp [evalM, h]
  · simp [evalM]
  · rfl

theorem evalM_mkSub_of_le {θ : Binding} {a b : DimExpr} {x y : Nat}
    (ha : evalM θ a = .ok x) (hb : evalM θ b = .ok y) (h : y ≤ x) :
    evalM θ (DimExpr.mkSub a b) = .ok (x - y) := by
  unfold DimExpr.mkSub
  split
  · simp [evalM] at hb; subst hb; simpa using ha
  · rename_i l r
    simp [evalM] at ha hb; subst ha; subst hb; simp [evalM]
  · simp [evalM, ha, hb, Nat.not_lt.2 h]

theorem evalM_pos {θ : Binding} {e : DimExpr} (hp : PosDim e) (hb : Bound θ e) (ha : AllPos θ) :
    ∃ v, evalM θ e = .ok v ∧ 0 < v := by
  induction e with
  | literal c => exact ⟨c, rfl, hp⟩
  | parameter n =>
    obtain ⟨v, hv⟩ := hb
    exact ⟨v, by simp [evalM, hv], ha _ (lookup_mem θ n v hv)⟩
  | add a b iha ihb =>
    obtain ⟨x, hx, px⟩ := iha hp.1 hb.1
    obtain ⟨y, hy, py⟩ := ihb hp.2 hb.2
    exact ⟨x + y, by simp [evalM, hx, hy], by omega⟩
  | mul a b iha ihb =>
    obtain ⟨x, hx, px⟩ := iha hp.1 hb.1
    obtain ⟨y, hy, py⟩ := ihb hp.2 hb.2
    exact ⟨x * y, by simp [evalM, hx, hy], Nat.mul_pos px py⟩
  | pow a b iha ihb =>
    obtain ⟨x, hx, px⟩ := iha hp.1 hb.1
    obtain ⟨y, hy, py⟩ := ihb hp.2 hb.2
    exact ⟨x ^ y, by simp [evalM, hx, hy], Nat.pow_pos px⟩
  | min a b iha ihb =>
    obtain ⟨x, hx, px⟩ := iha hp.1 hb.1
    obtain ⟨y, hy, py⟩ := ihb hp.2 hb.2
    exact ⟨Nat.min x y, by simp [evalM, hx, hy], by simp only [Nat.min_def]; split <;> assumption⟩
  | max a b iha ihb =>
    obtain ⟨x, hx, px⟩ := iha hp.1 hb.1
    obtain ⟨y, hy, py⟩ := ihb hp.2 hb.2
    exact ⟨Nat.max x y, by simp [evalM, hx, hy], by simp only [Nat.max_def]; split <;> assumption⟩
  | sub a b _ _ => exact absurd hp (by simp [PosDim])
  | div a b _ _ => exact absurd hp (by simp [PosDim])
  | mod a b _ _ => exact absurd hp (by simp [PosDim])
  | clog2 a _ => exact absurd hp (by simp [PosDim])

theorem evalM_nonneg {θ : Binding} {e : DimExpr} (hp : NonNegDim e) (hb : Bound θ e) (ha : AllPos θ) :
    ∃ v, evalM θ e = .ok v := by
  rcases hp with h | h
  · subst h; exact ⟨0, rfl⟩
  · obtain ⟨v, hv, _⟩ := evalM_pos h hb ha
    exact ⟨v, hv⟩

theorem sliceOK_order {θ : Binding} {hi lo : DimExpr} (h : SliceOK hi lo)
    (hb : Bound θ hi ∧ Bound θ lo) (ha : AllPos θ) :
    ∃ h' l', evalM θ hi = .ok h' ∧ evalM θ lo = .ok l' ∧ l' ≤ h' := by
  obtain ⟨s, l, hlo, hhi, hs, hl⟩ := h
  subst hlo; subst hhi
  have hb1 := (Bound_mkSub hb.1).1
  have hbs := (Bound_mkAdd hb1).1
  have hbl := (Bound_mkAdd hb1).2
  obtain ⟨xs, hxs⟩ := evalM_nonneg hs hbs ha
  obtain ⟨xl, hxl, pl⟩ := evalM_pos hl hbl ha
  have hadd : evalM θ (DimExpr.mkAdd lo l) = .ok (xs + xl) := by
    rw [evalM_mkAdd]; simp [evalM, hxs, hxl]
  have hsub := evalM_mkSub_of_le (b := .literal 1) hadd rfl (by omega)
  exact ⟨xs + xl - 1, xs, hsub, hxs, by omega⟩

theorem evalM_sub_one_at_one :
    evalM [("n", 1)] (.sub (.parameter "n") (.literal 1)) = .ok 0 := by
  simp [evalM]

end Tools.ShippingGen4ParamLayerA
