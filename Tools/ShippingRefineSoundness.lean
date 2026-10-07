import Sparkle.IR.RefineCheck
import Tools.ShippingSeqOptSoundness

/-! # `refineCheck` is sound

`Sparkle.IR.RefineCheck.refineCheck m o` accepts `o` as a refinement of an
assign + register module `m`. This file proves what acceptance means:

* `RShape`: the normal forms, their evaluation (`rShape_eval`), their width
  bound (`rShape_bound`) and their independence of everything but the names
  they read (`rShape_congr`);
* the smart constructors: `rSlice_sound` (a part-select through a
  concatenation, of a constant, of the whole expression), `rBin_sound` (the
  two `&` simplifications), `rMux_sound` (the Bool encoding);
* `rNormE_sound` / `rNormBody_sound`: a normal form has the value of the
  expression it normalises;
* `refineCheck_step_sound`: one cycle — both modules step, the outputs agree,
  every register update of `o` is the update of the same register of `m`;
* `refineCheck_run_sound` / `refineCheck_transfer`: any number of cycles
  under the canonical seeding, from states equal on the registers of `o`. -/

namespace Tools.ShippingRefineSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.IR.Reorder (refsOf)
open Tools.ShippingOptSoundness Tools.ShippingSeqOptSoundness

/-! ## Normal forms -/

/-- The normal forms of `rNormE`. -/
inductive RShape (we : WEnv) : Expr → Prop
  | const {v : Int} {w : Nat} : 0 ≤ v → v < ((2 ^ w : Nat) : Int) → RShape we (.const v w)
  | ref (x : String) : RShape we (.ref x)
  | bin {o : Operator} {a b : Expr} : rBinOk o = true → RShape we a → RShape we b →
      RShape we (.op o [a, b])
  | un {o : Operator} {a : Expr} : rUnOk o = true → RShape we a → RShape we (.op o [a])
  | mux {c a b : Expr} : RShape we c → RShape we a → RShape we b →
      widthOf we a = widthOf we b → RShape we (.op .mux [c, a, b])
  | concat {a b : Expr} : RShape we a → RShape we b → RShape we (.concat [a, b])
  | slice {e : Expr} {hi lo : Nat} : RShape we e → RShape we (.slice e hi lo)

theorem refs_un_mem {op : Operator} {a : Expr} {x : String} :
    x ∈ refsOf (.op op [a]) ↔ x ∈ refsOf a := by
  simp [refsOf, Sparkle.IR.Reorder.refsOf.refsList]

theorem refs_concat_mem {a b : Expr} {x : String} :
    x ∈ refsOf (.concat [a, b]) ↔ x ∈ refsOf a ∨ x ∈ refsOf b := by
  simp [refsOf, Sparkle.IR.Reorder.refsOf.refsList]

theorem refs_slice_mem {e : Expr} {hi lo : Nat} {x : String} :
    x ∈ refsOf (.slice e hi lo) ↔ x ∈ refsOf e := by
  simp [refsOf]

/-- The value of a two-part concatenation. -/
theorem eval_concat2 (we : WEnv) (env : Env) (a b : Expr) (va vb : Nat)
    (ha : evalExpr we env a = some va) (hb : evalExpr we env b = some vb) :
    evalExpr we env (.concat [a, b]) =
      some ((mask (widthOf we a) va) <<< (widthOf we b) ||| mask (widthOf we b) vb) := by
  simp [evalExpr, evalList, ha, hb, evalExpr.go]

/-- The value of a part-select. -/
theorem eval_slice (we : WEnv) (env : Env) {e : Expr} {v : Nat}
    (h : evalExpr we env e = some v) (hi lo : Nat) :
    evalExpr we env (.slice e hi lo) = some (mask (hi - lo + 1) (v >>> lo)) := by
  simp only [evalExpr, h, Option.bind_eq_bind, Option.bind_some]

theorem widthOf_concat2 (we : WEnv) (a b : Expr) :
    widthOf we (.concat [a, b]) = widthOf we a + widthOf we b := by
  simp [widthOf, widthOf.go]

theorem rShape_eval (we : WEnv) (env : Env) :
    ∀ {e : Expr}, RShape we e → ∃ v, evalExpr we env e = some v
  | _, .const h0 hlt => ⟨_, evalConst_fit we env h0 hlt⟩
  | _, .ref x => ⟨env x, rfl⟩
  | .op o [a, b], .bin ho ha hb => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some]
    cases o <;> simp_all [rBinOk, evalOp]
  | .op o [a], .un ho ha => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    simp only [evalExpr, evalList, hva, Option.bind_eq_bind, Option.bind_some]
    cases o <;> simp_all [rUnOk, evalOp]
  | .op .mux [c, a, b], .mux hc ha hb _ => by
    obtain ⟨vc, hvc⟩ := rShape_eval we env hc
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind, Option.bind_some]
    simp [evalOp]
  | .concat [a, b], .concat ha hb => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    exact ⟨_, eval_concat2 we env a b va vb hva hvb⟩
  | .slice e hi lo, .slice he => by
    obtain ⟨v, hv⟩ := rShape_eval we env he
    exact ⟨mask (hi - lo + 1) (v >>> lo),
      by simp only [evalExpr, hv, Option.bind_eq_bind, Option.bind_some]⟩

/-- A two-operand node's value fits its width, when the first operand's
does (a right shift only drops bits; everything else is masked or one
bit). -/
theorem rBin_lt (we : WEnv) {o : Operator} (ho : rBinOk o = true) (a b : Expr) (va vb r : Nat)
    (hva : va < 2 ^ widthOf we a)
    (hr : evalOp we o [a, b] [va, vb] (widthOf we (.op o [a, b])) = some r) :
    r < 2 ^ widthOf we (.op o [a, b]) := by
  cases o <;> simp only [rBinOk, Bool.false_eq_true] at ho <;>
    simp only [evalOp, Option.some.injEq, widthOf] at hr ⊢ <;> subst hr
  all_goals first
    | exact Nat.mod_lt _ (Nat.two_pow_pos _)
    | (split <;> decide)
    | exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hva

theorem shl_or_lt {x y a b : Nat} (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    x <<< b ||| y < 2 ^ (a + b) := by
  apply Nat.or_lt_two_pow
  · rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl _) (Nat.two_pow_pos b)
  · exact Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (Nat.le_add_left b a))

theorem rShape_bound (we : WEnv) (env : Env) :
    ∀ {e : Expr}, RShape we e → (∀ x ∈ refsOf e, env x < 2 ^ we x) →
      ∀ v, evalExpr we env e = some v → v < 2 ^ widthOf we e
  | _, .const h0 hlt, _, v, hv => by
    rw [evalConst_fit we env h0 hlt] at hv
    cases hv; simp only [widthOf]; omega
  | _, .ref x, hr, v, hv => by
    simp only [evalExpr, Option.some.injEq] at hv
    subst hv; exact hr x (by simp [refsOf])
  | .op o [a, b], .bin ho ha hb, hr, v, hv => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    have hba := rShape_bound we env ha
      (fun x hx => hr x (refs_bin_mem.mpr (Or.inl hx))) va hva
    simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some] at hv
    exact rBin_lt we ho a b va vb v hba hv
  | .op o [a], .un ho ha, _, v, hv => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    simp only [evalExpr, evalList, hva, Option.bind_eq_bind, Option.bind_some] at hv
    cases o <;> simp only [rUnOk, Bool.false_eq_true] at ho <;>
      simp only [evalOp, Option.some.injEq, widthOf] at hv ⊢ <;> subst hv <;>
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | .op .mux [c, a, b], .mux hc ha hb hw, hr, v, hv => by
    obtain ⟨vc, hvc⟩ := rShape_eval we env hc
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    have hba := rShape_bound we env ha
      (fun x hx => hr x (refs_mux_mem.mpr (Or.inr (Or.inl hx)))) va hva
    have hbb := rShape_bound we env hb
      (fun x hx => hr x (refs_mux_mem.mpr (Or.inr (Or.inr hx)))) vb hvb
    simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind, Option.bind_some,
      evalOp, Option.some.injEq] at hv
    subst hv
    have hwm : widthOf we (.op .mux [c, a, b]) = widthOf we a := by simp [widthOf]
    rw [hwm]
    by_cases h0 : vc ≠ 0
    · simp [h0, hba]
    · have h0' : vc = 0 := by omega
      simp [h0', hw, hbb]
  | .concat [a, b], .concat ha hb, _, v, hv => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    rw [eval_concat2 we env a b va vb hva hvb] at hv
    cases hv
    rw [widthOf_concat2]
    exact shl_or_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  | .slice e hi lo, .slice he, _, v, hv => by
    obtain ⟨ve, hve⟩ := rShape_eval we env he
    simp only [evalExpr, hve, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv
    subst hv
    simp only [widthOf]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## Normal forms depend only on the names they read -/

theorem evalOp2_congr {we we' : WEnv} (o : Operator) (a b : Expr) (va vb w : Nat)
    (ha : widthOf we' a = widthOf we a) (hb : widthOf we' b = widthOf we b) :
    evalOp we' o [a, b] [va, vb] w = evalOp we o [a, b] [va, vb] w := by
  cases o <;> simp [evalOp, ha, hb]

theorem widthOf_op2_congr {we we' : WEnv} (o : Operator) (a b : Expr)
    (ha : widthOf we' a = widthOf we a) (hb : widthOf we' b = widthOf we b) :
    widthOf we' (.op o [a, b]) = widthOf we (.op o [a, b]) := by
  cases o <;> simp [widthOf, ha, hb]

theorem evalOp1_congr {we we' : WEnv} (o : Operator) (a : Expr) (va w : Nat)
    (ha : widthOf we' a = widthOf we a) :
    evalOp we' o [a] [va] w = evalOp we o [a] [va] w := by
  cases o <;> simp [evalOp, ha]

theorem widthOf_op1_congr {we we' : WEnv} (o : Operator) (a : Expr)
    (ha : widthOf we' a = widthOf we a) :
    widthOf we' (.op o [a]) = widthOf we (.op o [a]) := by
  cases o <;> simp [widthOf, ha]

/-- A normal form under another width environment and another environment
that agree with the first on the names it reads: the same shape, width and
value. -/
theorem rShape_congr {we we' : WEnv} {env env' : Env} :
    ∀ {e : Expr}, RShape we e → (∀ x ∈ refsOf e, we' x = we x ∧ env' x = env x) →
      RShape we' e ∧ widthOf we' e = widthOf we e ∧ evalExpr we' env' e = evalExpr we env e
  | _, .const h0 hlt, _ =>
    ⟨.const h0 hlt, rfl, by rw [evalConst_fit we' env' h0 hlt, evalConst_fit we env h0 hlt]⟩
  | _, .ref x, h => by
    obtain ⟨hw, hv⟩ := h x (by simp [refsOf])
    exact ⟨.ref x, by simp [widthOf, hw], by simp [evalExpr, hv]⟩
  | .op o [a, b], .bin ho ha hb, h => by
    obtain ⟨sa, wa, ea⟩ := rShape_congr ha (fun x hx => h x (refs_bin_mem.mpr (Or.inl hx)))
    obtain ⟨sb, wb, eb⟩ := rShape_congr hb (fun x hx => h x (refs_bin_mem.mpr (Or.inr hx)))
    refine ⟨.bin ho sa sb, widthOf_op2_congr o a b wa wb, ?_⟩
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    simp only [evalExpr, evalList, ea, eb, hva, hvb, Option.bind_eq_bind, Option.bind_some,
      widthOf_op2_congr o a b wa wb]
    exact evalOp2_congr o a b va vb _ wa wb
  | .op o [a], .un ho ha, h => by
    obtain ⟨sa, wa, ea⟩ := rShape_congr ha (fun x hx => h x (refs_un_mem.mpr hx))
    refine ⟨.un ho sa, widthOf_op1_congr o a wa, ?_⟩
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    simp only [evalExpr, evalList, ea, hva, Option.bind_eq_bind, Option.bind_some,
      widthOf_op1_congr o a wa]
    exact evalOp1_congr o a va _ wa
  | .op .mux [c, a, b], .mux hc ha hb hw, h => by
    obtain ⟨sc, wc, ec⟩ := rShape_congr hc (fun x hx => h x (refs_mux_mem.mpr (Or.inl hx)))
    obtain ⟨sa, wa, ea⟩ :=
      rShape_congr ha (fun x hx => h x (refs_mux_mem.mpr (Or.inr (Or.inl hx))))
    obtain ⟨sb, wb, eb⟩ :=
      rShape_congr hb (fun x hx => h x (refs_mux_mem.mpr (Or.inr (Or.inr hx))))
    refine ⟨.mux sc sa sb (by rw [wa, wb, hw]), by simp [widthOf, wa], ?_⟩
    obtain ⟨vc, hvc⟩ := rShape_eval we env hc
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    simp only [evalExpr, evalList, ec, ea, eb, hvc, hva, hvb, Option.bind_eq_bind,
      Option.bind_some]
    simp [evalOp]
  | .concat [a, b], .concat ha hb, h => by
    obtain ⟨sa, wa, ea⟩ := rShape_congr ha (fun x hx => h x (refs_concat_mem.mpr (Or.inl hx)))
    obtain ⟨sb, wb, eb⟩ := rShape_congr hb (fun x hx => h x (refs_concat_mem.mpr (Or.inr hx)))
    refine ⟨.concat sa sb, by rw [widthOf_concat2, widthOf_concat2, wa, wb], ?_⟩
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    rw [eval_concat2 we' env' a b va vb (by rw [ea, hva]) (by rw [eb, hvb]),
      eval_concat2 we env a b va vb hva hvb, wa, wb]
  | .slice e hi lo, .slice he, h => by
    obtain ⟨se, _, ee⟩ := rShape_congr he (fun x hx => h x (refs_slice_mem.mpr hx))
    exact ⟨.slice se, by simp [widthOf], by simp only [evalExpr, ee]⟩

/-! ## Part-selects -/

theorem concat_val (va vb wb : Nat) (hvb : vb < 2 ^ wb) :
    va <<< wb ||| vb = va * 2 ^ wb + vb := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hvb, Nat.shiftLeft_eq]

/-- A part-select above the low part reads the high part. -/
theorem slice_hi (va vb wb lo k : Nat) (hvb : vb < 2 ^ wb) (hlo : wb ≤ lo) :
    mask k ((va * 2 ^ wb + vb) >>> lo) = mask k (va >>> (lo - wb)) := by
  obtain ⟨d, rfl⟩ : ∃ d, lo = wb + d := ⟨lo - wb, by omega⟩
  simp only [mask, Nat.shiftRight_eq_div_pow, Nat.add_sub_cancel_left]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_comm (va * 2 ^ wb),
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos wb), Nat.div_eq_of_lt hvb, Nat.zero_add]

/-- A part-select inside the low part reads the low part. -/
theorem slice_lo (va vb wb lo k : Nat) (h : lo + k ≤ wb) :
    mask k ((va * 2 ^ wb + vb) >>> lo) = mask k (vb >>> lo) := by
  obtain ⟨d, rfl⟩ : ∃ d, wb = lo + k + d := ⟨wb - (lo + k), by omega⟩
  simp only [mask, Nat.shiftRight_eq_div_pow]
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← Nat.pow_add]
  have hm : va * 2 ^ (lo + k + d) = 2 ^ (lo + k) * (va * 2 ^ d) := by
    rw [Nat.pow_add]; ac_rfl
  rw [hm, Nat.add_comm, Nat.add_mul_mod_self_left]

/-- The part-select of a normal form that is not taken apart. -/
theorem slice_generic (we : WEnv) (env : Env) {e : Expr} (hs : RShape we e)
    (hb : ∀ v, evalExpr we env e = some v → v < 2 ^ widthOf we e) (hi lo v : Nat)
    (hv : evalExpr we env e = some v) :
    RShape we (if lo = 0 ∧ hi + 1 = widthOf we e then e else .slice e hi lo) ∧
    widthOf we (if lo = 0 ∧ hi + 1 = widthOf we e then e else .slice e hi lo) = hi - lo + 1 ∧
    evalExpr we env (if lo = 0 ∧ hi + 1 = widthOf we e then e else .slice e hi lo) =
      some (mask (hi - lo + 1) (v >>> lo)) ∧
    (∀ x ∈ refsOf (if lo = 0 ∧ hi + 1 = widthOf we e then e else .slice e hi lo),
      x ∈ refsOf e) := by
  by_cases hfull : lo = 0 ∧ hi + 1 = widthOf we e
  · rw [if_pos hfull]
    obtain ⟨rfl, hw⟩ := hfull
    refine ⟨hs, by omega, ?_, fun x hx => hx⟩
    have hlt := hb v hv
    rw [← hw] at hlt
    rw [hv]
    simp [mask, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hfull]
    exact ⟨.slice hs, by simp [widthOf],
      by simp only [evalExpr, hv, Option.bind_eq_bind, Option.bind_some],
      fun x hx => refs_slice_mem.mp hx⟩

/-- **`rSlice` is the part-select.** On a normal form reading fitting names
it returns a normal form of width `hi - lo + 1` whose value is the selected
bits, reading no new name. -/
theorem rSlice_sound (we : WEnv) (env : Env) :
    ∀ {e : Expr}, RShape we e → (∀ x ∈ refsOf e, env x < 2 ^ we x) →
      ∀ (hi lo v : Nat), evalExpr we env e = some v →
        RShape we (rSlice we e hi lo) ∧ widthOf we (rSlice we e hi lo) = hi - lo + 1 ∧
        evalExpr we env (rSlice we e hi lo) = some (mask (hi - lo + 1) (v >>> lo)) ∧
        (∀ x ∈ refsOf (rSlice we e hi lo), x ∈ refsOf e)
  | .const c w, .const h0 hlt, _, hi, lo, v, hv => by
    rw [evalConst_fit we env h0 hlt] at hv
    cases hv
    simp only [rSlice]
    split
    · rename_i hfull
      obtain ⟨rfl, rfl⟩ := hfull
      refine ⟨.const h0 hlt, by simp [widthOf], ?_, fun x hx => hx⟩
      rw [evalConst_fit we env h0 hlt]
      have hc : c.toNat < 2 ^ (hi + 1) := by omega
      simp [mask, Nat.mod_eq_of_lt hc]
    · have hk : mask (hi - lo + 1) (c.toNat >>> lo) < 2 ^ (hi - lo + 1) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have h0' : (0 : Int) ≤ Int.ofNat (mask (hi - lo + 1) (c.toNat >>> lo)) :=
        Int.natCast_nonneg _
      have hlt' : Int.ofNat (mask (hi - lo + 1) (c.toNat >>> lo)) <
          ((2 ^ (hi - lo + 1) : Nat) : Int) := Int.ofNat_lt.mpr hk
      refine ⟨.const h0' hlt', by simp [widthOf], ?_, fun x hx => by simp [refsOf] at hx⟩
      rw [evalConst_fit we env h0' hlt']
      simp
  | .ref x, hs, hr, hi, lo, v, hv => by
    simp only [rSlice]
    exact slice_generic we env hs (fun v hv => rShape_bound we env hs hr v hv) hi lo v hv
  | .op o [a, b], hs, hr, hi, lo, v, hv => by
    simp only [rSlice]
    exact slice_generic we env hs (fun v hv => rShape_bound we env hs hr v hv) hi lo v hv
  | .op o [a], hs, hr, hi, lo, v, hv => by
    simp only [rSlice]
    exact slice_generic we env hs (fun v hv => rShape_bound we env hs hr v hv) hi lo v hv
  | .op .mux [c, a, b], hs, hr, hi, lo, v, hv => by
    simp only [rSlice]
    exact slice_generic we env hs (fun v hv => rShape_bound we env hs hr v hv) hi lo v hv
  | .slice e hi' lo', hs, hr, hi, lo, v, hv => by
    simp only [rSlice]
    exact slice_generic we env hs (fun v hv => rShape_bound we env hs hr v hv) hi lo v hv
  | .concat [a, b], .concat ha hb, hr, hi, lo, v, hv => by
    obtain ⟨va, hva⟩ := rShape_eval we env ha
    obtain ⟨vb, hvb⟩ := rShape_eval we env hb
    have hra : ∀ x ∈ refsOf a, env x < 2 ^ we x :=
      fun x hx => hr x (refs_concat_mem.mpr (Or.inl hx))
    have hrb : ∀ x ∈ refsOf b, env x < 2 ^ we x :=
      fun x hx => hr x (refs_concat_mem.mpr (Or.inr hx))
    have hba := rShape_bound we env ha hra va hva
    have hbb := rShape_bound we env hb hrb vb hvb
    have hval : evalExpr we env (.concat [a, b]) =
        some (va * 2 ^ widthOf we b + vb) := by
      rw [eval_concat2 we env a b va vb hva hvb]
      simp only [mask, Nat.mod_eq_of_lt hba, Nat.mod_eq_of_lt hbb]
      rw [concat_val va vb _ hbb]
    rw [hval] at hv
    cases hv
    simp only [rSlice]
    split
    · rename_i hfull
      obtain ⟨rfl, hw⟩ := hfull
      refine ⟨.concat ha hb, by rw [widthOf_concat2]; omega, ?_, fun x hx => hx⟩
      rw [hval]
      have hlt : va * 2 ^ widthOf we b + vb < 2 ^ (hi + 1) := by
        rw [hw, Nat.pow_add]
        calc va * 2 ^ widthOf we b + vb
            < va * 2 ^ widthOf we b + 2 ^ widthOf we b := Nat.add_lt_add_left hbb _
          _ = (va + 1) * 2 ^ widthOf we b := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ 2 ^ widthOf we a * 2 ^ widthOf we b := Nat.mul_le_mul_right _ hba
      simp [mask, Nat.mod_eq_of_lt hlt]
    · split
      · rename_i hge
        obtain ⟨s, w, e, r⟩ := rSlice_sound we env ha hra (hi - widthOf we b)
          (lo - widthOf we b) va hva
        refine ⟨s, by rw [w]; omega, ?_, fun x hx => refs_concat_mem.mpr (Or.inl (r x hx))⟩
        have hk : hi - widthOf we b - (lo - widthOf we b) + 1 = hi - lo + 1 := by omega
        rw [e, slice_hi va vb _ lo _ hbb hge, hk]
      · split
        · rename_i hlt
          obtain ⟨s, w, e, r⟩ := rSlice_sound we env hb hrb hi lo vb hvb
          refine ⟨s, w, ?_, fun x hx => refs_concat_mem.mpr (Or.inr (r x hx))⟩
          rw [e, slice_lo va vb _ lo _ (by omega)]
        · exact ⟨.slice (.concat ha hb), by simp [widthOf], eval_slice we env hval hi lo,
            fun x hx => refs_slice_mem.mp hx⟩

/-! ## The smart constructors -/

theorem evalOp2_args (we : WEnv) (o : Operator) {a b a' b' : Expr} (va vb w : Nat)
    (ha : widthOf we a' = widthOf we a) (hb : widthOf we b' = widthOf we b) :
    evalOp we o [a', b'] [va, vb] w = evalOp we o [a, b] [va, vb] w := by
  cases o <;> simp [evalOp, ha, hb]

theorem widthOf_op2_args (we : WEnv) (o : Operator) {a b a' b' : Expr}
    (ha : widthOf we a' = widthOf we a) (hb : widthOf we b' = widthOf we b) :
    widthOf we (.op o [a', b']) = widthOf we (.op o [a, b]) := by
  cases o <;> simp [widthOf, ha, hb]

theorem evalOp1_args (we : WEnv) (o : Operator) {a a' : Expr} (va w : Nat)
    (ha : widthOf we a' = widthOf we a) :
    evalOp we o [a'] [va] w = evalOp we o [a] [va] w := by
  cases o <;> simp [evalOp, ha]

theorem widthOf_op1_args (we : WEnv) (o : Operator) {a a' : Expr}
    (ha : widthOf we a' = widthOf we a) :
    widthOf we (.op o [a']) = widthOf we (.op o [a]) := by
  cases o <;> simp [widthOf, ha]

/-- Names all of which are in `ins` fit their widths. -/
theorem refs_fit {we : WEnv} {ins : List String} {init : Env}
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) {e : Expr}
    (h : (refsOf e).all (fun x => ins.contains x) = true) :
    ∀ x ∈ refsOf e, init x < 2 ^ we x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  exact hins x (by simpa using this)

/-- **`rBin` is the two-operand node.** -/
theorem rBin_sound {we : WEnv} {ins : List String} {init : Env}
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) {o : Operator} (ho : rBinOk o = true)
    {a b : Expr} (sa : RShape we a) (sb : RShape we b) {va vb : Nat}
    (hva : evalExpr we init a = some va) (hvb : evalExpr we init b = some vb) :
    RShape we (rBin we ins o a b) ∧
    widthOf we (rBin we ins o a b) = widthOf we (.op o [a, b]) ∧
    evalExpr we init (rBin we ins o a b) = evalExpr we init (.op o [a, b]) := by
  have generic : RShape we (.op o [a, b]) := .bin ho sa sb
  unfold rBin
  split
  · rename_i mv w
    -- `a & const`
    have hand : widthOf we (.op .and [a, .const mv w]) = max (widthOf we a) w := by
      simp [widthOf]
    cases sb with
    | const h0 hlt =>
      rw [evalConst_fit we init h0 hlt] at hvb
      cases hvb
      have hev : evalExpr we init (.op .and [a, .const mv w]) =
          some (mask (max (widthOf we a) w) (va &&& mv.toNat)) := by
        have hc := evalConst_fit we init h0 hlt
        have hl : evalList we init [a, .const mv w] = some [va, mv.toNat] := by
          simp only [evalList, hva, hc, Option.bind_eq_bind, Option.bind_some]
        rw [evalExpr, hl]
        simp only [Option.bind_eq_bind, Option.bind_some, hand, evalOp]
      split
      · rename_i hc
        obtain ⟨hmv, hwa, hrefs⟩ := hc
        have hbound : va < 2 ^ w := by
          rw [← hwa]
          exact rShape_bound we init sa (refs_fit hins hrefs) va hva
        refine ⟨sa, by rw [hand, hwa, Nat.max_self], ?_⟩
        rw [hev, hva, hwa, Nat.max_self]
        have hmvn : mv.toNat = 2 ^ w - 1 := by rw [hmv]; simp
        rw [hmvn, and_mask va w hbound]
      · split
        · rename_i hz
          subst hz
          have hz0 : (0 : Int) < ((2 ^ max (widthOf we a) w : Nat) : Int) := by
            have := Nat.two_pow_pos (max (widthOf we a) w)
            omega
          refine ⟨.const (Int.le_refl 0) hz0, by simp [widthOf], ?_⟩
          rw [hev, evalConst_fit we init (Int.le_refl 0) hz0]
          simp [mask]
        · exact ⟨generic, rfl, rfl⟩
  · exact ⟨generic, rfl, rfl⟩

/-- **`rMux` is the mux node.** -/
theorem rMux_sound {we : WEnv} {ins : List String} {init : Env}
    (hins : ∀ x ∈ ins, init x < 2 ^ we x)
    {c a b e' : Expr} (sc : RShape we c) (sa : RShape we a) (sb : RShape we b)
    {vc va vb : Nat} (hvc : evalExpr we init c = some vc)
    (hva : evalExpr we init a = some va) (hvb : evalExpr we init b = some vb)
    (h : rMux we ins c a b = some e') :
    RShape we e' ∧ widthOf we e' = widthOf we a ∧
    evalExpr we init e' = some (if vc ≠ 0 then va else vb) := by
  unfold rMux at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨rfl, rfl, hw, hrefs⟩ := hc
    have h1 : evalExpr we init (.const 1 1) = some 1 :=
      evalConst_fit we init (by decide) (by decide)
    have h0 : evalExpr we init (.const 0 1) = some 0 :=
      evalConst_fit we init (by decide) (by decide)
    rw [h1] at hva
    rw [h0] at hvb
    cases hva
    cases hvb
    have hb : vc < 2 ^ 1 := by
      rw [← hw]
      exact rShape_bound we init sc (refs_fit hins hrefs) vc hvc
    refine ⟨sc, by simp [widthOf, hw], ?_⟩
    rw [hvc]
    have : vc = 0 ∨ vc = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · split at h
    · rename_i hw
      cases h
      refine ⟨.mux sc sa sb hw, by simp [widthOf], ?_⟩
      simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind, Option.bind_some]
      simp [evalOp]
    · cases h

/-! ## Normalisation -/

/-- What the definitions seen so far guarantee, in the current environment. -/
def RDefsOk (we : WEnv) (init env : Env) (defs : List (String × Expr)) : Prop :=
  (∀ x d, defs.lookup x = some d → RShape we d ∧ evalExpr we init d = some (env x)) ∧
  (∀ x, defs.lookup x = none → env x = init x)

set_option maxHeartbeats 1000000 in
/-- **A normal form has the value of the expression it normalises**: it is
a normal form of the same width, and the expression evaluates, in the
current environment, to what the normal form evaluates to in the initial
one. -/
theorem rNormE_sound {we : WEnv} {ins : List String} {defs : List (String × Expr)}
    {init env : Env} (hd : RDefsOk we init env defs)
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) :
    ∀ (r e' : Expr), rNormE we ins defs r = some e' →
      RShape we e' ∧ widthOf we e' = widthOf we r ∧
      ∃ v, evalExpr we env r = some v ∧ evalExpr we init e' = some v
  | .const v w, e', h => by
    simp only [rNormE] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨.const hc.1 hc.2, rfl, _, evalConst_fit we env hc.1 hc.2,
        evalConst_fit we init hc.1 hc.2⟩
    · cases h
  | .ref x, e', h => by
    simp only [rNormE] at h
    cases hl : defs.lookup x with
    | some d =>
      rw [hl] at h
      simp only at h
      by_cases hw : we x = widthOf we d
      · rw [if_pos hw] at h
        cases h
        obtain ⟨hs, he⟩ := hd.1 x _ hl
        exact ⟨hs, by simp [widthOf, hw], env x, rfl, he⟩
      · rw [if_neg hw] at h; cases h
    | none =>
      rw [hl] at h
      cases h
      exact ⟨.ref x, rfl, env x, rfl, by simp [evalExpr, hd.2 x hl]⟩
  | .op .mux [c, a, b], e', h => by
    simp only [rNormE] at h
    cases hcn : rNormE we ins defs c with
    | none => simp [hcn] at h
    | some c' =>
      cases han : rNormE we ins defs a with
      | none => simp [hcn, han] at h
      | some a' =>
        cases hbn : rNormE we ins defs b with
        | none => simp [hcn, han, hbn] at h
        | some b' =>
          simp only [hcn, han, hbn, Option.bind_eq_bind, Option.bind_some] at h
          obtain ⟨sc, -, vc, hvc, hvc'⟩ := rNormE_sound hd hins c c' hcn
          obtain ⟨sa, wa, va, hva, hva'⟩ := rNormE_sound hd hins a a' han
          obtain ⟨sb, -, vb, hvb, hvb'⟩ := rNormE_sound hd hins b b' hbn
          obtain ⟨se, we', ee⟩ := rMux_sound hins sc sa sb hvc' hva' hvb' h
          refine ⟨se, by rw [we', wa]; simp [widthOf], if vc ≠ 0 then va else vb, ?_, ee⟩
          simp only [evalExpr, evalList, hvc, hva, hvb, Option.bind_eq_bind, Option.bind_some]
          simp [evalOp]
  | .op o [a, b], e', h => by
    simp only [rNormE] at h
    split at h
    · rename_i ho
      cases ha : rNormE we ins defs a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : rNormE we ins defs b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          obtain ⟨sa, wa, va, hva, hva'⟩ := rNormE_sound hd hins a a' ha
          obtain ⟨sb, wb, vb, hvb, hvb'⟩ := rNormE_sound hd hins b b' hb
          obtain ⟨se, we', ee⟩ := rBin_sound hins ho sa sb hva' hvb'
          have hgen : RShape we (.op o [a', b']) := .bin ho sa sb
          obtain ⟨v, hv⟩ := rShape_eval we init hgen
          refine ⟨se, by rw [we', widthOf_op2_args we o wa wb], v, ?_, by rw [ee, hv]⟩
          simp only [evalExpr, evalList, hva', hvb', Option.bind_eq_bind, Option.bind_some] at hv
          simp only [evalExpr, evalList, hva, hvb, Option.bind_eq_bind, Option.bind_some]
          rw [← widthOf_op2_args we o wa wb, ← evalOp2_args we o va vb _ wa wb]
          exact hv
    · cases h
  | .op o [a], e', h => by
    simp only [rNormE] at h
    split at h
    · rename_i ho
      cases ha : rNormE we ins defs a with
      | none => simp [ha] at h
      | some a' =>
        simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨sa, wa, va, hva, hva'⟩ := rNormE_sound hd hins a a' ha
        have hgen : RShape we (.op o [a']) := .un ho sa
        obtain ⟨v, hv⟩ := rShape_eval we init hgen
        refine ⟨hgen, widthOf_op1_args we o wa, v, ?_, hv⟩
        simp only [evalExpr, evalList, hva', Option.bind_eq_bind, Option.bind_some] at hv
        simp only [evalExpr, evalList, hva, Option.bind_eq_bind, Option.bind_some]
        rw [← widthOf_op1_args we o wa, ← evalOp1_args we o va _ wa]
        exact hv
    · cases h
  | .concat [a, b], e', h => by
    simp only [rNormE] at h
    cases ha : rNormE we ins defs a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : rNormE we ins defs b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨sa, wa, va, hva, hva'⟩ := rNormE_sound hd hins a a' ha
        obtain ⟨sb, wb, vb, hvb, hvb'⟩ := rNormE_sound hd hins b b' hb
        refine ⟨.concat sa sb, by rw [widthOf_concat2, widthOf_concat2, wa, wb], _,
          eval_concat2 we env a b va vb hva hvb, ?_⟩
        rw [eval_concat2 we init a' b' va vb hva' hvb', wa, wb]
  | .slice e hi lo, e', h => by
    simp only [rNormE] at h
    cases he : rNormE we ins defs e with
    | none => simp [he] at h
    | some e1 =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i hrefs
        cases h
        obtain ⟨se, -, v, hv, hv'⟩ := rNormE_sound hd hins e e1 he
        obtain ⟨s, w, ev, -⟩ := rSlice_sound we init se (refs_fit hins hrefs) hi lo v hv'
        exact ⟨s, by rw [w]; simp [widthOf], _, eval_slice we env hv hi lo, ev⟩
      · cases h
  | .op _ [], _, h => by simp [rNormE] at h
  | .op .mux (_ :: _ :: _ :: _ :: _), _, h => by simp [rNormE] at h
  | .concat [], _, h => by simp [rNormE] at h
  | .concat [_], _, h => by simp [rNormE] at h
  | .concat (_ :: _ :: _ :: _), _, h => by simp [rNormE] at h
  | .sliceDim _ _ _, _, h => by simp [rNormE] at h
  | .index _ _, _, h => by simp [rNormE] at h

/-- A body `rNormBody` accepts evaluates, and every name's normal form
carries its value. -/
theorem rNormBody_sound {we : WEnv} {ins : List String} {mems : MEnv} {init : Env}
    (hins : ∀ x ∈ ins, init x < 2 ^ we x) :
    ∀ (body : List Stmt) (defs D : List (String × Expr)) (env : Env),
      RDefsOk we init env defs → rNormBody we ins defs body = some D →
      ∃ envF, evalAssigns we mems body env = some envF ∧ RDefsOk we init envF D
  | [], defs, D, env, hd, h => by
    simp only [rNormBody, Option.some.injEq] at h
    subst h; exact ⟨env, rfl, hd⟩
  | .assign l r :: rest, defs, D, env, hd, h => by
    simp only [rNormBody] at h
    cases he : rNormE we ins defs r with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨hs, -, v, hv, hv'⟩ := rNormE_sound hd hins r e he
      have hd' : RDefsOk we init (fun n => if n = l then v else env n) ((l, e) :: defs) := by
        refine ⟨fun x d hx => ?_, fun x hx => ?_⟩
        · rw [lookup_cons_eq'] at hx
          split at hx
          · rename_i hxl; cases hx; subst hxl; simp [hs, hv']
          · rename_i hxl
            obtain ⟨a, b⟩ := hd.1 x d hx
            exact ⟨a, by simp [hxl, b]⟩
        · rw [lookup_cons_eq'] at hx
          split at hx
          · cases hx
          · rename_i hxl; simp [hxl, hd.2 x hx]
      obtain ⟨envF, hev, hdF⟩ := rNormBody_sound (mems := mems) hins rest _ D _ hd' h
      exact ⟨envF, by simp [evalAssigns, hv, hev], hdF⟩
  | .register .. :: _, _, _, _, _, h => by simp [rNormBody] at h
  | .memory .. :: _, _, _, _, _, h => by simp [rNormBody] at h
  | .inst .. :: _, _, _, _, _, h => by simp [rNormBody] at h

/-! ## One cycle -/

theorem regOf_some {rM : List (String × String × (String × Sparkle.IR.Type.ResetKind) × Expr × Int)}
    {name : String} {rm : String × String × (String × Sparkle.IR.Type.ResetKind) × Expr × Int}
    (h : regOf rM name = some rm) : rm ∈ rM ∧ rm.1 = name := by
  unfold regOf at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

open Sparkle.IR.RegDedup (declWidth) in
set_option maxHeartbeats 4000000 in
/-- **`refineCheck` is sound for one cycle.** With reset low and fitting
inputs and register states, both modules step: the outputs agree, every
register update of `o` is the update of the same register of `m`, and the
updates of `m` stay width-bounded. -/
theorem refineCheck_step_sound {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) {mems : MEnv} {init : Env}
    (hins : ∀ x ∈ m.inputs.map (·.name), init x < 2 ^ declWidth m x)
    (hregs : ∀ r ∈ seqRegs m, init r.1 < 2 ^ declWidth m r.1)
    (hrst : init "rst" = 0) {initO : Env}
    (hagree : ∀ x ∈ ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      initO x = init x)
    (hrstO : initO "rst" = 0) :
    ∃ envM envO nextsM nextsO,
      stepModule (declWidth m) m.body init mems = some (envM, nextsM, mems) ∧
      stepModule (declWidth o) o.body initO mems = some (envO, nextsO, mems) ∧
      (∀ p ∈ m.outputs, envO p.name = envM p.name) ∧
      nextsM.map (·.1) = (seqRegs m).map (·.1) ∧
      nextsO.map (·.1) = (seqRegs o).map (·.1) ∧
      (∀ pr ∈ nextsO, pr ∈ nextsM) ∧
      (∀ pr ∈ nextsM, pr.2 < 2 ^ declWidth m pr.1) := by
  simp only [refineCheck] at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨h1, h2⟩ := hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hinEq, houtEq⟩, hokM⟩, hokO⟩, hndM⟩, hndO⟩, hdisjM⟩, hdisjO⟩, hzM⟩,
    hzO⟩, hpairs⟩, hallM⟩ := h1
  -- every register of `o` and its namesake in `m`
  have hpair : ∀ ro ∈ seqRegs o, ∃ rm, regOf (seqRegs m) ro.1 = some rm ∧ rm ∈ seqRegs m ∧
      rm.1 = ro.1 ∧ rm.2.2.1.1 = "rst" ∧ ro.2.2.1.1 = "rst" ∧
      declWidth m rm.1 = declWidth o ro.1 := by
    intro ro hro
    have hf := List.all_eq_true.mp hpairs ro hro
    cases hrm : regOf (seqRegs m) ro.1 with
    | none => rw [hrm] at hf; cases hf
    | some rm =>
      rw [hrm] at hf
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
      obtain ⟨hmem, hname⟩ := regOf_some hrm
      exact ⟨rm, rfl, hmem, hname, hf.1.1.1.1.1.2, hf.1.1.1.1.2, hf.1.2⟩
  have hallM' : ∀ rm ∈ seqRegs m, rm.2.2.1.1 = "rst" := by
    intro rm hrm
    have := List.all_eq_true.mp hallM rm hrm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this.1
  -- fitting environments over both reference domains
  have hinsMfit : ∀ x ∈ (m.inputs.map (·.name) ++ (seqRegs m).map (·.1)),
      init x < 2 ^ (declWidth m) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hins x hx
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
      exact he ▸ hregs r hr
  have hwEq : ∀ x ∈ ((m.inputs.map (·.name)).filter
      (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      declWidth m x = declWidth o x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨-, hwx⟩ := List.mem_filter.mp hx
      simpa using hwx
    · obtain ⟨ro, hro, he⟩ := List.mem_map.mp hx
      obtain ⟨rm, -, -, hname, -, -, hw⟩ := hpair ro hro
      subst he
      rw [← hname, hw, hname]
  have hinsOfit : ∀ x ∈ ((m.inputs.map (·.name)).filter
      (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      initO x < 2 ^ (declWidth o) x := by
    intro x hx
    rw [hagree x hx, ← hwEq x hx]
    rcases List.mem_append.mp hx with hx | hx
    · exact hins x (List.mem_filter.mp hx).1
    · obtain ⟨ro, hro, he⟩ := List.mem_map.mp hx
      obtain ⟨rm, -, hmem, hname, -, -, -⟩ := hpair ro hro
      subst he
      rw [← hname]
      exact hregs rm hmem
  -- the normal-form half of the check
  split at h2
  case h_2 => cases h2
  rename_i dm dO hnm hno
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨houts, hnexts⟩, hsomeM⟩ := h2
  have hd0M : RDefsOk (declWidth m) init init [] :=
    ⟨fun x d hx => by simp [List.lookup] at hx, fun _ _ => rfl⟩
  have hd0O : RDefsOk (declWidth o) initO initO [] :=
    ⟨fun x d hx => by simp [List.lookup] at hx, fun _ _ => rfl⟩
  obtain ⟨envM, hevM, hdM⟩ :=
    rNormBody_sound (mems := mems) hinsMfit (seqAssigns m) [] dm init hd0M hnm
  obtain ⟨envO, hevO, hdO⟩ :=
    rNormBody_sound (mems := mems) hinsOfit (seqAssigns o) [] dO initO hd0O hno
  have hevMfull : evalAssigns (declWidth m) mems m.body init = some envM := by
    rw [evalAssigns_seq_skip hokM]
    exact hevM
  have hevOfull : evalAssigns (declWidth o) mems o.body initO = some envO := by
    rw [evalAssigns_seq_skip hokO]
    exact hevO
  -- reset stays low through the assign segments
  have hzMfull : m.body.all (fun st => match st with
      | .assign l _ => l != "rst"
      | _ => true) = true := by
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | assign l r => exact List.all_eq_true.mp hzM _ (List.mem_filter.mpr ⟨hst, rfl⟩)
    | register o c rk i iv => rfl
    | memory n aw dw md wa wd wen ra rd ep ew rp => rfl
    | inst n mn conns => rfl
  have hzOfull : o.body.all (fun st => match st with
      | .assign l _ => l != "rst"
      | _ => true) = true := by
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | assign l r => exact List.all_eq_true.mp hzO _ (List.mem_filter.mpr ⟨hst, rfl⟩)
    | register o c rk i iv => rfl
    | memory n aw dw md wa wd wen ra rd ep ew rp => rfl
    | inst n mn conns => rfl
  have hrstM : envM "rst" = 0 := by
    rw [evalAssigns_keeps "rst" hokM hzMfull hevMfull]
    exact hrst
  have hrstOF : envO "rst" = 0 := by
    rw [evalAssigns_keeps "rst" hokO hzOfull hevOfull]
    exact hrstO
  have hif : ¬((0 : Nat) ≠ 0) := fun h => h rfl
  -- a normal form of `o` has the same value in both initial environments
  have hcongr : ∀ {e : Expr}, RShape (declWidth o) e →
      (refsOf e).all (fun x => ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)).contains x) = true →
      evalExpr (declWidth m) init e = evalExpr (declWidth o) initO e := by
    intro e hs hrefs
    refine (rShape_congr hs (fun x hx => ?_)).2.2
    have hx' : x ∈ ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)) := by
      have := List.all_eq_true.mp hrefs x hx
      simpa [List.contains_eq_mem] using this
    exact ⟨hwEq x hx', (hagree x hx').symm⟩
  -- output correspondence
  have houtCorr : ∀ p ∈ m.outputs, envO p.name = envM p.name := by
    intro p hp
    have h := List.all_eq_true.mp houts p hp
    split at h
    case h_2 => cases h
    rename_i em eo hem heo
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨heq, hrefsO⟩ := h
    obtain ⟨-, hvM⟩ := hdM.1 p.name em hem
    obtain ⟨hsO, hvO⟩ := hdO.1 p.name eo heo
    rw [heq, hcongr hsO hrefsO, hvO] at hvM
    exact Option.some.inj hvM
  -- register next values
  have hfoldM : seqRegsL m.body = seqRegs m := (seqRegs_eq m).symm
  have hfoldO : seqRegsL o.body = seqRegs o := (seqRegs_eq o).symm
  have hvMall : ∀ r ∈ seqRegsL m.body, evalExpr (declWidth m) envM r.2.2.2.1 =
      some ((evalExpr (declWidth m) envM r.2.2.2.1).getD 0) := by
    intro r hr
    have hr' : r ∈ seqRegs m := hfoldM ▸ hr
    have hs := List.all_eq_true.mp hsomeM r hr'
    obtain ⟨fm, hfm⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨-, -, v, hv, -⟩ := rNormE_sound hdM hinsMfit r.2.2.2.1 fm hfm
    rw [hv]
    rfl
  have hregNext : ∀ ro ∈ seqRegs o, ∀ rm, regOf (seqRegs m) ro.1 = some rm →
      evalExpr (declWidth o) envO ro.2.2.2.1 =
        some ((evalExpr (declWidth o) envO ro.2.2.2.1).getD 0) ∧
      (evalExpr (declWidth m) envM rm.2.2.2.1).getD 0 =
        (evalExpr (declWidth o) envO ro.2.2.2.1).getD 0 := by
    intro ro hro rm hrm
    have hn := List.all_eq_true.mp hnexts ro hro
    rw [hrm] at hn
    simp only at hn
    split at hn
    case h_2 => cases hn
    rename_i fm fo hfm hfo
    rw [Bool.and_eq_true, decide_eq_true_eq] at hn
    obtain ⟨heq, hrefsO⟩ := hn
    obtain ⟨-, -, vM, hevalMr, hevalMf⟩ := rNormE_sound hdM hinsMfit rm.2.2.2.1 fm hfm
    obtain ⟨hsFo, -, vO, hevalOr, hevalOf⟩ := rNormE_sound hdO hinsOfit ro.2.2.2.1 fo hfo
    rw [heq, hcongr hsFo hrefsO, hevalOf] at hevalMf
    have hvals : vO = vM := Option.some.inj hevalMf
    refine ⟨by rw [hevalOr]; rfl, ?_⟩
    rw [hevalMr, hevalOr]
    simp [hvals]
  have hvOall : ∀ r ∈ seqRegsL o.body, evalExpr (declWidth o) envO r.2.2.2.1 =
      some ((evalExpr (declWidth o) envO r.2.2.2.1).getD 0) := by
    intro r hr
    have hr' : r ∈ seqRegs o := hfoldO ▸ hr
    obtain ⟨rm, hrm, -⟩ := hpair r hr'
    exact (hregNext r hr' rm hrm).1
  have hnM := regNexts_seq_map (we := (declWidth m)) (mems := mems) (envF := envM)
    (f := fun e => (evalExpr (declWidth m) envM e).getD 0) hokM hvMall
  have hnO := regNexts_seq_map (we := (declWidth o)) (mems := mems) (envF := envO)
    (f := fun e => (evalExpr (declWidth o) envO e).getD 0) hokO hvOall
  rw [hfoldM] at hnM
  rw [hfoldO] at hnO
  have hmemM := memNexts_seqStmtOk (we := (declWidth m)) (mems := mems) (envF := envM) hokM
  have hmemO := memNexts_seqStmtOk (we := (declWidth o)) (mems := mems) (envF := envO) hokO
  refine ⟨envM, envO,
    (seqRegs m).map (fun r => (r.1, if envM r.2.2.1.1 ≠ 0 then
        encodeInit r.2.2.2.2 ((declWidth m) r.1)
      else mask ((declWidth m) r.1) ((evalExpr (declWidth m) envM r.2.2.2.1).getD 0))),
    (seqRegs o).map (fun r => (r.1, if envO r.2.2.1.1 ≠ 0 then
        encodeInit r.2.2.2.2 ((declWidth o) r.1)
      else mask ((declWidth o) r.1) ((evalExpr (declWidth o) envO r.2.2.2.1).getD 0))),
    ?_, ?_, houtCorr, ?_, ?_, ?_, ?_⟩
  · simp only [stepModule, hevMfull, hnM, hmemM, Option.bind_eq_bind, Option.bind_some]
  · simp only [stepModule, hevOfull, hnO, hmemO, Option.bind_eq_bind, Option.bind_some]
  · rw [List.map_map]
    rfl
  · rw [List.map_map]
    rfl
  · intro pr hpr
    obtain ⟨ro, hro, he⟩ := List.mem_map.mp hpr
    obtain ⟨rm, hrm, hmem, hname, hkM, hkO, hw⟩ := hpair ro hro
    subst he
    refine List.mem_map.mpr ⟨rm, hmem, ?_⟩
    rw [hkM, hkO, hrstM, hrstOF, if_neg hif, if_neg hif, hname, ← hname, hw,
      (hregNext ro hro rm hrm).2, hname]
  · intro pr hpr
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hpr
    subst he
    show (if envM r.2.2.1.1 ≠ 0 then encodeInit r.2.2.2.2 ((declWidth m) r.1)
      else mask ((declWidth m) r.1) ((evalExpr (declWidth m) envM r.2.2.2.1).getD 0)) <
        2 ^ (declWidth m) r.1
    rw [hallM' r hr, hrstM, if_neg hif]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## Any number of cycles -/

/-- Applying a nodup update list at the name of one of its entries yields
that entry's value. -/
theorem applyNexts_mem {st : String → Nat} {nexts : List (String × Nat)}
    (hnd : (nexts.map (·.1)).Nodup) {pr : String × Nat} (h : pr ∈ nexts) :
    applyNexts st nexts pr.1 = pr.2 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  exact applyNexts_at hnd i hi

/-- An entry of an update list for every name in its name list. -/
theorem nexts_entry {nexts : List (String × Nat)} {names : List String}
    (h : nexts.map (·.1) = names) {x : String} (hx : x ∈ names) :
    ∃ pr ∈ nexts, pr.1 = x := by
  rw [← h] at hx
  obtain ⟨pr, hpr, he⟩ := List.mem_map.mp hx
  exact ⟨pr, hpr, he⟩

open Sparkle.IR.RegDedup (declWidth) in
set_option maxHeartbeats 2000000 in
/-- **Accepted pairs are trace-equivalent.** Under the canonical seeding
from any fitting input stream that holds reset low, and from any pair of
register states equal on the registers of `o` (with the `m` state
width-bounded), both modules run for `k` cycles and their output streams
coincide, cycle for cycle. -/
theorem refineCheck_run_sound {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name))
    (hrstZ : ∀ t, ins t "rst" = 0) :
    ∀ (k : Nat) (stM stO : String → Nat) (mems : MEnv),
      (∀ r ∈ seqRegs o, stO r.1 = stM r.1) →
      (∀ r ∈ seqRegs m, stM r.1 < 2 ^ declWidth m r.1) →
      ∃ trM trO,
        runModule (declWidth m) m.body (seedIn m ins) k stM mems = some trM ∧
        runModule (declWidth o) o.body (seedIn m ins) k stO mems = some trO ∧
        trM.length = k ∧ trO.length = k ∧
        ∀ p ∈ m.outputs, trO.map (fun e => e p.name) = trM.map (fun e => e p.name) := by
  intro k
  induction k with
  | zero =>
    intro stM stO mems hcpl hfit
    exact ⟨[], [], rfl, rfl, rfl, rfl, fun p _ => rfl⟩
  | succ k ih =>
    intro stM stO mems hcpl hfit
    have hstat := hchk
    simp only [refineCheck] at hstat
    rw [Bool.and_eq_true] at hstat
    obtain ⟨h1, -⟩ := hstat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hinEq, houtEq⟩, hokM⟩, hokO⟩, hndM⟩, hndO⟩, hdisjM⟩, hdisjO⟩, hzM⟩,
      hzO⟩, hpairs⟩, hallM⟩ := h1
    have hcontains : ∀ x ∈ m.inputs.map (·.name),
        ((m.inputs.map (·.name)).contains x) = true := by
      intro x hx
      simpa [List.contains_eq_mem] using hx
    have hnotInM : ∀ r ∈ seqRegs m,
        ((m.inputs.map (·.name)).contains r.1) = false := by
      intro r hr
      have hd := List.all_eq_true.mp hdisjM r hr
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    have hnotInO : ∀ r ∈ seqRegs o,
        ((m.inputs.map (·.name)).contains r.1) = false := by
      intro r hr
      have hd := List.all_eq_true.mp hdisjO r hr
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    have hinsE : ∀ x ∈ m.inputs.map (·.name),
        seedIn m ins k stM x < 2 ^ declWidth m x := by
      intro x hx
      simp only [seedIn]
      rw [if_pos (hcontains x hx)]
      exact hinsFit k x hx
    have hregsE : ∀ r ∈ seqRegs m,
        seedIn m ins k stM r.1 < 2 ^ declWidth m r.1 := by
      intro r hr
      simp only [seedIn]
      rw [if_neg (by rw [hnotInM r hr]; exact Bool.false_ne_true)]
      exact hfit r hr
    have hrstE : seedIn m ins k stM "rst" = 0 := by
      simp only [seedIn]
      rw [if_pos (hcontains _ hrstIn)]
      exact hrstZ k
    have hrstOE : seedIn m ins k stO "rst" = 0 := by
      simp only [seedIn]
      rw [if_pos (hcontains _ hrstIn)]
      exact hrstZ k
    have hagreeE : ∀ x ∈ ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
        seedIn m ins k stO x = seedIn m ins k stM x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hxin, -⟩ := List.mem_filter.mp hx
        simp only [seedIn]
        rw [if_pos (hcontains x hxin), if_pos (hcontains x hxin)]
      · obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
        subst he
        simp only [seedIn]
        rw [if_neg (by rw [hnotInO r hr]; exact Bool.false_ne_true),
          if_neg (by rw [hnotInO r hr]; exact Bool.false_ne_true)]
        exact hcpl r hr
    obtain ⟨envM, envO, nextsM, nextsO, hstepM, hstepO, hout, hnmM, hnmO, hsub, hbnd⟩ :=
      refineCheck_step_sound hchk (mems := mems) hinsE hregsE hrstE hagreeE hrstOE
    have hndM' : (nextsM.map (·.1)).Nodup := by rw [hnmM]; exact hndM
    have hndO' : (nextsO.map (·.1)).Nodup := by rw [hnmO]; exact hndO
    have hcpl' : ∀ r ∈ seqRegs o,
        applyNexts stO nextsO r.1 = applyNexts stM nextsM r.1 := by
      intro r hr
      obtain ⟨pr, hpr, he⟩ := nexts_entry hnmO (List.mem_map_of_mem (f := (·.1)) hr)
      rw [← he, applyNexts_mem hndO' hpr, applyNexts_mem hndM' (hsub pr hpr)]
    have hfit' : ∀ r ∈ seqRegs m,
        applyNexts stM nextsM r.1 < 2 ^ declWidth m r.1 := by
      intro r hr
      obtain ⟨pr, hpr, he⟩ := nexts_entry hnmM (List.mem_map_of_mem (f := (·.1)) hr)
      rw [← he, applyNexts_mem hndM' hpr]
      exact hbnd pr hpr
    obtain ⟨trM', trO', hrunM', hrunO', hlenM', hlenO', houts'⟩ :=
      ih (applyNexts stM nextsM) (applyNexts stO nextsO) mems hcpl' hfit'
    refine ⟨envM :: trM', envO :: trO', ?_, ?_, by simp [hlenM'], by simp [hlenO'], ?_⟩
    · simp only [runModule, hstepM, Option.bind_eq_bind, Option.bind_some, hrunM']
    · simp only [runModule, hstepO, Option.bind_eq_bind, Option.bind_some, hrunO']
    · intro p hp
      simp only [List.map_cons]
      rw [hout p hp, houts' p hp]

open Sparkle.IR.RegDedup (declWidth) in
/-- Transfer an `m`-side canonical-seed run through the check: the accepted
module runs from any state equal on its registers, and its per-cycle outputs
equal the given trace's. -/
theorem refineCheck_transfer {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name))
    (hrstZ : ∀ t, ins t "rst" = 0)
    {k : Nat} {stM stO : String → Nat} {mems : MEnv}
    (hcpl : ∀ r ∈ seqRegs o, stO r.1 = stM r.1)
    (hfit : ∀ r ∈ seqRegs m, stM r.1 < 2 ^ declWidth m r.1)
    {envs : List Env}
    (hrun : runModule (declWidth m) m.body (seedIn m ins) k stM mems = some envs) :
    ∃ envsO,
      runModule (declWidth o) o.body (seedIn m ins) k stO mems = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name := by
  obtain ⟨trM, trO, hrunM, hrunO, hlenM, hlenO, houts⟩ :=
    refineCheck_run_sound hchk ins hinsFit hrstIn hrstZ k stM stO mems hcpl hfit
  rw [hrun] at hrunM
  have htrM : trM = envs := (Option.some.inj hrunM.symm)
  subst htrM
  refine ⟨trO, hrunO, by omega, ?_⟩
  intro p hp j hj hj'
  have h1 := List.getElem_of_eq (houts p hp)
    (by simp only [List.length_map]; omega : j < (trO.map (fun e => e p.name)).length)
  simpa using h1

/-- Refinements compose along a pipeline: `m ⟶ b ⟶ o`. The middle module's
trace is the first's (on the outputs), so a run of `m` transfers to `o`. -/
theorem refineCheck_ports {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs := by
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨h1.1.1.1.1.1.1.1.1.1.1.1, h1.1.1.1.1.1.1.1.1.1.1.2⟩

end Tools.ShippingRefineSoundness
