/-
  Precision selection, as a theorem.

  `Transport.lean` fixes the format at Q15.16 (`scale = 2^16`) and derives one
  ultimate bound.  This file makes the fractional-bit count `f` a variable, so the
  bound becomes a *function* of the precision — and then a question an engineer
  actually asks becomes a proposition Lean can decide:

      "Is Q7.8 good enough for a steady-state error budget of 0.01?"

  The answer here is no, and Q15.16's answer is yes, and both are proven.  That
  claim is simply not expressible while the format is a hardcoded constant, which
  is why `IP/Control/FixedPointGen.lean` parameterizes the circuits.

  ## The shape of the result

  Everything flows from `Transport.lean`'s structure with `2^16` replaced by
  `2^f`:

      ε(f)      = 3 / 2^f                     -- per-step quantization error
      Vbound(f) = 810·ε(f)² / (1 - σ)         -- ultimate bound on V

  `σ` and the contraction rate `ρ` are properties of the *controller*, not the
  format, so they are unchanged — which is itself the useful structural fact:
  **precision affects only the additive floor, never the decay rate.**  A coarser
  format does not make a stable design unstable in this bound; it makes the
  residual error larger.

  ## What this bound deliberately does not cover

  Rounding the *coefficients* is a separate mechanism: it moves the poles, i.e.
  perturbs `ρ`, rather than adding a bounded disturbance.  This file says nothing
  about it, and the two must not be conflated.

  Worth noting because the naive guess about that mechanism is wrong: for
  `IIRBiquadGen.marginalCoeffs`, coefficient rounding pulls the poles *inward*
  (radius 0.968 at `f=4`, 0.998 at `f=8`, 0.99899 at `f=16` — every format
  stable), so coarse quantization *damps* that filter rather than destabilising
  it.  The measured residual is therefore non-monotone in `f`, driven by the
  quantization deadband; see `Tests/IP/Control/PrecisionSweepTest.lean`.  A bound
  on the additive disturbance — which is what is proven here — says nothing either
  way about that, and claiming otherwise would overstate it.

  ## Note on `w`

  The bound depends on `f` alone, not on the total width `w`.  That is correct and
  is the sweep's headline: Q23.8 and Q7.8 have the same accuracy despite Q23.8
  being twice as wide, because they share `f = 8`.  Width buys dynamic range —
  i.e. it postpones saturation — which the clamps handle structurally and the
  bound therefore never sees.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import SparkleProofs.Control.LQRDesign

namespace SparkleProofs.Control.Precision

open SparkleProofs.Control.LQRDesign

/-! ### Precision-dependent quantities -/

/-- One LSB of a format with `f` fractional bits. -/
noncomputable def lsb (f : Nat) : ℝ := 1 / (2 ^ f : ℝ)

theorem lsb_pos (f : Nat) : 0 < lsb f := by
  unfold lsb; positivity

/-- Per-step, per-component quantization error at precision `f`.

    Each state component is two `mulQ`s plus an add, so at most three floors
    contribute; `3·lsb` is a safe (loose) bound.  Same constant as
    `Transport.ε`, now as a function of `f`. -/
noncomputable def ε (f : Nat) : ℝ := 3 * lsb f

theorem eps_pos (f : Nat) : 0 < ε f := by
  unfold ε; have := lsb_pos f; linarith

/-- The ISS decay factor.  A property of the controller, **independent of `f`** —
    this is the structural point noted in the header. -/
noncomputable def σ : ℝ := (1 + ρ) / 2

theorem sigma_lt_one : σ < 1 := by
  unfold σ; have := rho_lt_one; linarith

theorem one_sub_sigma_pos : (0 : ℝ) < 1 - σ := by
  have := sigma_lt_one; linarith

/-- `σ = 79/80`, so `1 - σ = 1/80`.  Pinned as a numeral because every bound
    below divides by it. -/
theorem one_sub_sigma_eq : 1 - σ = 1 / 80 := by
  unfold σ ρ; norm_num

/-- The ultimate bound on `V` at precision `f`: the fixed point of
    `v ↦ σ·v + 810·ε(f)²`. -/
noncomputable def Vbound (f : Nat) : ℝ := 810 * (ε f) ^ 2 / (1 - σ)

theorem Vbound_pos (f : Nat) : 0 < Vbound f := by
  unfold Vbound
  have h1 := one_sub_sigma_pos
  have h2 := eps_pos f
  positivity

/-- Closed form: `Vbound f = 583200 / 4^f`.

    `810 · (3/2^f)² / (1/80) = 810 · 9 · 80 / 4^f = 583200 / 4^f`.  Having the
    numeral makes the two budget theorems below `norm_num` computations rather
    than analytic arguments. -/
theorem Vbound_eq (f : Nat) : Vbound f = 583200 / (4 ^ f : ℝ) := by
  unfold Vbound ε lsb
  rw [one_sub_sigma_eq]
  have h4 : (4 : ℝ) ^ f = (2 ^ f : ℝ) * (2 ^ f : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hne : ((2 : ℝ) ^ f) ≠ 0 := by positivity
  rw [h4]
  field_simp
  ring

/-! ### Monotonicity: more fractional bits is never worse -/

/-- `Vbound` is decreasing in `f`: adding a fractional bit cuts the bound by 4×. -/
theorem Vbound_succ (f : Nat) : Vbound (f + 1) = Vbound f / 4 := by
  rw [Vbound_eq, Vbound_eq, pow_succ]
  have hne : ((4 : ℝ) ^ f) ≠ 0 := by positivity
  field_simp

/-- Monotone: a finer format always gives an at-least-as-good bound. -/
theorem Vbound_antitone {f₁ f₂ : Nat} (h : f₁ ≤ f₂) : Vbound f₂ ≤ Vbound f₁ := by
  rw [Vbound_eq, Vbound_eq]
  have hp : (0 : ℝ) < 4 ^ f₁ := by positivity
  have hle : (4 : ℝ) ^ f₁ ≤ 4 ^ f₂ := pow_le_pow_right₀ (by norm_num) h
  exact div_le_div_of_nonneg_left (by norm_num) hp hle

/-! ### Precision selection

The engineering question, decided.  A budget is a bound on `V`; via
`LQRDesign.V_lower` (`½‖x‖² ≤ V`) it converts to a bound on the state norm, so a
`V`-budget of `B` corresponds to `‖x‖² ≤ 2B`. -/

/-- A representative steady-state error budget on `V`. -/
noncomputable def budget : ℝ := 1 / 100

/-- **Q7.8 misses the budget.**  `Vbound 8 = 583200/65536 ≈ 8.9`, which is three
    orders of magnitude over `0.01`. -/
theorem q7_8_misses_budget : ¬ (Vbound 8 ≤ budget) := by
  rw [Vbound_eq]
  unfold budget
  norm_num

/-- Q11.4 misses it by even more — included so the sweep has a clear loser. -/
theorem q11_4_misses_budget : ¬ (Vbound 4 ≤ budget) := by
  rw [Vbound_eq]
  unfold budget
  norm_num

/-- **Q15.16 meets the budget.**  `Vbound 16 = 583200/4294967296 ≈ 1.36e-4`,
    comfortably under `0.01`. -/
theorem q15_16_meets_budget : Vbound 16 ≤ budget := by
  rw [Vbound_eq]
  unfold budget
  norm_num

/-- The precision at which the budget first becomes satisfiable is `f = 12`:
    `Vbound 12 = 583200/16777216 ≈ 0.0348 > 0.01`, while `Vbound 13 ≈ 0.0087`. -/
theorem q_12_misses_budget : ¬ (Vbound 12 ≤ budget) := by
  rw [Vbound_eq]; unfold budget; norm_num

theorem q_13_meets_budget : Vbound 13 ≤ budget := by
  rw [Vbound_eq]; unfold budget; norm_num

/-- **The precision-selection statement.**  13 fractional bits is exactly the
    threshold for this budget: 12 is not enough, 13 is, and by monotonicity every
    `f ≥ 13` also is.

    This is the theorem that the hardcoded-format version of the development could
    not even state. -/
theorem min_fracBits_for_budget :
    ¬ (Vbound 12 ≤ budget) ∧ (∀ f, 13 ≤ f → Vbound f ≤ budget) := by
  refine ⟨q_12_misses_budget, fun f hf => ?_⟩
  exact le_trans (Vbound_antitone hf) q_13_meets_budget

/-- Converted to the state norm: at Q15.16 the trajectory is ultimately confined
    to `‖x‖² ≤ 2·Vbound 16`, i.e. `‖x‖ ≲ 0.017`. -/
theorem q15_16_state_bound (x1 x2 : ℝ) (h : V x1 x2 ≤ Vbound 16) :
    x1 ^ 2 + x2 ^ 2 ≤ 2 * Vbound 16 := by
  have hlow := V_lower x1 x2
  linarith

end SparkleProofs.Control.Precision
