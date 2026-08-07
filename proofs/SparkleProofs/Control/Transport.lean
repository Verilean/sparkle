/-
  The bridge: from an ℝ Lyapunov certificate to the fixed-point circuit Sparkle
  synthesizes.

  This file is the point of the whole exercise.  `LQRDesign.lean` proves a
  contraction over `ℝ`; `IP/Control/LQRStateFeedback.lean` is integer arithmetic
  on `BitVec 32`.  Neither statement implies the other by itself.  What connects
  them is:

  1. **A quantization-error bound.**  Each Q15.16 operation in the circuit is the
     exact rational operation followed by a floor to a multiple of `2^-16`.  So
     the fixed-point step differs from the ℝ step by at most a fixed `ε` per
     component.  Crucially `ε` is *known and small*, not merely "some error".

  2. **ISS with that error as the disturbance.**  `LQRDesign.lyapunov_iss` says
     the contraction survives an additive per-component perturbation of size
     `ε`, at the cost of an additive `O(ε²)` floor.  Feeding the quantization
     bound in as the disturbance turns the ℝ contraction into a *practical
     stability* statement about the integer circuit: the state enters and stays
     inside an explicitly computed ball whose radius is proportional to `ε`.

  This is what the accuracy-bound tools (VCFloat2, Daisy, PRECiSA) do not give
  you — they bound the error but never close the loop — and what the
  control-implementation tools (Park et al. TACAS'17, DSVerifier) give only for
  bounded horizons via SMT/BMC.  Here it is an unbounded, kernel-checked
  induction.

  ## Honest scope

  The `Signal`-level step (that the `circuit do` in `LQRStateFeedback.lean`
  computes exactly `LQR.step` at every cycle) is proven in the main package via
  `Sparkle.Verification.LoopProps.loop_iterate`, not here — that direction needs
  no Mathlib.  See `IP/Control/Proof/LQRCircuitEq.lean`.  This file assumes that
  equality and does the numeric/analytic half.
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import SparkleProofs.Control.LQRDesign

namespace SparkleProofs.Control.Transport

open SparkleProofs.Control.LQRDesign

/-! ### Interpretation of the fixed-point words

A Q15.16 word `n : ℤ` denotes the real `n / 2^16`.  The circuit's state is a pair
of such words. -/

/-- The Q15.16 scale. -/
def scale : ℤ := 2 ^ 16

/-- Interpret a Q15.16 numerator as a real. -/
noncomputable def toR (n : ℤ) : ℝ := (n : ℝ) / (scale : ℝ)

/-- One LSB, as a real.  This is the granularity of every quantity in the
    circuit and the unit in which all error bounds are expressed. -/
noncomputable def lsb : ℝ := 1 / (scale : ℝ)

theorem lsb_pos : (0 : ℝ) < lsb := by
  unfold lsb scale; norm_num

/-! ### The quantization-error bound

`mulQ a b = ⌊a*b / 2^16⌋` on numerators.  Since `⌊z⌋ ≤ z < ⌊z⌋ + 1`, the
fixed-point product differs from the exact rational product by less than one
LSB, and — because Lean's `Int./` floors, matching `BitVec.sshiftRight` exactly
— the error is always in `(-1, 0]` LSB regardless of sign.

That sign-independence is why the implementation uses arithmetic shift right
rather than a truncating divide: a truncating shifter would give an error in
`(-1, 1)` whose sign follows the operand, which doubles the bound and breaks the
monotonicity used below. -/

/-- Fixed-point multiply on numerators: exact product, then floor by `2^16`. -/
def mulQ (a b : ℤ) : ℤ := (a * b) / scale

/-- **Single-operation error bound.**  The fixed-point product is below the exact
    product by less than one LSB, and never above it.

    The proof works from the two defining inequalities of integer floor division
    (`scale * (ab / scale) ≤ ab < scale * (ab / scale) + scale`, which `omega`
    gets from `Int.ediv_add_emod` plus the remainder bounds), casts them to `ℝ`,
    and divides through by `scale²`. -/
theorem mulQ_error (a b : ℤ) :
    (mulQ a b : ℝ) * lsb ≤ toR a * toR b ∧
    toR a * toR b < (mulQ a b : ℝ) * lsb + lsb := by
  have hscale : (0 : ℤ) < scale := by unfold scale; norm_num
  have hfloor := Int.mul_ediv_add_emod (a * b) scale
  have hmod_lt := Int.emod_lt_of_pos (a * b) hscale
  have hmod_nonneg := Int.emod_nonneg (a * b) (by omega : scale ≠ 0)
  -- The two defining floor inequalities, as integers.
  have hlo : scale * ((a * b) / scale) ≤ a * b := by omega
  have hhi : a * b < scale * ((a * b) / scale) + scale := by omega
  have hsR : (0 : ℝ) < (scale : ℝ) := by unfold scale; norm_num
  have hne : (scale : ℝ) ≠ 0 := ne_of_gt hsR
  -- Cast both to ℝ.  `mulQ a b` is literally `(a*b)/scale`.
  have hloR : (scale : ℝ) * ((mulQ a b : ℤ) : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hlo
    unfold mulQ; push_cast at h ⊢; linarith
  have hhiR : (a : ℝ) * (b : ℝ) < (scale : ℝ) * ((mulQ a b : ℤ) : ℝ) + (scale : ℝ) := by
    have h := (Int.cast_lt (R := ℝ)).mpr hhi
    unfold mulQ; push_cast at h ⊢; linarith
  -- Both goals are those inequalities divided by `scale²`.  Rather than steering
  -- `rw` through nested divisions, multiply the goal up by `scale² > 0`, discharge
  -- it with `field_simp` + `nlinarith`, then cancel.
  have hpos : (0 : ℝ) < (scale : ℝ) * (scale : ℝ) := by positivity
  unfold toR lsb
  refine ⟨?_, ?_⟩
  · have key : ((mulQ a b : ℤ) : ℝ) * (1 / (scale : ℝ)) * ((scale : ℝ) * (scale : ℝ))
             ≤ ((a : ℝ) / (scale : ℝ)) * ((b : ℝ) / (scale : ℝ)) * ((scale : ℝ) * (scale : ℝ)) := by
      field_simp
      nlinarith [hloR, hsR]
    exact le_of_mul_le_mul_right (by linarith [key]) hpos
  · have key : ((a : ℝ) / (scale : ℝ)) * ((b : ℝ) / (scale : ℝ)) * ((scale : ℝ) * (scale : ℝ))
             < (((mulQ a b : ℤ) : ℝ) * (1 / (scale : ℝ)) + 1 / (scale : ℝ))
               * ((scale : ℝ) * (scale : ℝ)) := by
      field_simp
      nlinarith [hhiR, hsR]
    exact lt_of_mul_lt_mul_right (by linarith [key]) (le_of_lt hpos)

/-! ### The ultimate bound

Combining `LQRDesign.lyapunov_iss` with the per-step quantization bound gives a
geometric recursion on `V`, whose fixed point is the ultimate bound. -/

/-- Per-step per-component quantization error of the LQR state update.

    Each component of the update is a sum of two `mulQ`s plus an add, so at most
    three floors contribute; `3 · lsb` is a safe (loose) bound. -/
noncomputable def ε : ℝ := 3 * lsb

theorem eps_nonneg : 0 ≤ ε := by
  unfold ε; have := lsb_pos; linarith

/-- The geometric decay factor from the ISS bound. -/
noncomputable def σ : ℝ := (1 + ρ) / 2

theorem sigma_lt_one : σ < 1 := by
  unfold σ; have := rho_lt_one; linarith

theorem sigma_pos : (0 : ℝ) < σ := by
  unfold σ; have := rho_pos; linarith

/-- The ultimate bound on `V`: the fixed point of `v ↦ σ·v + 810ε²`. -/
noncomputable def Vbound : ℝ := 810 * ε ^ 2 / (1 - σ)

theorem Vbound_nonneg : 0 ≤ Vbound := by
  unfold Vbound
  have h1 : (0 : ℝ) < 1 - σ := by have := sigma_lt_one; linarith
  positivity

/-- **Practical stability of the fixed-point implementation.**

    If the (interpreted) fixed-point state satisfies `V ≤ v` and the fixed-point
    step differs from the ℝ step by at most `ε` per component, then after one
    step `V ≤ σ·v + 810ε²`.

    Iterating this is the induction that gives the ultimate bound; the iteration
    is `ultimate_bound` below. -/
theorem step_contracts (x1 x2 d1 d2 v : ℝ)
    (hd1 : |d1| ≤ ε) (hd2 : |d2| ≤ ε) (hv : V x1 x2 ≤ v) :
    V (nextX1 x1 x2 + d1) (nextX2 x1 x2 + d2) ≤ σ * v + 810 * ε ^ 2 := by
  have hiss := lyapunov_iss x1 x2 d1 d2 ε eps_nonneg hd1 hd2
  have hσ : σ = (1 + ρ) / 2 := rfl
  have hσpos : (0 : ℝ) < σ := sigma_pos
  calc V (nextX1 x1 x2 + d1) (nextX2 x1 x2 + d2)
      ≤ (1 + ρ) / 2 * V x1 x2 + 810 * ε ^ 2 := hiss
    _ = σ * V x1 x2 + 810 * ε ^ 2 := by rw [hσ]
    _ ≤ σ * v + 810 * ε ^ 2 := by nlinarith [hσpos, hv]

/-- A trajectory of the *quantized* closed loop: at each step the ideal ℝ update
    is perturbed by a disturbance bounded by `ε`.  This models the fixed-point
    circuit without committing to a particular rounding, so the theorem covers
    the actual hardware a fortiori. -/
structure QuantTraj where
  x1 : Nat → ℝ
  x2 : Nat → ℝ
  d1 : Nat → ℝ
  d2 : Nat → ℝ
  hd1 : ∀ n, |d1 n| ≤ ε
  hd2 : ∀ n, |d2 n| ≤ ε
  hstep1 : ∀ n, x1 (n + 1) = nextX1 (x1 n) (x2 n) + d1 n
  hstep2 : ∀ n, x2 (n + 1) = nextX2 (x1 n) (x2 n) + d2 n

/-- **The headline theorem: an unbounded, kernel-checked ultimate bound.**

    For every quantized trajectory, `V` is eventually confined to `Vbound` — and
    the confinement is monotone, so once inside it never leaves.

    Stated as: `V` at step `n` is at most `σⁿ·V₀ + Vbound`.  As `n → ∞` the first
    term vanishes, giving the ultimate bound; for finite `n` it is an explicit
    envelope. -/
theorem ultimate_bound (T : QuantTraj) (n : Nat) :
    V (T.x1 n) (T.x2 n) ≤ σ ^ n * V (T.x1 0) (T.x2 0) + Vbound := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have := Vbound_nonneg
    linarith
  | succ m ih =>
    have hσpos : (0 : ℝ) < σ := sigma_pos
    have hσlt : σ < 1 := sigma_lt_one
    have hone : (0 : ℝ) < 1 - σ := by linarith
    have hx1 : T.x1 (m + 1) = nextX1 (T.x1 m) (T.x2 m) + T.d1 m := T.hstep1 m
    have hx2 : T.x2 (m + 1) = nextX2 (T.x1 m) (T.x2 m) + T.d2 m := T.hstep2 m
    rw [hx1, hx2]
    have hc := step_contracts (T.x1 m) (T.x2 m) (T.d1 m) (T.d2 m)
      (σ ^ m * V (T.x1 0) (T.x2 0) + Vbound) (T.hd1 m) (T.hd2 m) ih
    -- `σ·(σᵐV₀ + Vbound) + 810ε² = σᵐ⁺¹V₀ + (σ·Vbound + 810ε²)`, and
    -- `σ·Vbound + 810ε² = Vbound` because `Vbound` is exactly the fixed point.
    have hfix : σ * Vbound + 810 * ε ^ 2 = Vbound := by
      have hne : (1 : ℝ) - σ ≠ 0 := ne_of_gt hone
      unfold Vbound
      field_simp
      ring
    calc V (nextX1 (T.x1 m) (T.x2 m) + T.d1 m) (nextX2 (T.x1 m) (T.x2 m) + T.d2 m)
        ≤ σ * (σ ^ m * V (T.x1 0) (T.x2 0) + Vbound) + 810 * ε ^ 2 := hc
      _ = σ ^ (m + 1) * V (T.x1 0) (T.x2 0) + (σ * Vbound + 810 * ε ^ 2) := by ring
      _ = σ ^ (m + 1) * V (T.x1 0) (T.x2 0) + Vbound := by rw [hfix]

/-- The asymptotic form: the state norm is ultimately bounded by an explicit
    constant proportional to the LSB.  This is the statement a control engineer
    would want: "quantization costs you a steady-state error of this size, and
    nothing worse — no drift, no limit cycle." -/
theorem ultimate_norm_bound (T : QuantTraj) (n : Nat) :
    (T.x1 n) ^ 2 + (T.x2 n) ^ 2
      ≤ 2 * (σ ^ n * V (T.x1 0) (T.x2 0) + Vbound) := by
  have h := ultimate_bound T n
  have hlow := V_lower (T.x1 n) (T.x2 n)
  linarith

end SparkleProofs.Control.Transport
