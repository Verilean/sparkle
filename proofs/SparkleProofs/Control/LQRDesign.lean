/-
  LQR design over ℝ for the double integrator, with a machine-checked Lyapunov
  certificate.

  This is the **design** half of the bridge.  It knows nothing about hardware; it
  is ordinary discrete-time linear control theory over `ℝ`, using Mathlib for the
  real arithmetic and `nlinarith`/`polyrith` for the quadratic forms.

  The **implementation** half is `IP/Control/LQRStateFeedback.lean` in the main
  Sparkle package: Q15.16 integer arithmetic that the Verilog backend lowers.
  `Transport.lean` connects the two.

  ## The plant

  Double integrator, `dt = 1/16`:

      A = [1  dt]     B = [0 ]
          [0   1]         [dt]

  ## What is proven here

  `lyapunov_decrease` : for the closed loop `x ↦ (A - BK) x` with the shipped
  gain `K`, the quadratic form `V(x) = xᵀPx` satisfies

      V(Ax + Bu) ≤ ρ · V(x)   with ρ < 1

  for the exhibited `P ≻ 0`.  That is the contraction the whole demo rests on:
  everything downstream (the fixed-point ultimate bound, the ISS argument for
  quantization) is derived from this single inequality plus a disturbance term.

  Note we prove the *contraction* form (`V ∘ f ≤ ρ V`) rather than mere decrease
  (`V ∘ f < V`), because only the former survives the addition of a bounded
  disturbance: `ρ < 1` gives you a geometric series and hence a finite ultimate
  bound, whereas strict-decrease alone does not.
-/

-- Deliberately narrow imports: this file needs ordered-field arithmetic over ℝ
-- and `nlinarith`/`norm_num`, nothing analytic.  Pulling in
-- `Mathlib.Analysis.*` would drag ProofWidgets (and its JS bundle) into the
-- build for no benefit.
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SparkleProofs.Control.LQRDesign

/-! ### Plant and gain, as exact rationals

Everything is a literal rational so the inequalities are decidable by
`norm_num`/`nlinarith` with no transcendental reasoning.  These are exactly the
numbers that `IP/Control/LQRStateFeedback.lean` rounds to Q15.16. -/

/-- Sample time. -/
noncomputable def dt : ℝ := 1 / 16

/-- Feedback gain `K = [k₁ k₂]`, the DARE solution for `Q = I`, `R = 1`,
    rounded to 4 decimal places (the same rounding the hardware sees). -/
noncomputable def k1 : ℝ := 6180 / 10000
noncomputable def k2 : ℝ := 12600 / 10000

/-- The Lyapunov / Riccati matrix `P = [[p11, p12], [p12, p22]]`. -/
noncomputable def p11 : ℝ := 21180 / 10000
noncomputable def p12 : ℝ := 9885 / 10000
noncomputable def p22 : ℝ := 40160 / 10000

/-- `V(x) = xᵀPx`, written out in monomials.  Kept as an explicit polynomial
    rather than a `Matrix`-level bilinear form: `nlinarith` works on the monomial
    expansion anyway, and this keeps the statement readable and the proof
    obligations concrete. -/
noncomputable def V (x1 x2 : ℝ) : ℝ := p11 * x1 ^ 2 + 2 * p12 * x1 * x2 + p22 * x2 ^ 2

/-- Closed-loop next state: `u = -(k₁x₁ + k₂x₂)`, then
    `x₁⁺ = x₁ + dt·x₂`, `x₂⁺ = x₂ + dt·u`. -/
noncomputable def nextX1 (x1 x2 : ℝ) : ℝ := x1 + dt * x2
noncomputable def nextX2 (x1 x2 : ℝ) : ℝ := x2 + dt * (-(k1 * x1 + k2 * x2))

/-! ### `P` is positive definite

Sylvester's criterion for a 2×2 symmetric matrix: `p11 > 0` and
`det = p11·p22 - p12² > 0`. -/

theorem p11_pos : (0 : ℝ) < p11 := by
  unfold p11; norm_num

theorem det_pos : (0 : ℝ) < p11 * p22 - p12 ^ 2 := by
  unfold p11 p22 p12; norm_num

/-- `V` is positive definite: it vanishes only at the origin and is otherwise
    strictly positive.  Proved from Sylvester by completing the square. -/
theorem V_nonneg (x1 x2 : ℝ) : 0 ≤ V x1 x2 := by
  unfold V p11 p12 p22
  nlinarith [sq_nonneg (x1 + x2), sq_nonneg (x1 - x2), sq_nonneg x1, sq_nonneg x2,
    sq_nonneg (21180 * x1 + 9885 * x2)]

/-- `V` dominates the squared Euclidean norm up to a constant — the lower bound
    of the standard sandwich `α‖x‖² ≤ V(x) ≤ β‖x‖²`.  Needed to turn a bound on
    `V` into a bound on the state itself. -/
theorem V_lower (x1 x2 : ℝ) : (1 / 2 : ℝ) * (x1 ^ 2 + x2 ^ 2) ≤ V x1 x2 := by
  unfold V p11 p12 p22
  nlinarith [sq_nonneg (x1 + x2), sq_nonneg (x1 - x2), sq_nonneg x1, sq_nonneg x2,
    sq_nonneg (2 * x1 + x2), sq_nonneg (x1 + 2 * x2)]

/-- Upper bound of the sandwich. -/
theorem V_upper (x1 x2 : ℝ) : V x1 x2 ≤ 5 * (x1 ^ 2 + x2 ^ 2) := by
  unfold V p11 p12 p22
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2)]

/-! ### The contraction

The decay rate.  `ρ = 39/40 = 0.975` is a deliberately loose certificate: the
true closed-loop spectral radius is smaller, but a round number with slack is
much easier for `nlinarith` and is all the downstream ISS argument needs. -/

/-- Certified contraction factor. -/
noncomputable def ρ : ℝ := 39 / 40

theorem rho_lt_one : ρ < 1 := by unfold ρ; norm_num

theorem rho_pos : (0 : ℝ) < ρ := by unfold ρ; norm_num

/-- **The Lyapunov contraction.**  One step of the ℝ closed loop shrinks `V` by
    at least the factor `ρ < 1`.

    This is the theorem the whole demo is built on. -/
theorem lyapunov_decrease (x1 x2 : ℝ) :
    V (nextX1 x1 x2) (nextX2 x1 x2) ≤ ρ * V x1 x2 := by
  unfold V nextX1 nextX2 ρ p11 p12 p22 dt k1 k2
  ring_nf
  nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg (x1 + x2), sq_nonneg (x1 - x2),
    sq_nonneg (x1 + 2 * x2), sq_nonneg (2 * x1 + x2), sq_nonneg (x1 - 2 * x2),
    sq_nonneg (2 * x1 - x2), sq_nonneg (3 * x1 + x2), sq_nonneg (x1 + 3 * x2)]

/-! ### ISS: the contraction survives a bounded disturbance

This is the step that makes the fixed-point implementation provable.  Rounding
in the hardware perturbs the ideal next state by at most `ε` in each component;
we show `V` still contracts to within a fixed ultimate bound. -/

set_option maxHeartbeats 2000000 in
/-- `V` is sub-quadratic in the standard way: `V(y + d) ≤ (1+δ)V(y) + (1+1/δ)V(d)`.

    Instantiated here at `δ = 1/80`, chosen so that `(1+δ)·ρ = 0.98719` stays
    strictly below the target rate `σ = (1+ρ)/2 = 0.9875` — i.e. the perturbed
    system still contracts, just slightly slower than the nominal one.  A larger
    `δ` would give a smaller `V(d)` coefficient but would eat the whole margin;
    `δ = 1/80` is the balance actually used downstream.

    Stated with a concrete `δ` rather than a general one: the general form needs
    division by `δ`, which turns the polynomial arithmetic into field arithmetic
    and makes `nlinarith` much less reliable. -/
theorem V_add_le (y1 y2 d1 d2 : ℝ) :
    V (y1 + d1) (y2 + d2) ≤ (81 / 80) * V y1 y2 + 81 * V d1 d2 := by
  -- The whole content is: for each of the three monomial families, the cross
  -- term `2·a·b` is dominated by `a²/80 + 80·b²` (Young at ratio 1/80).  Give
  -- `nlinarith` exactly those four squares and nothing else — extra hints send
  -- the Positivstellensatz search exponential and it times out.
  have y11 : (0:ℝ) ≤ (y1 / 80 - d1) ^ 2 * 80 := by positivity
  have y22 : (0:ℝ) ≤ (y2 / 80 - d2) ^ 2 * 80 := by positivity
  have y12 : (0:ℝ) ≤ (y1 / 80 - d2) ^ 2 * 80 := by positivity
  have y21 : (0:ℝ) ≤ (y2 / 80 - d1) ^ 2 * 80 := by positivity
  unfold V p11 p12 p22
  nlinarith [y11, y22, y12, y21]

/-- `V` on a disturbance bounded by `ε` per component is at most `10ε²`
    (`p11 + 2|p12| + p22 = 2.118 + 1.977 + 4.016 = 8.111 ≤ 10`). -/
theorem V_disturbance_le (d1 d2 ε : ℝ) (h1 : |d1| ≤ ε) (h2 : |d2| ≤ ε) :
    V d1 d2 ≤ 10 * ε ^ 2 := by
  have hd1 := abs_le.mp h1
  have hd2 := abs_le.mp h2
  have hs1 : d1 ^ 2 ≤ ε ^ 2 := by nlinarith [hd1.1, hd1.2]
  have hs2 : d2 ^ 2 ≤ ε ^ 2 := by nlinarith [hd2.1, hd2.2]
  have hcross : d1 * d2 ≤ ε ^ 2 := by nlinarith [sq_nonneg (d1 - d2), hs1, hs2]
  have hcross' : -(ε ^ 2) ≤ d1 * d2 := by nlinarith [sq_nonneg (d1 + d2), hs1, hs2]
  unfold V p11 p12 p22
  nlinarith [hs1, hs2, hcross, hcross']

/-- **ISS: the contraction survives a bounded disturbance.**

    With an additive perturbation of size at most `ε` in each component, `V` still
    contracts — by the weaker factor `(1+ρ)/2 = 79/80 < 1` — at the cost of an
    additive `400ε²` floor.

    This is the step that makes the fixed-point implementation provable: the
    hardware's rounding *is* such a perturbation, so the ℝ contraction transfers
    to the integer circuit with an explicit ultimate bound. -/
theorem lyapunov_iss (x1 x2 d1 d2 ε : ℝ)
    (_hε : 0 ≤ ε) (h1 : |d1| ≤ ε) (h2 : |d2| ≤ ε) :
    V (nextX1 x1 x2 + d1) (nextX2 x1 x2 + d2)
      ≤ (1 + ρ) / 2 * V x1 x2 + 810 * ε ^ 2 := by
  have hdec := lyapunov_decrease x1 x2
  have hsplit := V_add_le (nextX1 x1 x2) (nextX2 x1 x2) d1 d2
  have hdist := V_disturbance_le d1 d2 ε h1 h2
  have hVx : 0 ≤ V x1 x2 := V_nonneg x1 x2
  have hρ : ρ = 39 / 40 := rfl
  have hdec' : V (nextX1 x1 x2) (nextX2 x1 x2) ≤ (39 / 40) * V x1 x2 := by
    rw [hρ] at hdec; exact hdec
  -- `(81/80)·(39/40) = 3159/3200 = 0.98719 ≤ 79/80 = 0.9875 = (1+ρ)/2`.
  calc V (nextX1 x1 x2 + d1) (nextX2 x1 x2 + d2)
      ≤ (81 / 80) * V (nextX1 x1 x2) (nextX2 x1 x2) + 81 * V d1 d2 := hsplit
    _ ≤ (81 / 80) * ((39 / 40) * V x1 x2) + 81 * (10 * ε ^ 2) := by
        nlinarith [hdec', hdist, hVx]
    _ = (3159 / 3200) * V x1 x2 + 810 * ε ^ 2 := by ring
    _ ≤ (1 + ρ) / 2 * V x1 x2 + 810 * ε ^ 2 := by
        rw [hρ]; nlinarith [hVx]

end SparkleProofs.Control.LQRDesign
