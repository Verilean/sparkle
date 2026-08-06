/-
  Machine-checked certificates for the two estimators in
  `IP/Control/Observer.lean` — steady-state Kalman and H∞.

  ## What is proven, and why these two theorems are *different in kind*

  Both filters are the same RTL with different gain constants, so what actually
  distinguishes them must be provable *about the gains*.  It is:

  * `kf_contraction` / `hinf_contraction` — both error dynamics
    `e⁺ = (A − KH)e` contract a quadratic `V` at rate `ρ = 0.98`.  This says
    each filter converges when the disturbances are zero.  It does **not**
    distinguish them.

  * `hinf_dissipation` — the H∞ gain additionally satisfies the dissipation
    inequality

        V(e⁺) − V(e) ≤ γ²·(w²/q + v²/r) − ‖e‖²,     γ = 2

    for **all** disturbances `w` (process) and `v` (measurement) — not just
    Gaussian ones, not just small ones.  Summing it over any horizon telescopes
    into `Σ‖e‖² ≤ γ²·Σ(w²/q + v²/r) + V(e₀)`: the energy reaching the estimate
    is at most `γ²` times the (weighted) disturbance energy, whatever the
    disturbance is.  That is the H∞ guarantee, and the Kalman gain does not
    satisfy it at this `γ` — Kalman optimizes the *average* under Gaussian
    assumptions and pays for it in the worst case.

  This is the formal content behind the tutorial's use-case B ("外乱がやたら多い"
  — gusty/adversarial environments): when the disturbance is not the noise you
  modelled, the H∞ certificate still means something and the Kalman optimality
  claim does not.

  ## Where the numbers come from

  Gains and certificate matrices were computed offline (Riccati iterations;
  γ_min ≈ 1.309 by bisection, design at γ = 1.964, certified here at the
  rounder γ = 2) and are *verified*, not derived, in Lean — the same
  guess-and-verify shape as `LQRDesign.lean`.  Every `nlinarith` below is
  handed the rows of an exact rational LDLᵀ decomposition of the certificate's
  Gram matrix, computed in exact arithmetic beforehand — so each proof is a
  sum-of-squares certificate whose existence was established outside Lean and
  whose *validity* is established by the kernel.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SparkleProofs.Control.EstimatorDesign

/-! ### Plant -/

/-- Sample time `dt = 1/16`. -/
noncomputable def dt : ℝ := 1 / 16

/-! ### Steady-state Kalman filter -/

/-- Kalman gain (offline Riccati; `q = 1/32`, `r = 1/100`). -/
noncomputable def kfK1 : ℝ := 4636 / 10000
noncomputable def kfK2 : ℝ := 13960 / 10000

/-- Lyapunov matrix for the Kalman error dynamics (offline discrete-Lyapunov
    solve, rounded to 4 decimals). -/
noncomputable def kfP11 : ℝ := 321755 / 10000
noncomputable def kfP12 : ℝ := -90055 / 10000
noncomputable def kfP22 : ℝ := 43262 / 10000

noncomputable def kfV (e1 e2 : ℝ) : ℝ :=
  kfP11 * e1 ^ 2 + 2 * kfP12 * e1 * e2 + kfP22 * e2 ^ 2

/-- Error dynamics `e⁺ = (A − KH)e` for the Kalman gain. -/
noncomputable def kfNext1 (e1 e2 : ℝ) : ℝ := (1 - kfK1) * e1 + dt * e2
noncomputable def kfNext2 (e1 e2 : ℝ) : ℝ := -kfK2 * e1 + e2

theorem kfP_posdef : (0 : ℝ) < kfP11 ∧ (0 : ℝ) < kfP11 * kfP22 - kfP12 ^ 2 := by
  refine ⟨by norm_num [kfP11], by norm_num [kfP11, kfP22, kfP12]⟩

/-- **Kalman error contraction**: `V(e⁺) ≤ 0.98·V(e)`.  True worst-case ratio
    0.97129, so the certificate has slack. -/
theorem kf_contraction (e1 e2 : ℝ) :
    kfV (kfNext1 e1 e2) (kfNext2 e1 e2) ≤ (98 / 100) * kfV e1 e2 := by
  unfold kfV kfNext1 kfNext2 kfP11 kfP12 kfP22 kfK1 kfK2 dt
  -- SOS hint: LDLᵀ of `ρP − AᵀPA` has rows (e1 + 0.5053·e2) and e2,
  -- pivots 0.3564 and 0.8225.
  nlinarith [sq_nonneg (e1 + (5053 / 10000) * e2), sq_nonneg e2,
    sq_nonneg (e1 + e2), sq_nonneg (e1 - e2)]

/-! ### H∞ filter -/

/-- H∞ gain (offline H∞ Riccati at design γ = 1.964; γ_min ≈ 1.309). -/
noncomputable def hiK1 : ℝ := 4974 / 10000
noncomputable def hiK2 : ℝ := 15472 / 10000

/-- Lyapunov matrix for the H∞ error dynamics. -/
noncomputable def hiP11 : ℝ := 334620 / 10000
noncomputable def hiP12 : ℝ := -90457 / 10000
noncomputable def hiP22 : ℝ := 41528 / 10000

noncomputable def hiV (e1 e2 : ℝ) : ℝ :=
  hiP11 * e1 ^ 2 + 2 * hiP12 * e1 * e2 + hiP22 * e2 ^ 2

noncomputable def hiNext1 (e1 e2 : ℝ) : ℝ := (1 - hiK1) * e1 + dt * e2
noncomputable def hiNext2 (e1 e2 : ℝ) : ℝ := -hiK2 * e1 + e2

theorem hiP_posdef : (0 : ℝ) < hiP11 ∧ (0 : ℝ) < hiP11 * hiP22 - hiP12 ^ 2 := by
  refine ⟨by norm_num [hiP11], by norm_num [hiP11, hiP22, hiP12]⟩

/-- **H∞ error contraction**: same statement as the Kalman one — this is the
    part the two filters share.  True worst-case ratio 0.97225. -/
theorem hinf_contraction (e1 e2 : ℝ) :
    hiV (hiNext1 e1 e2) (hiNext2 e1 e2) ≤ (98 / 100) * hiV e1 e2 := by
  unfold hiV hiNext1 hiNext2 hiP11 hiP12 hiP22 hiK1 hiK2 dt
  nlinarith [sq_nonneg (e1 + (5472 / 10000) * e2), sq_nonneg e2,
    sq_nonneg (e1 + e2), sq_nonneg (e1 - e2)]

/-! ### The dissipation inequality — what only the H∞ gain provides -/

/-- Storage function: `γ²·P⁻¹` of the H∞ design Riccati, rounded to 4 decimals.
    (The design `P`, not the Lyapunov `P` above — the storage that certifies
    dissipation comes from the game-theoretic Riccati itself.) -/
noncomputable def sP11 : ℝ := 12452067 / 10000
noncomputable def sP12 : ℝ := -1728567 / 10000
noncomputable def sP22 : ℝ := 457700 / 10000

noncomputable def sV (e1 e2 : ℝ) : ℝ :=
  sP11 * e1 ^ 2 + 2 * sP12 * e1 * e2 + sP22 * e2 ^ 2

/-- Full disturbed error dynamics: `e⁺ = (A−KH)e + Gw − Kv` with `G = [0;1]`. -/
noncomputable def hiNextW1 (e1 e2 _w v : ℝ) : ℝ := (1 - hiK1) * e1 + dt * e2 - hiK1 * v
noncomputable def hiNextW2 (e1 e2 w v : ℝ) : ℝ := -hiK2 * e1 + e2 + w - hiK2 * v

/-- **The H∞ dissipation inequality**, certified at `γ = 2` with the weighted
    supply `γ²(w²/q + v²/r) = 128·w² + 400·v²` (`q = 1/32`, `r = 1/100`):

        V(e⁺) − V(e) ≤ 128·w² + 400·v² − ‖e‖²    for ALL e, w, v.

    Telescoping over any horizon gives `Σ‖e‖² ≤ 4·Σ(32w² + 100v²) + V(e₀)` —
    a worst-case energy gain bound needing no distributional assumption
    whatsoever.  This is the theorem that separates the H∞ gain from the
    Kalman gain; it is false for the Kalman gain at this `γ`.

    Proof: the Gram matrix of the difference is negative semidefinite; the
    `nlinarith` hints are the rows of its exact rational LDLᵀ (pivots 551.3,
    6.60, 4.57, 14.27 — comfortably interior). -/
theorem hinf_dissipation (e1 e2 w v : ℝ) :
    sV (hiNextW1 e1 e2 w v) (hiNextW2 e1 e2 w v) - sV e1 e2
      ≤ 128 * w ^ 2 + 400 * v ^ 2 - (e1 ^ 2 + e2 ^ 2) := by
  unfold sV hiNextW1 hiNextW2 sP11 sP12 sP22 hiK1 hiK2 dt
  nlinarith [sq_nonneg (e1 - (1288 / 10000) * e2 + (2861 / 10000) * w + (3634 / 10000) * v),
    sq_nonneg (e2 - (22209 / 10000) * w + (49442 / 10000) * v),
    sq_nonneg (w - (1 / 10000) * v),
    sq_nonneg v, sq_nonneg w,
    sq_nonneg (e1 + e2), sq_nonneg (e1 - e2)]

/-- The storage is positive semidefinite (Sylvester: `1245.2·45.77 > 172.86²`). -/
theorem sV_nonneg (e1 e2 : ℝ) : 0 ≤ sV e1 e2 := by
  unfold sV sP11 sP12 sP22
  nlinarith [sq_nonneg (e1 + e2), sq_nonneg (e1 - e2), sq_nonneg e1, sq_nonneg e2,
    sq_nonneg ((1388 / 10000) * e1 - e2)]

/-- The storage-augmented invariant — the standard dissipation argument:
    telescoping `hinf_dissipation` over the horizon. -/
theorem hinf_energy_invariant
    (e1 e2 w v : ℕ → ℝ)
    (hstep1 : ∀ n, e1 (n + 1) = hiNextW1 (e1 n) (e2 n) (w n) (v n))
    (hstep2 : ∀ n, e2 (n + 1) = hiNextW2 (e1 n) (e2 n) (w n) (v n))
    (N : ℕ) :
    (Finset.range N).sum (fun n => (e1 n) ^ 2 + (e2 n) ^ 2) + sV (e1 N) (e2 N)
      ≤ (Finset.range N).sum (fun n => 128 * (w n) ^ 2 + 400 * (v n) ^ 2)
        + sV (e1 0) (e2 0) := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hd := hinf_dissipation (e1 M) (e2 M) (w M) (v M)
    rw [← hstep1 M, ← hstep2 M] at hd
    linarith

/-- **The telescoped H∞ guarantee**: over any horizon, the accumulated
    estimation-error energy is at most `γ² = 4` times the accumulated weighted
    disturbance energy, plus the initial storage.  No distributional assumption
    on `w`, `v` — this is a worst-case bound, and it is exactly what the
    "disturbance-heavy" use case needs from its estimator. -/
theorem hinf_energy_bound
    (e1 e2 w v : ℕ → ℝ)
    (hstep1 : ∀ n, e1 (n + 1) = hiNextW1 (e1 n) (e2 n) (w n) (v n))
    (hstep2 : ∀ n, e2 (n + 1) = hiNextW2 (e1 n) (e2 n) (w n) (v n))
    (N : ℕ) :
    (Finset.range N).sum (fun n => (e1 n) ^ 2 + (e2 n) ^ 2)
      ≤ (Finset.range N).sum (fun n => 128 * (w n) ^ 2 + 400 * (v n) ^ 2)
        + sV (e1 0) (e2 0) := by
  have h := hinf_energy_invariant e1 e2 w v hstep1 hstep2 N
  have hnn := sV_nonneg (e1 N) (e2 N)
  linarith

end SparkleProofs.Control.EstimatorDesign
