/-
  The H∞ estimator, transported to fixed point.

  ## What this is

  `EstimatorDesign.lean` proves two things about the H∞ observer over ℝ: an
  error contraction (`hinf_contraction`, ρ = 0.98) and the dissipation
  inequality that only the H∞ gain provides (`hinf_dissipation`).  Neither
  said anything about the Q15.16 circuit.

  This file does for H∞ what `Transport.lean` + `QuantizedGains.lean` +
  `StepError.lean` did for the LQR loop: certify the gains the hardware
  actually holds, carry the contraction through a bounded per-step error, and
  land an ultimate bound.  §12.10 listed it as "follows the same ISS pattern
  but is not written"; it is written now.

  ## Two places H∞ differs from the LQR transport

  **1. The Young split had to change.**  `LQRDesign.V_add_le` uses ratio
  1/80, giving `V(y+d) ≤ (81/80)·V(y) + 81·V(d)`.  That is fine when
  ρ = 39/40: `(81/80)·(39/40) = 0.98719 ≤ 0.9875 = (1+ρ)/2`.  For the H∞
  filter ρ = 0.98, and `(81/80)·0.98 = 0.99225 > 0.99` — the same split does
  not close.  Ratio 1/100 does: `(101/100)·0.98 = 0.9898 ≤ 0.99`.

  Generally the identity is

      V(y/n − d)·n ≥ 0   ⟹   V(y+d) ≤ (1+1/n)·V(y) + (1+n)·V(d)

  so the pair is `(1+1/n, 1+n)` — here `(101/100, 101)`.  Getting that
  constant wrong is the whole difficulty: with `C = 500` the statement is
  still TRUE but `nlinarith` cannot find it, because the coordinate-wise
  Young squares LQR uses are not a witness for it.  The witness is the single
  `P`-norm square `V(y/100 − d) ≥ 0`.

  **2. The disturbance constant is bigger.**  `hiP11 + 2|hiP12| + hiP22 =
  33.462 + 18.091 + 4.153 = 55.71`, against 8.11 for the LQR `P`.  So
  `hiV(d) ≤ 56ε²` where the LQR bound was `10ε²`, and the ISS residual is
  `101 · 56 = 5656 ε²` rather than 810ε².  That is not a defect — `hiV` is
  simply scaled differently — but it means the H∞ ultimate bound is NOT
  comparable to the LQR one term by term.

  ## The quantized gains

      hiK1 = 0.4974  →  32598 / 65536 = 0.497406…
      hiK2 = 1.5472  →  101397 / 65536 = 1.547195…

  Worst-case contraction ratio (exact rationals): nominal 0.97224763,
  quantized 0.97223470, against the certified ρ = 0.98.  Same `P`, same ρ —
  the slack absorbs the rounding, exactly as in `QuantizedGains.lean`.
-/

import SparkleProofs.Control.EstimatorDesign
import SparkleProofs.Control.Transport

namespace SparkleProofs.Control.HinfTransport

open SparkleProofs.Control.EstimatorDesign
open SparkleProofs.Control.Transport

/-! ### The gains as the circuit holds them -/

/-- `hiK1 = 0.4974` after Q15.16 rounding. -/
noncomputable def hiK1q : ℝ := 32598 / 65536

/-- `hiK2 = 1.5472` after Q15.16 rounding. -/
noncomputable def hiK2q : ℝ := 101397 / 65536

noncomputable def hiNext1q (e1 e2 : ℝ) : ℝ := (1 - hiK1q) * e1 + dt * e2
noncomputable def hiNext2q (e1 e2 : ℝ) : ℝ := -hiK2q * e1 + e2

/-! ### Contraction survives quantizing the gains -/

/-- **H∞ error contraction with the implemented gains.**  Same `hiV`, same
    `P`, same ρ = 0.98 as `hinf_contraction`.  The hint is the LDLᵀ row of
    `ρP − AqᵀPAq` (pivots 0.331 / 0.818). -/
theorem hinf_contraction_q (e1 e2 : ℝ) :
    hiV (hiNext1q e1 e2) (hiNext2q e1 e2) ≤ (98 / 100) * hiV e1 e2 := by
  unfold hiV hiNext1q hiNext2q hiP11 hiP12 hiP22 hiK1q hiK2q dt
  nlinarith [sq_nonneg (e1 + (5462870819 / 10000000000) * e2), sq_nonneg e2,
    sq_nonneg (e1 + e2), sq_nonneg (e1 - e2)]

/-! ### ISS building blocks for `hiV`

`LQRDesign`'s versions are specific to its own `V`; these are the `hiV`
analogues, with the constants recomputed (see the header). -/

theorem hiV_nonneg (e1 e2 : ℝ) : 0 ≤ hiV e1 e2 := by
  unfold hiV hiP11 hiP12 hiP22
  nlinarith [sq_nonneg e1, sq_nonneg e2, sq_nonneg (e1 - e2), sq_nonneg (e1 + e2)]

/-- Young at ratio 1/100.  The witness is the single `P`-norm square
    `hiV (y/100 − d) ≥ 0`, not four coordinate-wise squares — see the header
    on why the LQR-style hints fail here. -/
theorem hiV_add_le (y1 y2 d1 d2 : ℝ) :
    hiV (y1 + d1) (y2 + d2) ≤ (101 / 100) * hiV y1 y2 + 101 * hiV d1 d2 := by
  have key : (0:ℝ) ≤ hiV (y1 / 100 - d1) (y2 / 100 - d2) * 100 := by
    have h := hiV_nonneg (y1 / 100 - d1) (y2 / 100 - d2)
    linarith
  unfold hiV hiP11 hiP12 hiP22 at *
  nlinarith [key]

/-- `hiV` on an ε-bounded disturbance: `hiP11 + 2|hiP12| + hiP22 = 55.71 ≤ 56`. -/
theorem hiV_disturbance_le (d1 d2 ε : ℝ) (h1 : |d1| ≤ ε) (h2 : |d2| ≤ ε) :
    hiV d1 d2 ≤ 56 * ε ^ 2 := by
  have hd1 := abs_le.mp h1
  have hd2 := abs_le.mp h2
  have hs1 : d1 ^ 2 ≤ ε ^ 2 := by nlinarith [hd1.1, hd1.2]
  have hs2 : d2 ^ 2 ≤ ε ^ 2 := by nlinarith [hd2.1, hd2.2]
  have hcross : d1 * d2 ≤ ε ^ 2 := by nlinarith [sq_nonneg (d1 - d2), hs1, hs2]
  have hcross' : -(ε ^ 2) ≤ d1 * d2 := by nlinarith [sq_nonneg (d1 + d2), hs1, hs2]
  unfold hiV hiP11 hiP12 hiP22
  nlinarith [hs1, hs2, hcross, hcross']

/-! ### ISS and the ultimate bound -/

/-- The H∞ decay factor: `(1 + 0.98)/2 = 0.99`. -/
noncomputable def hσ : ℝ := 99 / 100

theorem hsigma_pos : (0:ℝ) < hσ := by unfold hσ; norm_num
theorem hsigma_lt_one : hσ < 1 := by unfold hσ; norm_num

/-- **ISS for the quantized-gain H∞ error dynamics.** -/
theorem hinf_iss_q (e1 e2 d1 d2 ε : ℝ)
    (_hε : 0 ≤ ε) (h1 : |d1| ≤ ε) (h2 : |d2| ≤ ε) :
    hiV (hiNext1q e1 e2 + d1) (hiNext2q e1 e2 + d2)
      ≤ hσ * hiV e1 e2 + 5656 * ε ^ 2 := by
  have hdec := hinf_contraction_q e1 e2
  have hsplit := hiV_add_le (hiNext1q e1 e2) (hiNext2q e1 e2) d1 d2
  have hdist := hiV_disturbance_le d1 d2 ε h1 h2
  have hVx : 0 ≤ hiV e1 e2 := hiV_nonneg e1 e2
  calc hiV (hiNext1q e1 e2 + d1) (hiNext2q e1 e2 + d2)
      ≤ (101 / 100) * hiV (hiNext1q e1 e2) (hiNext2q e1 e2)
        + 101 * hiV d1 d2 := hsplit
    _ ≤ (101 / 100) * ((98 / 100) * hiV e1 e2) + 101 * (56 * ε ^ 2) := by
        nlinarith [hdec, hdist, hVx]
    _ = (9898 / 10000) * hiV e1 e2 + 5656 * ε ^ 2 := by ring
    _ ≤ hσ * hiV e1 e2 + 5656 * ε ^ 2 := by
        unfold hσ; nlinarith [hVx]

/-- The ultimate bound's fixed point: `hσ·B + 5656ε² = B`. -/
noncomputable def hVbound : ℝ := 5656 * ε ^ 2 / (1 - hσ)

theorem hVbound_nonneg : 0 ≤ hVbound := by
  unfold hVbound
  have h1 : (0:ℝ) < 1 - hσ := by have := hsigma_lt_one; linarith
  positivity

/-- A trajectory of the quantized-gain H∞ error dynamics under bounded
    per-step quantization error. -/
structure HinfTraj where
  e1 : Nat → ℝ
  e2 : Nat → ℝ
  d1 : Nat → ℝ
  d2 : Nat → ℝ
  hd1 : ∀ n, |d1 n| ≤ ε
  hd2 : ∀ n, |d2 n| ≤ ε
  hstep1 : ∀ n, e1 (n + 1) = hiNext1q (e1 n) (e2 n) + d1 n
  hstep2 : ∀ n, e2 (n + 1) = hiNext2q (e1 n) (e2 n) + d2 n

/-- **The H∞ ultimate bound, for the circuit's gains and the circuit's
    rounding.**  The estimator analogue of `Transport.ultimate_bound`. -/
theorem hinf_ultimate_bound (T : HinfTraj) (n : Nat) :
    hiV (T.e1 n) (T.e2 n) ≤ hσ ^ n * hiV (T.e1 0) (T.e2 0) + hVbound := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have := hVbound_nonneg
    linarith
  | succ m ih =>
    have hσpos := hsigma_pos
    have hσlt := hsigma_lt_one
    have hone : (0:ℝ) < 1 - hσ := by linarith
    have hx1 : T.e1 (m + 1) = hiNext1q (T.e1 m) (T.e2 m) + T.d1 m := T.hstep1 m
    have hx2 : T.e2 (m + 1) = hiNext2q (T.e1 m) (T.e2 m) + T.d2 m := T.hstep2 m
    rw [hx1, hx2]
    have hiss := hinf_iss_q (T.e1 m) (T.e2 m) (T.d1 m) (T.d2 m) ε
      eps_nonneg (T.hd1 m) (T.hd2 m)
    have hfix : hσ * hVbound + 5656 * ε ^ 2 = hVbound := by
      have hne : (1:ℝ) - hσ ≠ 0 := ne_of_gt hone
      unfold hVbound
      field_simp
      ring
    calc hiV (hiNext1q (T.e1 m) (T.e2 m) + T.d1 m) (hiNext2q (T.e1 m) (T.e2 m) + T.d2 m)
        ≤ hσ * hiV (T.e1 m) (T.e2 m) + 5656 * ε ^ 2 := hiss
      _ ≤ hσ * (hσ ^ m * hiV (T.e1 0) (T.e2 0) + hVbound) + 5656 * ε ^ 2 := by
          nlinarith [ih, hσpos]
      _ = hσ ^ (m + 1) * hiV (T.e1 0) (T.e2 0) + (hσ * hVbound + 5656 * ε ^ 2) := by
          ring
      _ = hσ ^ (m + 1) * hiV (T.e1 0) (T.e2 0) + hVbound := by rw [hfix]

end SparkleProofs.Control.HinfTransport
