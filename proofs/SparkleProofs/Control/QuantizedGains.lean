/-
  The certificate re-derived for the gains the circuit ACTUALLY holds.

  ## The gap this closes

  `LQRDesign.lean` certifies the nominal design: `k1 = 0.6180`,
  `k2 = 1.2600`.  The circuit cannot hold those numbers.  It holds their
  Q15.16 roundings:

      k1 = 0.6180  →  40501 / 65536 = 0.617996…   (0.248 lsb low)
      k2 = 1.2600  →  82575 / 65536 = 1.259994…   (0.360 lsb low)

  `StepError.stepX2_err` therefore had to state its bound against the ℝ
  update *using the quantized gains*, and §12.10 listed the difference as
  open.  It could not be folded into the per-step ε: a gain error multiplies
  the STATE, so its contribution grows with `|x|` and is not a constant
  number of LSBs.

  The fix is not a tighter ε.  It is to certify the system the hardware
  implements — this file.

  ## It works, and not by luck

  The measured worst-case ratio for the quantized-gain closed loop is
  **0.97178930**, against the certified ρ = 39/40 = 0.975.  The nominal
  system measures 0.97178926 — quantizing the gains moved the true
  contraction rate by 3.7·10⁻⁸, far inside the certificate's slack.

  That is the practical argument for choosing a *round* ρ above the measured
  ratio rather than the tightest one that closes (`LQRDesign`'s step 2): the
  slack is what lets an implementation detail change the plant slightly
  without invalidating the proof.  A ρ pinned at 0.9717893 would have needed
  a fresh `P` here.

  So the SAME `P` from `LQRDesign` is reused, and the hint below is the exact
  rational LDLᵀ of `ρP − AqᵀPAq`, with pivots 0.01742 and 0.13471 — both
  comfortably positive, so the matrix is PSD and the LDLᵀ row is a
  sum-of-squares witness.
-/

import SparkleProofs.Control.LQRDesign
import SparkleProofs.Control.Transport

namespace SparkleProofs.Control.QuantizedGains

open SparkleProofs.Control.LQRDesign SparkleProofs.Control.Transport

/-! ### The gains as the circuit holds them -/

/-- `k1` after Q15.16 rounding: `⌊0.6180 · 2¹⁶⌋ = 40501`. -/
noncomputable def k1q : ℝ := 40501 / 65536

/-- `k2` after Q15.16 rounding: `⌊1.2600 · 2¹⁶⌋ = 82575`. -/
noncomputable def k2q : ℝ := 82575 / 65536

/-- `x1⁺ = x1 + dt·x2` — unchanged, since `dt = 1/16` is dyadic and survives
    quantization exactly (`StepError.toR_dtQ`). -/
noncomputable def nextX1q (x1 x2 : ℝ) : ℝ := x1 + dt * x2

/-- `x2⁺ = x2 + dt·(−(k1q·x1 + k2q·x2))` — the quantized gains. -/
noncomputable def nextX2q (x1 x2 : ℝ) : ℝ := x2 + dt * (-(k1q * x1 + k2q * x2))

/-! ### The contraction, for the implemented system -/

/-- **The quantized-gain closed loop contracts at the same rate.**

    Same `V`, same `P`, same ρ = 39/40 as `LQRDesign.lyapunov_decrease` —
    only the gains differ.  The `nlinarith` hint is the LDLᵀ row of
    `ρP − AqᵀPAq` (`x1 + 3.79134·x2`, pivots 0.01742 / 0.13471). -/
theorem lyapunov_decrease_q (x1 x2 : ℝ) :
    V (nextX1q x1 x2) (nextX2q x1 x2) ≤ ρ * V x1 x2 := by
  unfold V nextX1q nextX2q k1q k2q dt ρ p11 p12 p22
  nlinarith [sq_nonneg (x1 + (3791344616 / 1000000000) * x2),
             sq_nonneg x1, sq_nonneg x2, sq_nonneg (x1 + x2), sq_nonneg (x1 - x2)]

/-- **ISS for the implemented system.**

    Identical in shape to `LQRDesign.lyapunov_iss`, and deliberately built
    from the same two system-independent lemmas (`V_add_le`,
    `V_disturbance_le`) — only `lyapunov_decrease_q` is swapped in.  That is
    the point: the ISS argument never depended on which gains were used, only
    on the contraction, so re-certifying the gains is all that was needed. -/
theorem lyapunov_iss_q (x1 x2 d1 d2 ε : ℝ)
    (_hε : 0 ≤ ε) (h1 : |d1| ≤ ε) (h2 : |d2| ≤ ε) :
    V (nextX1q x1 x2 + d1) (nextX2q x1 x2 + d2)
      ≤ (1 + ρ) / 2 * V x1 x2 + 810 * ε ^ 2 := by
  have hdec := lyapunov_decrease_q x1 x2
  have hsplit := V_add_le (nextX1q x1 x2) (nextX2q x1 x2) d1 d2
  have hdist := V_disturbance_le d1 d2 ε h1 h2
  have hVx : 0 ≤ V x1 x2 := V_nonneg x1 x2
  have hρ : ρ = 39 / 40 := rfl
  have hdec' : V (nextX1q x1 x2) (nextX2q x1 x2) ≤ (39 / 40) * V x1 x2 := by
    rw [hρ] at hdec; exact hdec
  calc V (nextX1q x1 x2 + d1) (nextX2q x1 x2 + d2)
      ≤ (81 / 80) * V (nextX1q x1 x2) (nextX2q x1 x2) + 81 * V d1 d2 := hsplit
    _ ≤ (81 / 80) * ((39 / 40) * V x1 x2) + 81 * (10 * ε ^ 2) := by
        nlinarith [hdec', hdist, hVx]
    _ = (3159 / 3200) * V x1 x2 + 810 * ε ^ 2 := by ring
    _ ≤ (1 + ρ) / 2 * V x1 x2 + 810 * ε ^ 2 := by
        rw [hρ]; nlinarith [hVx]

/-! ### The ultimate bound, for the implemented system

Everything below mirrors `Transport.lean` with `lyapunov_iss_q` swapped for
`lyapunov_iss`.  The structure is identical because the ISS-to-envelope
argument never mentioned the gains. -/

/-- One step of the quantized-gain loop, with bounded disturbance, shrinks `V`
    toward the fixed point. -/
theorem step_contracts_q (x1 x2 d1 d2 v : ℝ)
    (hd1 : |d1| ≤ ε) (hd2 : |d2| ≤ ε) (hv : V x1 x2 ≤ v) :
    V (nextX1q x1 x2 + d1) (nextX2q x1 x2 + d2) ≤ σ * v + 810 * ε ^ 2 := by
  have hiss := lyapunov_iss_q x1 x2 d1 d2 ε eps_nonneg hd1 hd2
  have hσ : σ = (1 + ρ) / 2 := rfl
  have hσpos : (0 : ℝ) < σ := sigma_pos
  calc V (nextX1q x1 x2 + d1) (nextX2q x1 x2 + d2)
      ≤ (1 + ρ) / 2 * V x1 x2 + 810 * ε ^ 2 := hiss
    _ = σ * V x1 x2 + 810 * ε ^ 2 := by rw [hσ]
    _ ≤ σ * v + 810 * ε ^ 2 := by nlinarith [hσpos, hv]

/-- A trajectory of the quantized-gain loop under bounded per-step error. -/
structure QuantTrajQ where
  x1 : Nat → ℝ
  x2 : Nat → ℝ
  d1 : Nat → ℝ
  d2 : Nat → ℝ
  hd1 : ∀ n, |d1 n| ≤ ε
  hd2 : ∀ n, |d2 n| ≤ ε
  hstep1 : ∀ n, x1 (n + 1) = nextX1q (x1 n) (x2 n) + d1 n
  hstep2 : ∀ n, x2 (n + 1) = nextX2q (x1 n) (x2 n) + d2 n

/-- **The ultimate bound for the system the hardware implements.**

    Same envelope `σⁿ·V₀ + Vbound` as `Transport.ultimate_bound`, but about
    the quantized-gain dynamics — so the gain-rounding error is inside the
    theorem rather than outside it. -/
theorem ultimate_bound_q (T : QuantTrajQ) (n : Nat) :
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
    have hx1 : T.x1 (m + 1) = nextX1q (T.x1 m) (T.x2 m) + T.d1 m := T.hstep1 m
    have hx2 : T.x2 (m + 1) = nextX2q (T.x1 m) (T.x2 m) + T.d2 m := T.hstep2 m
    rw [hx1, hx2]
    have hc := step_contracts_q (T.x1 m) (T.x2 m) (T.d1 m) (T.d2 m)
      (σ ^ m * V (T.x1 0) (T.x2 0) + Vbound) (T.hd1 m) (T.hd2 m) ih
    have hfix : σ * Vbound + 810 * ε ^ 2 = Vbound := by
      have hne : (1 : ℝ) - σ ≠ 0 := ne_of_gt hone
      unfold Vbound
      field_simp
      ring
    calc V (nextX1q (T.x1 m) (T.x2 m) + T.d1 m) (nextX2q (T.x1 m) (T.x2 m) + T.d2 m)
        ≤ σ * (σ ^ m * V (T.x1 0) (T.x2 0) + Vbound) + 810 * ε ^ 2 := hc
      _ = σ ^ (m + 1) * V (T.x1 0) (T.x2 0) + (σ * Vbound + 810 * ε ^ 2) := by ring
      _ = σ ^ (m + 1) * V (T.x1 0) (T.x2 0) + Vbound := by rw [hfix]

end SparkleProofs.Control.QuantizedGains
