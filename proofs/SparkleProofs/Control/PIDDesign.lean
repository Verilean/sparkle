/-
  Closed-loop Lyapunov certificate for the PID demo — the worked example that
  tutorial Chapter 12 §12.1–12.2 walks through line by line.

  ## The system, exactly as implemented

  Plant (`IP/Control/PID.lean : plantStep`, `plantA/plantB`):

      x⁺ = 0.9·x + 0.1·u

  PID (`IP/Control/PID.lean : step`, gains `demoGains`), regulating to r = 0:

      e   = −x
      I⁺  = I + Ki·e                    Ki = 1/4
      u   = Kp·e + I⁺ + Kd·(e − p)      Kp = 2,  Kd = 1/8
      p⁺  = e                           (p = previous error register)

  Substituting, the closed loop is linear in the state s = (x, I, p):

      x⁺ = 0.6625·x + 0.1·I − 0.0125·p
      I⁺ = −0.25·x  +     I
      p⁺ = −x

  (0.6625 = 0.9 − 0.1·(Kp + Ki + Kd).)  Closed-loop eigenvalues: 0.8717,
  0.8085, −0.0177 — stable, and that is the claim this file makes precise.

  ## The certificate

  `P` solves the discrete Lyapunov equation `AᵀPA − P = −I` (offline
  iteration, rounded to 4 decimals):

      P = ⎡ 8.0999  −5.4050  −0.0850 ⎤
          ⎢−5.4050   9.7880   0.0574 ⎥
          ⎣−0.0850   0.0574   1.0013 ⎦

  Certified rate ρ = 39/40 (the same constant the LQR chapter uses; the true
  worst-case ratio is 0.9306, so the certificate has real slack).  The
  `nlinarith` hints are the rows of the exact rational LDLᵀ of `ρP − AᵀPA`
  (pivots 0.798 / 0.732 / 0.975 — comfortably positive).

  ## What this does and does not say about the RTL

  This is the ℝ-level design fact.  On the implementation side
  (`IP/Control/PID.lean`) the same loop runs in Q15.16 with the integrator
  and output clamped; quantization enters as a bounded disturbance exactly as
  in `Transport.lean`, and the anti-windup clamp additionally makes `|I|` and
  `|u|` bounded *unconditionally* — for any gains, any input — which is
  checked by slamming the loop in `Tests/IP/Control/PIDTest.lean`.  The split
  (structural boundedness vs. certified convergence) is the chapter's first
  lesson.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SparkleProofs.Control.PIDDesign

/-! ### Gains and plant -/

noncomputable def Kp : ℝ := 2
noncomputable def Ki : ℝ := 1 / 4
noncomputable def Kd : ℝ := 1 / 8

/-- Plant pole and input gain: `x⁺ = pa·x + pb·u`. -/
noncomputable def pa : ℝ := 9 / 10
noncomputable def pb : ℝ := 1 / 10

/-! ### The closed loop, written out -/

/-- `x⁺ = (pa − pb(Kp+Ki+Kd))·x + pb·I − pb·Kd·p`. -/
noncomputable def nextX (x I p : ℝ) : ℝ :=
  (pa - pb * (Kp + Ki + Kd)) * x + pb * I - pb * Kd * p

/-- `I⁺ = I − Ki·x`. -/
noncomputable def nextI (x I _p : ℝ) : ℝ := I - Ki * x

/-- `p⁺ = e = −x`. -/
noncomputable def nextP (x _I _p : ℝ) : ℝ := -x

/-! ### The Lyapunov matrix -/

noncomputable def p11 : ℝ := 80999 / 10000
noncomputable def p12 : ℝ := -54050 / 10000
noncomputable def p13 : ℝ := -850 / 10000
noncomputable def p22 : ℝ := 97880 / 10000
noncomputable def p23 : ℝ := 574 / 10000
noncomputable def p33 : ℝ := 10013 / 10000

/-- `V(s) = sᵀPs`, expanded to monomials. -/
noncomputable def V (x I p : ℝ) : ℝ :=
  p11 * x ^ 2 + p22 * I ^ 2 + p33 * p ^ 2
    + 2 * p12 * x * I + 2 * p13 * x * p + 2 * p23 * I * p

/-- `P ≻ 0` by Sylvester: leading minors 8.10, 50.07, 50.09. -/
theorem P_posdef :
    (0 : ℝ) < p11 ∧
    (0 : ℝ) < p11 * p22 - p12 ^ 2 ∧
    (0 : ℝ) < p11 * (p22 * p33 - p23 ^ 2)
              - p12 * (p12 * p33 - p23 * p13)
              + p13 * (p12 * p23 - p22 * p13) := by
  refine ⟨by norm_num [p11], by norm_num [p11, p22, p12], ?_⟩
  norm_num [p11, p12, p13, p22, p23, p33]

/-- The sandwich: `V` dominates the squared norm (λ_min(P) ≈ 1.0004) and is
    dominated by 15 of it (λ_max(P) ≈ 14.42). -/
theorem V_lower (x I p : ℝ) :
    (999 / 1000 : ℝ) * (x ^ 2 + I ^ 2 + p ^ 2) ≤ V x I p := by
  unfold V p11 p12 p13 p22 p23 p33
  nlinarith [sq_nonneg (x + I), sq_nonneg (x - I), sq_nonneg (x + p),
    sq_nonneg (x - p), sq_nonneg (I + p), sq_nonneg (I - p),
    sq_nonneg (2 * x - I), sq_nonneg (x - 2 * I),
    sq_nonneg ((6588 / 10000) * x - I), sq_nonneg x, sq_nonneg I, sq_nonneg p]

theorem V_upper (x I p : ℝ) :
    V x I p ≤ 15 * (x ^ 2 + I ^ 2 + p ^ 2) := by
  unfold V p11 p12 p13 p22 p23 p33
  nlinarith [sq_nonneg (x + I), sq_nonneg (x - I), sq_nonneg (x + p),
    sq_nonneg (x - p), sq_nonneg (I + p), sq_nonneg (I - p)]

/-- **The PID closed-loop Lyapunov contraction**: one sample of the loop
    shrinks `V` by at least ρ = 39/40, for every state.

    Hints: rows of the exact rational LDLᵀ of `ρP − AᵀPA`
    (`x + 0.1694·I + 0.0027·p`, `I − 0.0025·p`, `p`; pivots
    0.798 / 0.732 / 0.975). -/
theorem pid_lyapunov_decrease (x I p : ℝ) :
    V (nextX x I p) (nextI x I p) (nextP x I p) ≤ (39 / 40) * V x I p := by
  unfold V nextX nextI nextP p11 p12 p13 p22 p23 p33 Kp Ki Kd pa pb
  nlinarith [sq_nonneg (x + (1694 / 10000) * I + (27 / 10000) * p),
    sq_nonneg (I - (25 / 10000) * p), sq_nonneg p,
    sq_nonneg x, sq_nonneg I, sq_nonneg (x + I), sq_nonneg (x - I)]

/-- Corollary in the form the tutorial quotes: geometric convergence of the
    state norm — after n samples the state has decayed like `(39/40)^(n/2)`
    up to the conditioning of `P`. -/
theorem pid_geometric_decay (x I p : ℝ) (n : ℕ)
    (traj : ℕ → ℝ × ℝ × ℝ)
    (h0 : traj 0 = (x, I, p))
    (hstep : ∀ k, traj (k + 1) =
      (nextX (traj k).1 (traj k).2.1 (traj k).2.2,
       nextI (traj k).1 (traj k).2.1 (traj k).2.2,
       nextP (traj k).1 (traj k).2.1 (traj k).2.2)) :
    V (traj n).1 (traj n).2.1 (traj n).2.2 ≤ (39 / 40) ^ n * V x I p := by
  induction n with
  | zero => simp [h0]
  | succ m ih =>
    have h := hstep m
    have hd := pid_lyapunov_decrease (traj m).1 (traj m).2.1 (traj m).2.2
    have hV : 0 ≤ V x I p := by
      have := V_lower x I p
      nlinarith [sq_nonneg x, sq_nonneg I, sq_nonneg p]
    calc V (traj (m+1)).1 (traj (m+1)).2.1 (traj (m+1)).2.2
        = V (nextX (traj m).1 (traj m).2.1 (traj m).2.2)
            (nextI (traj m).1 (traj m).2.1 (traj m).2.2)
            (nextP (traj m).1 (traj m).2.1 (traj m).2.2) := by rw [h]
      _ ≤ (39 / 40) * V (traj m).1 (traj m).2.1 (traj m).2.2 := hd
      _ ≤ (39 / 40) * ((39 / 40) ^ m * V x I p) := by nlinarith [ih]
      _ = (39 / 40) ^ (m + 1) * V x I p := by ring

end SparkleProofs.Control.PIDDesign
