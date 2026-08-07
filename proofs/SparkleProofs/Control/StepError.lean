/-
  Closing the last conditional in the Chapter 12 chain: the fixed-point
  trajectory really is an ε-perturbed ℝ trajectory.

  ## What was conditional

  `Transport.lean` proves `ultimate_bound` for any `QuantTraj` — a structure
  whose fields ASSUME

      x(n+1) = nextX (x n) + d n        with  |d n| ≤ ε.

  That is the right model of a quantized loop, but nothing connected it to the
  integers the circuit actually iterates.  So `ultimate_bound` read as "IF the
  hardware trajectory has this shape, THEN it is ultimately bounded", and the
  antecedent was folklore.

  This file discharges it.  `stepX1_err` / `stepX2_err` bound one fixed-point
  step against the ℝ update, `mkTraj` packages an integer trajectory into a
  `QuantTraj`, and `intTraj_ultimate_bound` states the consequence directly
  about integer state sequences — no `QuantTraj` hypothesis in sight.
  `circuit_ultimate_bound` then specialises it to the circuit's own gains.

  ## Where the ε = 3·lsb comes from

  Per component, counting floors:

  * `x1⁺ = x1 + mulQ dtQ x2` — one `mulQ`, so one floor: **1 lsb** (proved
    tighter than ε).
  * `x2⁺ = x2 + mulQ dtQ (-(mulQ k1Q x1 + mulQ k2Q x2))` — three `mulQ`s
    nested two deep.  The inner two each floor by < 1 lsb; `dt = 1/16`
    attenuates their contribution to the outer product, and the outer floor
    adds one more.  **3 lsb** is the loose bound `Transport.ε` already used.

  ## Gain quantization — handled, not deferred

  `stepX2_err` is stated against the ℝ update *using the quantized gains*
  (`toR k1Q`, `toR k2Q`), not the exact `k1 = 0.6180`, `k2 = 1.2600`:

      k1 = 0.6180  →  40501/65536 = 0.61799…   off by 0.248 lsb
      k2 = 1.2600  →  82575/65536 = 1.25999…   off by 0.360 lsb

  Those coefficient errors multiply the STATE, so their contribution grows
  with `|x|` and genuinely cannot be folded into a constant ε.  The fix is
  not a bigger ε — it is to certify the system the hardware implements, which
  `QuantizedGains.lean` does (same `P`, same ρ = 39/40; the true contraction
  ratio moves by 3.7·10⁻⁸).

  `circuit_ultimate_bound` at the bottom composes the two, so the gains in
  the theorem are the gains in the registers.  Nothing is left conditional.

  `dt = 1/16` never had the issue: dyadic, so `toR dtQ = dt` exactly, proved
  below rather than assumed.

-/

import SparkleProofs.Control.Transport
import SparkleProofs.Control.QuantizedGains

namespace SparkleProofs.Control.StepError

open SparkleProofs.Control.Transport SparkleProofs.Control.LQRDesign
open SparkleProofs.Control.QuantizedGains

/-! ### Q15.16 numerators for the design constants -/

/-- `dt = 1/16` as a Q15.16 numerator.  Dyadic, hence exact. -/
def dtQ : ℤ := 4096

/-- `toR dtQ = dt`, exactly — the one constant in this design that survives
    quantization with no error at all. -/
theorem toR_dtQ : toR dtQ = dt := by unfold toR dtQ dt scale; norm_num

/-! ### `toR` is additive, and relates to `lsb` -/

theorem toR_add (a b : ℤ) : toR (a + b) = toR a + toR b := by
  unfold toR; push_cast; ring

theorem toR_neg (a : ℤ) : toR (-a) = -toR a := by
  unfold toR; push_cast; ring

theorem toR_eq_mul_lsb (n : ℤ) : toR n = (n : ℝ) * lsb := by
  unfold toR lsb; ring

/-! ### One fixed-point step, per component -/

/-- The circuit's `x1` update on numerators. -/
def stepX1 (x1 x2 : ℤ) : ℤ := x1 + mulQ dtQ x2

/-- The circuit's `x2` update on numerators, with the gains as parameters so
    the statement does not silently fix a particular rounding of them. -/
def stepX2 (k1Q k2Q x1 x2 : ℤ) : ℤ :=
  x2 + mulQ dtQ (-(mulQ k1Q x1 + mulQ k2Q x2))

/-- **One `mulQ`, one floor.**  The `x1` channel is off by at most one LSB —
    tighter than `ε`, because `dt` is exact and only one product is floored. -/
theorem stepX1_err (x1 x2 : ℤ) :
    |toR (stepX1 x1 x2) - nextX1 (toR x1) (toR x2)| ≤ lsb := by
  obtain ⟨hlo, hhi⟩ := mulQ_error dtQ x2
  rw [toR_dtQ] at hlo hhi
  unfold stepX1 nextX1
  rw [toR_add, toR_eq_mul_lsb (mulQ dtQ x2), abs_le]
  constructor <;> linarith

/-- **Three `mulQ`s, three floors.**  The `x2` channel is off by at most
    `3·lsb = ε` from the ℝ update *with the same (quantized) gains*.  See the
    header on why the gains appear as `toR k1Q` rather than `k1`. -/
theorem stepX2_err (k1Q k2Q x1 x2 : ℤ) :
    |toR (stepX2 k1Q k2Q x1 x2)
      - (toR x2 + dt * (-(toR k1Q * toR x1 + toR k2Q * toR x2)))| ≤ 3 * lsb := by
  obtain ⟨h1lo, h1hi⟩ := mulQ_error k1Q x1
  obtain ⟨h2lo, h2hi⟩ := mulQ_error k2Q x2
  obtain ⟨h3lo, h3hi⟩ := mulQ_error dtQ (-(mulQ k1Q x1 + mulQ k2Q x2))
  rw [toR_dtQ] at h3lo h3hi
  rw [toR_neg, toR_add] at h3lo h3hi
  unfold stepX2
  rw [toR_add, toR_eq_mul_lsb (mulQ dtQ _), abs_le]
  rw [toR_eq_mul_lsb (mulQ k1Q x1), toR_eq_mul_lsb (mulQ k2Q x2)] at h3lo h3hi
  have hdt : dt = 1/16 := rfl
  constructor <;> nlinarith [lsb_pos]

/-! ### From integer trajectories to `QuantTraj` -/

/-- Package an integer state sequence whose steps are ε-accurate into the
    `QuantTraj` that `ultimate_bound` consumes.

    The disturbances are not invented: `d n` is *defined* as the difference
    between what the circuit computed and what ℝ would have, so `hstep` holds
    by `ring` and the only real content is the bound, supplied by the caller
    from `stepX1_err` / `stepX2_err`. -/
noncomputable def mkTraj (f1 f2 : Nat → ℤ)
    (h1 : ∀ n, |toR (f1 (n+1)) - nextX1 (toR (f1 n)) (toR (f2 n))| ≤ ε)
    (h2 : ∀ n, |toR (f2 (n+1)) - nextX2 (toR (f1 n)) (toR (f2 n))| ≤ ε) :
    QuantTraj :=
  { x1 := fun n => toR (f1 n)
    x2 := fun n => toR (f2 n)
    d1 := fun n => toR (f1 (n+1)) - nextX1 (toR (f1 n)) (toR (f2 n))
    d2 := fun n => toR (f2 (n+1)) - nextX2 (toR (f1 n)) (toR (f2 n))
    hd1 := h1
    hd2 := h2
    hstep1 := by intro n; ring
    hstep2 := by intro n; ring }

/-- **The ultimate bound, stated about integers.**

    No `QuantTraj` in the statement: given an integer state sequence whose
    steps are ε-accurate, its interpreted Lyapunov value obeys the same
    envelope `σⁿ·V₀ + Vbound`.  This is `ultimate_bound` with its antecedent
    discharged. -/
theorem intTraj_ultimate_bound (f1 f2 : Nat → ℤ)
    (h1 : ∀ n, |toR (f1 (n+1)) - nextX1 (toR (f1 n)) (toR (f2 n))| ≤ ε)
    (h2 : ∀ n, |toR (f2 (n+1)) - nextX2 (toR (f1 n)) (toR (f2 n))| ≤ ε)
    (n : Nat) :
    V (toR (f1 n)) (toR (f2 n))
      ≤ σ ^ n * V (toR (f1 0)) (toR (f2 0)) + Vbound :=
  ultimate_bound (mkTraj f1 f2 h1 h2) n

/-! ### The chain, closed

`stepX2_err` bounds the circuit against the ℝ update *with the quantized
gains*, and `QuantizedGains` certifies exactly that system.  Composing them
leaves nothing conditional: the gains the hardware holds are the gains the
theorem is about. -/

/-- The `x2` step error, stated against the quantized-gain ℝ update by name.
    This is `stepX2_err` with the gains fixed to what the circuit holds. -/
theorem stepX2_err_q (x1 x2 : ℤ) :
    |toR (stepX2 40501 82575 x1 x2) - nextX2q (toR x1) (toR x2)| ≤ 3 * lsb := by
  have h := stepX2_err 40501 82575 x1 x2
  have e1 : toR 40501 = k1q := by unfold toR k1q scale; norm_num
  have e2 : toR 82575 = k2q := by unfold toR k2q scale; norm_num
  unfold nextX2q
  rw [e1, e2] at h
  exact h

/-- Likewise for `x1` — `nextX1q` is `nextX1` (only the gains changed). -/
theorem stepX1_err_q (x1 x2 : ℤ) :
    |toR (stepX1 x1 x2) - nextX1q (toR x1) (toR x2)| ≤ lsb :=
  stepX1_err x1 x2

/-- **The end of the chain.**

    An integer state sequence produced by the circuit's own update — the
    quantized gains, the floors, all of it — obeys the ultimate bound.  No
    `QuantTraj` hypothesis, no nominal-gain idealization: `f1`/`f2` are
    literally what the registers hold. -/
theorem circuit_ultimate_bound (f1 f2 : Nat → ℤ)
    (hs1 : ∀ n, f1 (n + 1) = stepX1 (f1 n) (f2 n))
    (hs2 : ∀ n, f2 (n + 1) = stepX2 40501 82575 (f1 n) (f2 n))
    (n : Nat) :
    V (toR (f1 n)) (toR (f2 n))
      ≤ σ ^ n * V (toR (f1 0)) (toR (f2 0)) + Vbound := by
  have h1 : ∀ n, |toR (f1 (n+1)) - nextX1q (toR (f1 n)) (toR (f2 n))| ≤ ε := by
    intro n
    rw [hs1 n]
    have := stepX1_err_q (f1 n) (f2 n)
    have hl : lsb ≤ ε := by unfold ε; have := lsb_pos; linarith
    linarith
  have h2 : ∀ n, |toR (f2 (n+1)) - nextX2q (toR (f1 n)) (toR (f2 n))| ≤ ε := by
    intro n
    rw [hs2 n]
    have := stepX2_err_q (f1 n) (f2 n)
    have : (3 : ℝ) * lsb = ε := by unfold ε; ring
    linarith [stepX2_err_q (f1 n) (f2 n)]
  exact ultimate_bound_q
    { x1 := fun n => toR (f1 n)
      x2 := fun n => toR (f2 n)
      d1 := fun n => toR (f1 (n+1)) - nextX1q (toR (f1 n)) (toR (f2 n))
      d2 := fun n => toR (f2 (n+1)) - nextX2q (toR (f1 n)) (toR (f2 n))
      hd1 := h1
      hd2 := h2
      hstep1 := by intro n; ring
      hstep2 := by intro n; ring } n

end SparkleProofs.Control.StepError
