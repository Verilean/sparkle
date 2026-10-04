/-
  Chapter 14, layer 1: the ℝ market-making model and its inventory stability.

  ## The model

  The quoting engine (`IP/Net/HFTQuote.lean`) implements the constant-window
  form of Avellaneda–Stoikov market making:

      r    = s − k₁·q          reservation price (k₁ = γσ²τ, ticks/lot)
      bid  = r − δ             δ = half-spread
      ask  = r + δ

  The skew term −k₁·q is the stabilising mechanism: positive inventory
  shifts BOTH quotes down, making the ask more attractive (sell more) and
  the bid less attractive (buy less).  Under a linearised fill response,
  one quoting window removes an expected `c·q` of inventory (0 < c < 1 —
  `c` collects k₁ × the book's fill sensitivity × window length), leaving

      q' = (1 − c)·q + w

  where `w` is the residual fill noise, bounded per window by the fill cap
  `W` (you cannot be filled more than the size you quote).  Intuition for
  `c`: at c = 0.2, the skewed quotes work off an expected 20% of the
  carried inventory each window — hence the (1−c)ⁿ decay and the fact that
  a stronger skew response shrinks the resting ball W/c.

  ## What is proved

  This is EXACTLY Chapter 12's shape with new names: a contraction plus a
  bounded disturbance gives a geometric envelope with a noise ball —

      |qₙ| ≤ (1−c)ⁿ·|q₀| + W/c

  In trading language: the mean dynamics keep the position inside `W/c` of
  flat, regardless of the starting position, with the transient dying
  geometrically.  This is the theorem a risk desk wants — and note that
  W/c is exact, not an over-approximation: (1−c)·(W/c) + W = W/c, so the
  ball reproduces itself under the step.

  ## What is assumed, honestly

  The linear fill response (expected drift −c·q) is a MODELLING assumption
  — the linearisation of the A–S exponential intensities around small
  inventories.  The circuit does not depend on it for safety: the position
  limit `clampSym qMax` holds by construction for ANY market behaviour
  (same argument as the PID integrator's anti-windup).  This file bounds
  the *behaviour inside the limit* under the stated model; the clamp
  bounds the worst case without a model.
-/
import Mathlib.Tactic

namespace SparkleProofs.Hft.MarketMaking

/-! ### The quote equations (the shared ℝ source of truth) -/

/-- Reservation price: mid skewed against the inventory. -/
noncomputable def resPrice (k1 s q : ℝ) : ℝ := s - k1 * q

/-- Bid: reservation minus the half-spread. -/
noncomputable def bidPrice (k1 δ s q : ℝ) : ℝ := resPrice k1 s q - δ

/-- Ask: reservation plus the half-spread. -/
noncomputable def askPrice (k1 δ s q : ℝ) : ℝ := resPrice k1 s q + δ

/-- Quotes bracket the reservation price symmetrically — the spread is
    inventory-independent, only its CENTRE moves.  (Sanity lemma; the
    stabilisation happens through the centre.) -/
theorem spread_symmetric (k1 δ s q : ℝ) :
    askPrice k1 δ s q - resPrice k1 s q = resPrice k1 s q - bidPrice k1 δ s q := by
  simp [askPrice, bidPrice]

/-- The skew is linear in inventory: one extra lot moves both quotes down
    by exactly k₁.  This is the mechanism the drift model linearises. -/
theorem skew_linear (k1 s q : ℝ) :
    resPrice k1 s (q + 1) = resPrice k1 s q - k1 := by
  simp [resPrice]; ring

/-! ### Mean inventory dynamics -/

/-- One quoting window of the mean inventory dynamics. -/
noncomputable def stepInv (c q w : ℝ) : ℝ := (1 - c) * q + w

/-- One window contracts the inventory magnitude, up to the fill noise. -/
theorem inventory_contracts (c q w W : ℝ)
    (hc1 : c < 1) (hw : |w| ≤ W) :
    |stepInv c q w| ≤ (1 - c) * |q| + W := by
  unfold stepInv
  calc |(1 - c) * q + w|
      ≤ |(1 - c) * q| + |w| := abs_add_le _ _
    _ = (1 - c) * |q| + |w| := by
        rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 - c)]
    _ ≤ (1 - c) * |q| + W := by linarith

/-- An inventory trajectory: contraction rate, per-window fill cap, the
    noise sequence, and the recurrence — same shape as
    `Control.QuantizedGains.QuantTrajQ`. -/
structure InvTraj where
  c    : ℝ
  W    : ℝ
  hc0  : 0 < c
  hc1  : c < 1
  hW   : 0 ≤ W
  q0   : ℝ
  w    : Nat → ℝ
  hw   : ∀ n, |w n| ≤ W

/-- The inventory at window `n`. -/
noncomputable def InvTraj.q (T : InvTraj) : Nat → ℝ
  | 0     => T.q0
  | n + 1 => stepInv T.c (T.q n) (T.w n)

/-- **The position ultimate bound.**  Geometric decay of the initial
    inventory plus the noise ball `W/c` — and the ball is EXACT:
    `(1−c)·(W/c) + W = W/c`, so the envelope reproduces itself. -/
theorem inventory_ultimate_bound (T : InvTraj) (n : Nat) :
    |T.q n| ≤ (1 - T.c) ^ n * |T.q0| + T.W / T.c := by
  induction n with
  | zero =>
    simp only [InvTraj.q, pow_zero, one_mul]
    have : 0 ≤ T.W / T.c := div_nonneg T.hW (le_of_lt T.hc0)
    linarith
  | succ m ih =>
    have hρ0 : (0:ℝ) ≤ 1 - T.c := by linarith [T.hc1]
    have hstep := inventory_contracts T.c (T.q m) (T.w m) T.W T.hc1 (T.hw m)
    have hmono : (1 - T.c) * |T.q m|
        ≤ (1 - T.c) * ((1 - T.c) ^ m * |T.q0| + T.W / T.c) :=
      mul_le_mul_of_nonneg_left ih hρ0
    have hball : (1 - T.c) * (T.W / T.c) + T.W = T.W / T.c := by
      have hc : T.c ≠ 0 := ne_of_gt T.hc0
      field_simp
      ring
    calc |T.q (m + 1)|
        ≤ (1 - T.c) * |T.q m| + T.W := hstep
      _ ≤ (1 - T.c) * ((1 - T.c) ^ m * |T.q0| + T.W / T.c) + T.W := by linarith
      _ = (1 - T.c) ^ (m + 1) * |T.q0| + ((1 - T.c) * (T.W / T.c) + T.W) := by ring
      _ = (1 - T.c) ^ (m + 1) * |T.q0| + T.W / T.c := by rw [hball]

/-- Corollary a risk desk can read: once the transient has died
    (`(1−c)ⁿ·|q₀| ≤ ε`), the position stays within `W/c + ε` of flat. -/
theorem inventory_settles (T : InvTraj) (n : Nat) (ε : ℝ)
    (htrans : (1 - T.c) ^ n * |T.q0| ≤ ε) :
    |T.q n| ≤ T.W / T.c + ε := by
  have := inventory_ultimate_bound T n
  linarith

end SparkleProofs.Hft.MarketMaking
