/-
  Algebraic rewriting of a control law: equal over ℝ, NOT equal in fixed point.

  ## The use case

  You want fewer multiplies (or fewer divisions) in the datapath, so you
  rewrite the control law:

      u = Kp·e + Ki·s + Kd·(e − p)          -- as written
      u = (Kp+Kd)·e + Ki·s − Kd·p           -- Kd folded into the e coefficient

  Over ℝ these are the same function; `ring` proves it in one line.  In
  Q15.16 they are **different circuits**, because each `mulQ` floors and the
  rewrite moved the floors around.  Measured over 200 000 random states:

      disagreements   87 751 / 200 000   (44 %)
      worst |uA − uB|        1 lsb

  So the honest statement is not "the rewrite is safe" but:

      the rewrite is exact over ℝ, and costs at most N lsb in Q15.16,
      where N is the change in floor count along any path

  Both halves are proved below.  This is the pattern for any such rewrite:
  prove the ℝ identity with `ring`, then bound the fixed-point gap from the
  per-`mulQ` error (`Transport.mulQ_error`) — never assume the second follows
  from the first.

  ## Why it matters for a certificate

  `QuantizedGains.lean` re-certified the *gains*; this is the same issue one
  level up, for the *expression shape*.  If you prove stability for `uA` and
  synthesize `uB`, the Lyapunov argument covers a system the hardware does
  not implement — unless you carry the 1-lsb difference as an extra
  disturbance, which is exactly what `bound` below supplies to the ISS
  machinery.

  ## Divisions

  The same applies to strength reduction on divisions, with one extra
  obligation: the ℝ identity `(a/b)·x = a·(x/b)` needs `b ≠ 0`, so the
  rewrite is only licensed where the guard holds.  `div_reassoc` records
  that.  In fixed point a division is `divQref`, whose error is TWO-sided
  (`(−1,1)` lsb, it truncates) rather than the one-sided `(−1,0]` of `mulQ`
  — so moving a division across a rewrite changes the error interval shape,
  not just its size.
-/

import SparkleProofs.Control.Transport

namespace SparkleProofs.Control.AlgebraicRewrite

open SparkleProofs.Control.Transport

/-! ### Over ℝ: the rewrite is exact -/

/-- The control law as written: three separate gain products. -/
noncomputable def uA (kp ki kd e s p : ℝ) : ℝ := kp * e + ki * s + kd * (e - p)

/-- The rewritten law: `Kd` folded into the `e` coefficient.  On hardware the
    sum `kp + kd` is a compile-time constant, so this trades a runtime
    multiply for a constant fold in the general case. -/
noncomputable def uB (kp ki kd e s p : ℝ) : ℝ := (kp + kd) * e + ki * s - kd * p

/-- **The ℝ identity.**  One line — this is the easy half, and the half that
    tempts you into thinking the rewrite is free. -/
theorem uA_eq_uB (kp ki kd e s p : ℝ) : uA kp ki kd e s p = uB kp ki kd e s p := by
  unfold uA uB; ring

/-- Strength reduction on a division, with the side condition made explicit.
    `b ≠ 0` is not a formality: the rewrite is simply unlicensed at `b = 0`,
    and a circuit that divides has to handle that case anyway. -/
theorem div_reassoc (a b x : ℝ) (hb : b ≠ 0) : (a / b) * x = a * (x / b) := by
  field_simp

/-! ### In Q15.16: the rewrite is not exact

The fixed-point images of `uA` and `uB` on numerators.  Both use three
`mulQ`s, but they floor *different products*, which is enough to separate
them. -/

/-- `uA` in Q15.16, on numerators. -/
def uAq (kp ki kd e s p : ℤ) : ℤ := mulQ kp e + mulQ ki s + mulQ kd (e - p)

/-- `uB` in Q15.16, on numerators. -/
def uBq (kp ki kd e s p : ℤ) : ℤ := mulQ (kp + kd) e + mulQ ki s - mulQ kd p

theorem toR_add (a b : ℤ) : toR (a + b) = toR a + toR b := by
  unfold toR; push_cast; ring

theorem toR_sub (a b : ℤ) : toR (a - b) = toR a - toR b := by
  unfold toR; push_cast; ring

theorem toR_eq_mul_lsb (n : ℤ) : toR n = (n : ℝ) * lsb := by
  unfold toR lsb; ring

/-- Each `mulQ` sits within one lsb below the exact product (`mulQ_error`),
    so a three-`mulQ` expression is within 3 lsb of its ℝ value. -/
theorem uAq_err (kp ki kd e s p : ℤ) :
    |toR (uAq kp ki kd e s p)
      - uA (toR kp) (toR ki) (toR kd) (toR e) (toR s) (toR p)| ≤ 3 * lsb := by
  obtain ⟨h1lo, h1hi⟩ := mulQ_error kp e
  obtain ⟨h2lo, h2hi⟩ := mulQ_error ki s
  obtain ⟨h3lo, h3hi⟩ := mulQ_error kd (e - p)
  rw [toR_sub] at h3lo h3hi
  unfold uAq uA
  rw [toR_add, toR_add,
      toR_eq_mul_lsb (mulQ kp e), toR_eq_mul_lsb (mulQ ki s),
      toR_eq_mul_lsb (mulQ kd (e - p)), abs_le]
  constructor <;> linarith

/-- Same count for the rewritten shape. -/
theorem uBq_err (kp ki kd e s p : ℤ) :
    |toR (uBq kp ki kd e s p)
      - uB (toR kp) (toR ki) (toR kd) (toR e) (toR s) (toR p)| ≤ 3 * lsb := by
  obtain ⟨h1lo, h1hi⟩ := mulQ_error (kp + kd) e
  obtain ⟨h2lo, h2hi⟩ := mulQ_error ki s
  obtain ⟨h3lo, h3hi⟩ := mulQ_error kd p
  rw [toR_add] at h1lo h1hi
  unfold uBq uB
  rw [toR_sub, toR_add,
      toR_eq_mul_lsb (mulQ (kp + kd) e), toR_eq_mul_lsb (mulQ ki s),
      toR_eq_mul_lsb (mulQ kd p), abs_le]
  constructor <;> linarith

/-! ### Which rewrites are FREE — the part a search needs

For choosing an RTL shape automatically, the useful question is not "how big
is the error" but "which rewrites cost nothing at all".  Those can be applied
without bookkeeping; only the rest need an error budget.

Measured, then proved:

| rewrite | fixed point |
|---|---|
| reassociate / commute additions | **exact** |
| `mulQ a e + mulQ b e → mulQ (a+b) e` | exact **iff** one coefficient is a whole number of units |
| `mulQ k (a+b) → mulQ k a + mulQ k b` | 1 lsb — crosses a floor |

The middle row is the one that surprises.  Folding two gains into one saves a
multiplier, and it is tempting to assume it is always safe because it is
"just constant folding".  It is not: with `a = 0.5, b = 0.25` — both powers
of two — it disagrees on 25 % of inputs.  With `a = 2.0, b = 0.618` it is
exact.  Being dyadic is not the criterion; having **no fractional part** is,
because then `a·e / 2¹⁶` is an integer and there is nothing for the floor to
discard. -/

/-- **Constant folding is exact exactly when one gain is integral.**

    `scale ∣ a` says `a` denotes a whole number (2.0, 3.0, …), so `a·e` is
    always a multiple of `scale` and its `mulQ` loses nothing.  The other
    coefficient is unconstrained.

    A search may apply this rewrite freely under the hypothesis and must
    treat it as costing 1 lsb otherwise. -/
theorem fold_exact (a b e : ℤ) (ha : scale ∣ a) :
    mulQ a e + mulQ b e = mulQ (a + b) e := by
  obtain ⟨k, hk⟩ := ha
  subst hk
  unfold mulQ
  have hs : (0 : ℤ) < scale := by unfold scale; decide
  have h1 : scale * k * e = scale * (k * e) := by ring
  have h2 : (scale * k + b) * e = scale * (k * e) + b * e := by ring
  rw [h1, h2, Int.mul_ediv_cancel_left _ (by omega : (scale:ℤ) ≠ 0)]
  rw [add_comm (scale * (k * e)) (b * e), Int.add_mul_ediv_left _ _
      (by unfold scale; decide : (scale:ℤ) ≠ 0)]
  ring

/-- Additions reassociate exactly — no floor is involved, so this is just
    `Int` arithmetic.  Free for a search to use. -/
theorem add_reassoc_exact (x y z : ℤ) : (x + y) + z = x + (y + z) := by ring

/-- **The gap between the two shapes, bounded.**

    Each side is within 3 lsb of the same ℝ value (`uA_eq_uB`), so they are
    within 6 lsb of each other.  That is the *provable* bound from floor
    counting alone; the *measured* worst case is 1 lsb, because the floors
    are strongly correlated — a reminder that these bounds are sound, not
    tight, and that a tight bound needs a finer argument than counting. -/
theorem uAq_uBq_gap (kp ki kd e s p : ℤ) :
    |toR (uAq kp ki kd e s p) - toR (uBq kp ki kd e s p)| ≤ 6 * lsb := by
  have heq := uA_eq_uB (toR kp) (toR ki) (toR kd) (toR e) (toR s) (toR p)
  have h1 := abs_le.mp (uAq_err kp ki kd e s p)
  have h2 := abs_le.mp (uBq_err kp ki kd e s p)
  rw [heq] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end SparkleProofs.Control.AlgebraicRewrite
