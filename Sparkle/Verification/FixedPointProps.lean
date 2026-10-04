/-
  The Q15.16 multiply, proved rather than sampled.

  ## What this closes

  Tutorial Chapter 12 §12.2 argues that the ℝ control law, the Q15.16
  equation `retype` derives from it, and the RTL datapath are all the same
  equation.  The last link — "Sparkle's `mulQ` computes the same function as
  the transported `(a * b) / 2^16`" — was the one step checked on fixtures
  rather than proved (`Tests/IP/Control/PrecisionSweepTest.lean`).

  `mulQ_toInt` below is that proof.

  ## Why the obvious tactic does not work

  `bv_decide` rejects the goal outright:

      None of the hypotheses are in the supported BitVec fragment

  `BitVec.toInt` and `Int./` are not in the bitvector fragment it decides, so
  no width makes it applicable.  (The chapter used to claim `bv_decide`
  "should get it at this width"; that was wrong, and the correction is why
  this file exists.)  The route is instead:

    1. `prod64` — the 64-bit product of two sign-extended 32-bit values is
       EXACT.  `BitVec.toInt_mul` gives a `bmod 2^64`, and `|a·b| ≤ 2^62`
       kills it.
    2. `extract_toInt` — `extractLsb' 16 32` on a 64-bit word is division by
       2^16 on `toInt`, *provided the result fits in signed 32 bits*.  Proved
       by unfolding `Int.bmod` and splitting; `omega` cannot see through
       `bmod` on its own.
    3. Compose.

  ## The hypothesis is load-bearing

  Without the no-overflow side condition the statement is FALSE — the extract
  wraps.  At the 8/4 analogue (small enough to enumerate) `a = 17, b = 121`
  gives `17·121/16 = 128`, one past the signed 8-bit maximum, and the extract
  returns −128.  `Tests/IP/Control/PrecisionSweepTest.lean` pins that
  counterexample so the hypothesis is not later dropped as pedantry.

  No Mathlib: this lives in the RTL build graph deliberately, so the datapath
  and its correctness proof are checked by the same `lake build`.
-/

namespace Sparkle.Verification.FixedPointProps

/-- Sparkle's Q15.16 multiply, restated here verbatim from
    `IP/Control/FixedPoint.lean`.

    Restated rather than imported ON PURPOSE: importing `IP.Control` would
    pull the whole `Signal`/elaborator stack into a file that is pure
    `BitVec` arithmetic, and this module is meant to stay cheap enough to sit
    in the RTL build graph.  `Tests/IP/Control/PrecisionSweepTest.lean` pins
    the two definitions against each other so the restatement cannot drift. -/
def mulQ (a b : BitVec 32) : BitVec 32 :=
  BitVec.extractLsb' 16 32 ((a.signExtend 64) * (b.signExtend 64))

/-- Sign-extending two 32-bit values to 64 bits makes their product exact:
    64 bits cannot overflow on a product of two 32-bit signed values, since
    `|a·b| ≤ 2^31 · 2^31 = 2^62 < 2^63`. -/
theorem prod64 (a b : BitVec 32) :
    ((a.signExtend 64) * (b.signExtend 64)).toInt = a.toInt * b.toInt := by
  have ha1 : -(2^31 : Int) ≤ a.toInt := by have := BitVec.le_toInt a; simpa using this
  have ha2 : a.toInt < 2^31 := by have := @BitVec.toInt_lt 32 a; simpa using this
  have hb1 : -(2^31 : Int) ≤ b.toInt := by have := BitVec.le_toInt b; simpa using this
  have hb2 : b.toInt < 2^31 := by have := @BitVec.toInt_lt 32 b; simpa using this
  have hbound : (a.toInt * b.toInt).natAbs ≤ 2^31 * 2^31 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  -- Discharge the two inner `bmod`s as standalone equations: rewriting them
  -- in place leaves `omega` unable to connect the result to `a.toInt * b.toInt`.
  have ea : a.toInt.bmod (2^32) = a.toInt := Int.bmod_eq_of_le (by omega) (by omega)
  have eb : b.toInt.bmod (2^32) = b.toInt := Int.bmod_eq_of_le (by omega) (by omega)
  rw [BitVec.toInt_mul, BitVec.toInt_signExtend, BitVec.toInt_signExtend]
  simp only [Nat.min_def, if_neg (by omega : ¬ (64 ≤ 32))]
  rw [ea, eb]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- `extractLsb' 16 32` is `/ 2^16` on `toInt` — an ARITHMETIC shift, so it
    floors, matching `Int./` — as long as the quotient fits in signed 32 bits.

    `omega` cannot see through `Int.bmod`, so it is unfolded to its `if` and
    split before handing over. -/
theorem extract_toInt (p : BitVec 64)
    (h1 : -(2^31 : Int) ≤ p.toInt / 2^16) (h2 : p.toInt / 2^16 < 2^31) :
    (BitVec.extractLsb' 16 32 p).toInt = p.toInt / 2^16 := by
  have hn : (BitVec.extractLsb' 16 32 p).toNat = p.toNat >>> 16 % 2^32 := by simp
  have hlt : p.toNat < 2^64 := p.isLt
  rw [BitVec.toInt_eq_toNat_bmod, hn]
  rw [BitVec.toInt_eq_toNat_bmod] at h1 h2 ⊢
  simp only [Nat.shiftRight_eq_div_pow, Int.bmod] at *
  split at h1 <;> split at h2 <;> split <;> omega

/-- **The Chapter 12 §12.2.3 lemma.**  Sparkle's Q15.16 multiply computes the
    transported equation's `(a * b) / 2^16`, exactly, whenever the result is
    representable.

    This is what upgrades §12.2.2 from "agrees on the fixtures we tried" to
    "is the same function".  With it, the chain

        ℝ equation → (retype) → Q15.16 equation → (this) → RTL datapath

    has no sampled link left. -/
theorem mulQ_toInt (a b : BitVec 32)
    (hlo : -(2^31 : Int) ≤ (a.toInt * b.toInt) / 2^16)
    (hhi : (a.toInt * b.toInt) / 2^16 < 2^31) :
    (mulQ a b).toInt = (a.toInt * b.toInt) / 2^16 := by
  unfold mulQ
  rw [extract_toInt _ (by rw [prod64]; exact hlo) (by rw [prod64]; exact hhi), prod64]

end Sparkle.Verification.FixedPointProps
