/-
  Restoring division — the BitVec working step refines the Nat model.

  The hardware does one restoring-division step on a 33-bit remainder and a
  32-bit quotient/dividend register.  Here we prove that single step computes
  exactly `nstep`/`nqbit` (from `Divider.Math`) on the `toNat` values, given the
  loop-invariant bound `R < V < 2^32`.  This is the only place `BitVec`↔`Nat`
  bit-reasoning is needed; everything else is the pure `Nat` invariant.
-/
import Sparkle.Verification.Divider.Math
import Std.Tactic.BVDecide

set_option maxHeartbeats 800000

namespace Sparkle.Verification.Divider.BitProof

open Sparkle.Verification.Divider.Math

/-- One BitVec restoring-division working step (mirrors `divNext`'s working
    branch): returns the new `(remainder, quotient)` registers. -/
def bwstep (V : BitVec 33) (R : BitVec 33) (Q : BitVec 32) : BitVec 33 × BitVec 32 :=
  let qtop := BitVec.extractLsb' 31 1 Q
  let remWithBit := (R <<< 1#33) ||| (0#32 ++ qtop)
  let trial := remWithBit - V
  let nonNeg := BitVec.extractLsb' 32 1 trial == 0#1
  let newR := if nonNeg then trial else remWithBit
  let newQ := (Q <<< 1#32) ||| (if nonNeg then 1#32 else 0#32)
  (newR, newQ)

/-- Disjoint OR is addition for the remainder shift-in. -/
theorem rem_or_eq_add (R : BitVec 33) (bit : BitVec 1) :
    (R <<< 1#33) ||| (0#32 ++ bit) = (R <<< 1#33) + (0#32 ++ bit) := by
  bv_decide

/-- Disjoint OR is addition for the quotient shift-in. -/
theorem quot_or_eq_add (Q : BitVec 32) (c : BitVec 32) (hc : c = 0#32 ∨ c = 1#32) :
    (Q <<< 1#32) ||| c = (Q <<< 1#32) + c := by
  rcases hc with h | h <;> subst h <;> bv_decide

/-- `(0#32 ++ bit).toNat = bit.toNat`. -/
theorem append_bit_toNat (Q : BitVec 32) :
    ((0#32 ++ BitVec.extractLsb' 31 1 Q : BitVec 33)).toNat = Q.toNat / 2 ^ 31 % 2 := by
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  simp

/-- `(R <<< 1).toNat = 2·R` when `R < 2^32`. -/
theorem shl1_toNat (R : BitVec 33) (hR : R.toNat < 2 ^ 32) :
    (R <<< 1#33).toNat = 2 * R.toNat := by
  have h1 : (1#33 : BitVec 33).toNat = 1 := by decide
  rw [BitVec.shiftLeft_eq', h1]
  bv_omega

/-- `remWithBit.toNat = 2·R + bit`. -/
theorem remWithBit_toNat (R : BitVec 33) (Q : BitVec 32) (hR : R.toNat < 2 ^ 32) :
    ((R <<< 1#33) ||| (0#32 ++ BitVec.extractLsb' 31 1 Q)).toNat
      = 2 * R.toNat + Q.toNat / 2 ^ 31 % 2 := by
  rw [rem_or_eq_add, BitVec.toNat_add, shl1_toNat R hR, append_bit_toNat]
  omega

/-- The shifted quotient with a new low bit. -/
theorem quotbit_toNat (Q : BitVec 32) (c : BitVec 32) (hc : c = 0#32 ∨ c = 1#32) :
    ((Q <<< 1#32) ||| c).toNat = 2 * Q.toNat % 2 ^ 32 + c.toNat := by
  rw [quot_or_eq_add Q c hc]
  have h1 : (1#32 : BitVec 32).toNat = 1 := by decide
  rw [BitVec.shiftLeft_eq', h1]
  rcases hc with rfl | rfl <;> bv_omega

/-- The sign bit of the trial subtraction indicates whether `V ≤ remWithBit`. -/
theorem bwstep_refine (V R : BitVec 33) (Q : BitVec 32)
    (hV32 : V < 4294967296#33) (hR : R < V) :
    (BitVec.extractLsb' 32 1 (((R <<< 1#33) ||| (0#32 ++ BitVec.extractLsb' 31 1 Q)) - V) == 0#1)
      = decide (V ≤ (R <<< 1#33) ||| (0#32 ++ BitVec.extractLsb' 31 1 Q)) := by
  bv_decide

/-- **Per-step refinement.**  Under the invariant bound `R < V < 2^32`, the
    BitVec working step computes `nstep`/`nqbit` on the `toNat` values, with the
    consumed bit being bit 31 of `Q`. -/
theorem bwstep_toNat (V R : BitVec 33) (Q : BitVec 32)
    (hVpos : 0 < V.toNat) (hV32 : V.toNat < 2 ^ 32) (hR : R.toNat < V.toNat) :
    (bwstep V R Q).1.toNat = nstep V.toNat R.toNat (Q.toNat / 2 ^ 31 % 2)
    ∧ (bwstep V R Q).2.toNat
        = 2 * Q.toNat % 2 ^ 32 + nqbit V.toNat R.toNat (Q.toNat / 2 ^ 31 % 2) := by
  have hrw : ((R <<< 1#33) ||| (0#32 ++ BitVec.extractLsb' 31 1 Q)).toNat
      = 2 * R.toNat + Q.toNat / 2 ^ 31 % 2 := remWithBit_toNat R Q (by omega)
  simp only [bwstep, nstep, nqbit, bwstep_refine V R Q hV32 hR, BitVec.le_def, hrw, decide_eq_true_iff]
  by_cases hc : V.toNat ≤ 2 * R.toNat + Q.toNat / 2 ^ 31 % 2
  · simp only [hc, if_true]
    refine ⟨by rw [BitVec.toNat_sub, hrw]; omega, ?_⟩
    rw [quotbit_toNat Q 1#32 (Or.inr rfl)]
    rfl
  · simp only [hc, if_false]
    refine ⟨hrw, ?_⟩
    rw [quotbit_toNat Q 0#32 (Or.inl rfl)]
    rfl
-- ============================================================================
-- Power helper lemmas
-- ============================================================================

theorem two_pow_split (k : Nat) (hk : k ≤ 31) : 2 ^ (31 - k) * 2 ^ (k + 1) = 2 ^ 32 := by
  rw [← Nat.pow_add]; congr 1; omega

theorem two_pow_split2 (k : Nat) (hk : k ≤ 31) : (2 : Nat) ^ 31 = 2 ^ k * 2 ^ (31 - k) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem Qk_lt (V D : Nat) (hVpos : 0 < V) (hD : D < 2 ^ 32) (k : Nat) (hk : k ≤ 32) :
    Qk V D k < 2 ^ k := by
  have h1 := (div_invariant V D hVpos hD k hk).2.1
  rw [h1]
  have hDk : Dk D k < 2 ^ k := by
    unfold Dk
    apply Nat.div_lt_of_lt_mul
    have he : 2 ^ (32 - k) * 2 ^ k = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
    rw [he]; exact hD
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hDk

-- ============================================================================
-- Encoding induction: the BitVec working iteration matches the Nat model
-- ============================================================================

/-- Iterate the BitVec working step `k` times. -/
def bwsteps (V : BitVec 33) : Nat → (BitVec 33 × BitVec 32) → (BitVec 33 × BitVec 32)
  | 0, s => s
  | k + 1, s => bwstep V (bwsteps V k s).1 (bwsteps V k s).2

/-- **The shift-register encoding invariant.**  After `k` BitVec working steps
    from `(0, |dividend|)`, the remainder register holds `Rk` and the quotient
    register holds the dual-use encoding `(D % 2^(32-k))·2^k + Qk` — high bits
    are the unconsumed dividend, low bits are the quotient. -/
theorem bwsteps_enc (V33 : BitVec 33) (D32 : BitVec 32)
    (hVpos : 0 < V33.toNat) (hV32 : V33.toNat < 2 ^ 32) (hD : D32.toNat < 2 ^ 32) :
    ∀ k, k ≤ 32 →
      (bwsteps V33 k (0#33, D32)).1.toNat = Rk V33.toNat D32.toNat k
      ∧ (bwsteps V33 k (0#33, D32)).2.toNat
          = D32.toNat % 2 ^ (32 - k) * 2 ^ k + Qk V33.toNat D32.toNat k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · show (0#33 : BitVec 33).toNat = Rk V33.toNat D32.toNat 0
      simp [Rk]
    · show (D32).toNat = D32.toNat % 2 ^ (32 - 0) * 2 ^ 0 + Qk V33.toNat D32.toNat 0
      simp only [Qk, Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
      omega
  | succ k ih =>
    intro hk1
    have hk : k ≤ 31 := by omega
    have he : (2 : Nat) ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    obtain ⟨ihR, ihQ⟩ := ih (by omega)
    have hRklt : Rk V33.toNat D32.toNat k < V33.toNat :=
      (div_invariant V33.toNat D32.toNat hVpos hD k (by omega)).2.2
    have hQklt : Qk V33.toNat D32.toNat k < 2 ^ k := Qk_lt _ _ hVpos hD k (by omega)
    have h2k : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
    -- (X*2^k + Qk) / 2^k = X
    have hdiv : (D32.toNat % 2 ^ (32 - k) * 2 ^ k + Qk V33.toNat D32.toNat k) / 2 ^ k
        = D32.toNat % 2 ^ (32 - k) := by
      rw [Nat.add_comm, Nat.mul_comm (D32.toNat % 2 ^ (32 - k)) (2 ^ k),
        Nat.add_mul_div_left _ _ h2k, Nat.div_eq_of_lt hQklt, Nat.zero_add]
    -- bit 31 of the quotient register is the next dividend bit
    have hbit : (bwsteps V33 k (0#33, D32)).2.toNat / 2 ^ 31 % 2 = bitConsumed D32.toNat k := by
      rw [ihQ]
      rw [two_pow_split2 k hk, ← Nat.div_div_eq_div_mul, hdiv, he,
        Nat.mod_mul_right_div_self]
      unfold bitConsumed
      omega
    -- the encoding for the quotient register advances correctly
    have hQmod : 2 * (bwsteps V33 k (0#33, D32)).2.toNat % 2 ^ 32
        = D32.toNat % 2 ^ (31 - k) * 2 ^ (k + 1) + 2 * Qk V33.toNat D32.toNat k := by
      have hB : 2 * (D32.toNat % 2 ^ (32 - k) * 2 ^ k) = D32.toNat % 2 ^ (32 - k) * 2 ^ (k + 1) := by
        rw [Nat.mul_comm 2 (D32.toNat % 2 ^ (32 - k) * 2 ^ k), Nat.mul_assoc, ← Nat.pow_succ]
      have hA : D32.toNat % 2 ^ (32 - k) * 2 ^ (k + 1)
          = D32.toNat % 2 ^ (31 - k) * 2 ^ (k + 1) + D32.toNat / 2 ^ (31 - k) % 2 * 2 ^ 32 := by
        have hms : D32.toNat % 2 ^ (32 - k)
            = D32.toNat % 2 ^ (31 - k) + 2 ^ (31 - k) * (D32.toNat / 2 ^ (31 - k) % 2) := by
          rw [he]; exact Nat.mod_mul
        rw [hms, Nat.add_mul]
        congr 1
        rw [Nat.mul_comm (2 ^ (31 - k)) (D32.toNat / 2 ^ (31 - k) % 2), Nat.mul_assoc,
          two_pow_split k hk]
      have hQbv2 : 2 * (bwsteps V33 k (0#33, D32)).2.toNat
          = D32.toNat % 2 ^ (31 - k) * 2 ^ (k + 1) + 2 * Qk V33.toNat D32.toNat k
            + D32.toNat / 2 ^ (31 - k) % 2 * 2 ^ 32 := by
        rw [ihQ, Nat.mul_add, hB, hA]; omega
      have hMlt : D32.toNat % 2 ^ (31 - k) * 2 ^ (k + 1) + 2 * Qk V33.toNat D32.toNat k < 2 ^ 32 := by
        have hAle : D32.toNat % 2 ^ (31 - k) ≤ 2 ^ (31 - k) - 1 := by
          have := Nat.mod_lt D32.toNat (Nat.two_pow_pos (31 - k)); omega
        have hAb : D32.toNat % 2 ^ (31 - k) * 2 ^ (k + 1) ≤ (2 ^ (31 - k) - 1) * 2 ^ (k + 1) :=
          Nat.mul_le_mul_right _ hAle
        have hsub : (2 ^ (31 - k) - 1) * 2 ^ (k + 1) = 2 ^ 32 - 2 ^ (k + 1) := by
          rw [Nat.sub_mul, Nat.one_mul, two_pow_split k hk]
        have h2Qk : 2 * Qk V33.toNat D32.toNat k < 2 ^ (k + 1) := by
          rw [Nat.pow_succ]; omega
        have hp : 0 < (2 : Nat) ^ (k + 1) := Nat.two_pow_pos _
        have hple : (2 : Nat) ^ (k + 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [hQbv2, Nat.mul_comm (D32.toNat / 2 ^ (31 - k) % 2) (2 ^ 32),
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hMlt]
    -- assemble the step via bwstep_toNat
    have hRltV : (bwsteps V33 k (0#33, D32)).1.toNat < V33.toNat := by rw [ihR]; exact hRklt
    obtain ⟨hsR, hsQ⟩ := bwstep_toNat V33 (bwsteps V33 k (0#33, D32)).1
      (bwsteps V33 k (0#33, D32)).2 hVpos hV32 hRltV
    have hunf : bwsteps V33 (k + 1) (0#33, D32)
        = bwstep V33 (bwsteps V33 k (0#33, D32)).1 (bwsteps V33 k (0#33, D32)).2 := rfl
    rw [hunf]
    refine ⟨?_, ?_⟩
    · rw [hsR, ihR, hbit]; simp only [Rk]
    · rw [hsQ, ihR, hbit, hQmod]
      have h32 : 32 - (k + 1) = 31 - k := by omega
      rw [h32]
      simp only [Qk]
      omega

/-- After all 32 working steps, the quotient register holds `D / V` and the
    remainder register holds `D % V`. -/
theorem bwsteps_32 (V33 : BitVec 33) (D32 : BitVec 32)
    (hVpos : 0 < V33.toNat) (hV32 : V33.toNat < 2 ^ 32) (hD : D32.toNat < 2 ^ 32) :
    (bwsteps V33 32 (0#33, D32)).1.toNat = D32.toNat % V33.toNat
    ∧ (bwsteps V33 32 (0#33, D32)).2.toNat = D32.toNat / V33.toNat := by
  obtain ⟨hR, hQ⟩ := bwsteps_enc V33 D32 hVpos hV32 hD 32 (by omega)
  obtain ⟨hRm, hQm⟩ := div_invariant_32 V33.toNat D32.toNat hVpos hD
  refine ⟨?_, ?_⟩
  · rw [hR, hRm]
  · rw [hQ, hQm]; simp [Nat.mod_one]

end Sparkle.Verification.Divider.BitProof
