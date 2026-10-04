/-
  Restoring division — the Nat-level invariant.

  This is the mathematical heart of the divider correctness proof, kept free of
  any `BitVec`/`Signal` reasoning.  We model one restoring-division step on plain
  naturals and prove the loop invariant by induction: after `k` steps the
  remainder is `D_k % V` and the quotient is `D_k / V`, where `D_k` is the top
  `k` bits of the dividend.  At `k = 32` this yields `D / V` and `D % V`.

  The `BitVec` working step refines `nstep`/`nqbit`; that refinement (a single
  fixed-width fact) plus this invariant gives the full divider correctness.
-/

set_option maxHeartbeats 400000

namespace Sparkle.Verification.Divider.Math

/-- One restoring-division remainder step: shift in bit `b`, trial-subtract `V`. -/
def nstep (V r b : Nat) : Nat := if V ≤ 2 * r + b then 2 * r + b - V else 2 * r + b

/-- The quotient bit produced by one step. -/
def nqbit (V r b : Nat) : Nat := if V ≤ 2 * r + b then 1 else 0

/-- The bit of `D` consumed at step `k` (0-indexed): bit `31-k`, MSB first. -/
def bitConsumed (D k : Nat) : Nat := (D / 2 ^ (31 - k)) % 2

/-- The top `k` bits of `D` as a number: `D / 2^(32-k)`. -/
def Dk (D k : Nat) : Nat := D / 2 ^ (32 - k)

/-- Remainder register value after `k` restoring-division steps. -/
def Rk (V D : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => nstep V (Rk V D k) (bitConsumed D k)

/-- Quotient register value after `k` restoring-division steps. -/
def Qk (V D : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * Qk V D k + nqbit V (Rk V D k) (bitConsumed D k)

-- ============================================================================
-- One-step facts
-- ============================================================================

theorem nstep_eq_mod (V r b : Nat) (hr : r < V) (hb : b < 2) :
    nstep V r b = (2 * r + b) % V := by
  unfold nstep
  by_cases h : V ≤ 2 * r + b
  · rw [if_pos h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem nqbit_eq_div (V r b : Nat) (hr : r < V) (hb : b < 2) (hV : 0 < V) :
    nqbit V r b = (2 * r + b) / V := by
  unfold nqbit
  by_cases h : V ≤ 2 * r + b
  · rw [if_pos h]
    have e : 2 * r + b = (2 * r + b - V) + V * 1 := by omega
    rw [e, Nat.add_mul_div_left _ _ hV, Nat.div_eq_of_lt (by omega)]
  · rw [if_neg h]
    exact (Nat.div_eq_of_lt (by omega)).symm

/-- `D_{k+1} = 2·D_k + (next bit)`. -/
theorem Dk_succ (D k : Nat) (hk : k ≤ 31) :
    Dk D (k + 1) = 2 * Dk D k + bitConsumed D k := by
  unfold Dk bitConsumed
  have e2 : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have h31 : 32 - (k + 1) = 31 - k := by omega
  rw [h31, e2, ← Nat.div_div_eq_div_mul]
  omega

-- ============================================================================
-- The loop invariant
-- ============================================================================

/-- **Restoring-division invariant.**  For a non-zero divisor `V` and a 32-bit
    dividend `D`, after `k ≤ 32` steps the remainder register holds `D_k % V`,
    the quotient register holds `D_k / V`, and the remainder is `< V`. -/
theorem div_invariant (V D : Nat) (hV : 0 < V) (hD : D < 2 ^ 32) :
    ∀ k, k ≤ 32 → Rk V D k = Dk D k % V ∧ Qk V D k = Dk D k / V ∧ Rk V D k < V := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : Dk D 0 = 0 := by unfold Dk; exact Nat.div_eq_of_lt hD
    refine ⟨?_, ?_, ?_⟩
    · simp [Rk, h0]
    · simp [Qk, h0]
    · simpa [Rk] using hV
  | succ k ih =>
    intro hk1
    have hk : k ≤ 31 := by omega
    obtain ⟨ihR, ihQ, ihRlt⟩ := ih (by omega)
    have hb : bitConsumed D k < 2 := by unfold bitConsumed; omega
    -- `2·D_k + b = (2·(D_k % V) + b) + V·(2·(D_k / V))`
    have key : 2 * Dk D k + bitConsumed D k
             = (2 * (Dk D k % V) + bitConsumed D k) + V * (2 * (Dk D k / V)) := by
      have hdm := Nat.div_add_mod (Dk D k) V
      have hc : V * (2 * (Dk D k / V)) = 2 * (V * (Dk D k / V)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm V 2, Nat.mul_assoc]
      omega
    have hcong : (2 * Dk D k + bitConsumed D k) % V
               = (2 * (Dk D k % V) + bitConsumed D k) % V := by
      -- `2·Dₖ ≡ 2·(Dₖ % V)` mod V: the `V·(2·(Dₖ/V))` term in `key` vanishes.
      rw [key]; exact Nat.add_mul_mod_self_left _ _ _
    have hR : Rk V D (k + 1) = Dk D (k + 1) % V := by
      simp only [Rk]
      rw [nstep_eq_mod V (Rk V D k) (bitConsumed D k) ihRlt hb, ihR, Dk_succ D k hk]
      exact hcong.symm
    have hQ : Qk V D (k + 1) = Dk D (k + 1) / V := by
      simp only [Qk]
      rw [ihQ, nqbit_eq_div V (Rk V D k) (bitConsumed D k) ihRlt hb hV, ihR,
          Dk_succ D k hk, key, Nat.add_mul_div_left _ _ hV]
      omega
    exact ⟨hR, hQ, by rw [hR]; exact Nat.mod_lt _ hV⟩

/-- At the end of all 32 steps: quotient = `D / V`, remainder = `D % V`. -/
theorem div_invariant_32 (V D : Nat) (hV : 0 < V) (hD : D < 2 ^ 32) :
    Rk V D 32 = D % V ∧ Qk V D 32 = D / V := by
  obtain ⟨hR, hQ, _⟩ := div_invariant V D hV hD 32 (by omega)
  have hD32 : Dk D 32 = D := by unfold Dk; simp
  rw [hD32] at hR hQ
  exact ⟨hR, hQ⟩

end Sparkle.Verification.Divider.Math
