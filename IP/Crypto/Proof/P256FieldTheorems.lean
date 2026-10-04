/-
  IP.Crypto.Proof.P256FieldTheorems — formal theorems that the
  pure-data field arithmetic in `IP.Crypto.P256Field` satisfies
  the axioms of the field F_p, where

    p = 2^256 - 2^224 + 2^192 + 2^96 - 1   (the NIST P-256 prime).

  These are the "数体系が満たすべき性質" (the algebraic laws the number
  system the HW datapath computes over must obey): commutativity,
  associativity, distributivity, units, and the range invariant.
  Every theorem is `∀`-quantified over ALL field elements (not a
  finite set of value vectors), proved by hand from `Nat` core
  lemmas about `(· % p)` — no mathlib, no `decide` over 256-bit
  values, no `sorry`.  Modeled on `Ed25519FieldTheorems`.

  The P-256 HW field multiplier (`P256FieldHW.mulHW`) computes
  `mul a b`; these theorems certify that the operation it
  implements is the F_p field operation, not just that it matches
  a few test vectors.

  NOT proved here (would need field primality / `ring`, i.e.
  mathlib — kept as simulation-validated assumptions, honestly,
  NOT `sorry`):
    * `mul a (inv a) = 1` for `a ≠ 0` (Fermat's little theorem —
      needs `p` prime).  `inv`'s correctness is validated by the
      simulation cross-checks in the P256 HW tests.
-/
import IP.Crypto.Proof.P256Field

namespace Sparkle.IP.Crypto.P256Field

/-! ### Basic facts about the prime p. -/

theorem p_pos : 0 < p := by unfold p; decide

theorem p_ne_zero : p ≠ 0 := Nat.pos_iff_ne_zero.mp p_pos

/-! ### Range invariant — `reduce` always returns a value in `[0, p)`. -/

theorem reduce_lt (n : Nat) : reduce n < p := by
  unfold reduce
  exact Nat.mod_lt n p_pos

theorem add_lt (a b : Nat) : add a b < p := reduce_lt _
theorem sub_lt (a b : Nat) : sub a b < p := by
  unfold sub
  split <;> exact reduce_lt _
theorem mul_lt (a b : Nat) : mul a b < p := reduce_lt _
theorem sq_lt  (a   : Nat) : sq  a   < p := reduce_lt _

/-! ### `reduce` is idempotent, and the identity on in-range values. -/

theorem reduce_reduce (n : Nat) : reduce (reduce n) = reduce n := by
  unfold reduce
  exact Nat.mod_mod n p

theorem reduce_lt_self (n : Nat) (h : n < p) : reduce n = n := by
  unfold reduce
  exact Nat.mod_eq_of_lt h

/-! ### Addition — commutativity, associativity, additive unit. -/

theorem add_comm (a b : Nat) : add a b = add b a := by
  unfold add reduce
  rw [Nat.add_comm]

theorem add_assoc (a b c : Nat) : add (add a b) c = add a (add b c) := by
  unfold add reduce
  rw [Nat.add_mod ((a + b) % p) c p, Nat.mod_mod,
      Nat.add_mod a ((b + c) % p) p, Nat.mod_mod,
      ← Nat.add_mod (a + b) c p, ← Nat.add_mod a (b + c) p,
      Nat.add_assoc]

theorem add_zero (a : Nat) (ha : a < p) : add a 0 = a := by
  unfold add reduce
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt ha

theorem zero_add (a : Nat) (ha : a < p) : add 0 a = a := by
  rw [add_comm]; exact add_zero a ha

/-! ### Multiplication — commutativity, associativity, unit, zero. -/

theorem mul_comm (a b : Nat) : mul a b = mul b a := by
  unfold mul reduce
  rw [Nat.mul_comm]

theorem mul_assoc (a b c : Nat) : mul (mul a b) c = mul a (mul b c) := by
  unfold mul reduce
  rw [Nat.mul_mod (a * b % p) c p, Nat.mod_mod,
      Nat.mul_mod a (b * c % p) p, Nat.mod_mod,
      ← Nat.mul_mod (a * b) c p, ← Nat.mul_mod a (b * c) p,
      Nat.mul_assoc]

theorem mul_one (a : Nat) (ha : a < p) : mul a 1 = a := by
  unfold mul reduce
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt ha

theorem one_mul (a : Nat) (ha : a < p) : mul 1 a = a := by
  rw [mul_comm]; exact mul_one a ha

theorem mul_zero (a : Nat) : mul a 0 = 0 := by
  unfold mul reduce
  rw [Nat.mul_zero, Nat.zero_mod]

theorem zero_mul (a : Nat) : mul 0 a = 0 := by
  rw [mul_comm]; exact mul_zero a

/-! ### Distributivity. -/

theorem mul_add (a b c : Nat) : mul a (add b c) = add (mul a b) (mul a c) := by
  unfold mul add reduce
  rw [Nat.mul_mod a ((b + c) % p) p, Nat.mod_mod,
      ← Nat.mul_mod a (b + c) p,
      Nat.add_mod (a * b % p) (a * c % p) p,
      Nat.mod_mod, Nat.mod_mod,
      ← Nat.add_mod (a * b) (a * c) p,
      Nat.mul_add]

theorem add_mul (a b c : Nat) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm (add a b) c, mul_add, mul_comm c a, mul_comm c b]

/-! ### Squaring and subtraction. -/

theorem sq_eq_mul_self (a : Nat) : sq a = mul a a := rfl

theorem sub_self (a : Nat) : sub a a = 0 := by
  unfold sub reduce
  have h : ¬ a < a := Nat.lt_irrefl a
  simp [h]

theorem sub_add_cancel (a b : Nat) (ha : a < p) (hab : b ≤ a) :
    add (sub a b) b = a := by
  unfold add sub reduce
  have hne : ¬ a < b := Nat.not_lt.mpr hab
  have h1 : a - b < p := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  rw [if_neg hne, Nat.mod_eq_of_lt h1, Nat.sub_add_cancel hab,
      Nat.mod_eq_of_lt ha]

end Sparkle.IP.Crypto.P256Field
