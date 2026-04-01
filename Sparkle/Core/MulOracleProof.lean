/-
  Carry-Save = Multiply: Full inductive proof (zero sorry)
-/
import Sparkle.Verification.MulProps
import Std.Tactic.BVDecide

open Sparkle.Verification.MulProps

private def sm (a b : BitVec 64) : Nat → BitVec 64
  | 0 => (0 : BitVec 64)
  | n + 1 => sm a b n + (if (a >>> n).getLsbD 0 then b <<< n else (0 : BitVec 64))

private theorem sm_cons (a b : BitVec 64) (n : Nat) :
    (if a.getLsbD 0 then b else (0 : BitVec 64)) +
    sm (a >>> 1) (b <<< 1) n = sm a b (n + 1) := by
  induction n with
  | zero => simp [sm]
  | succ n ih =>
    simp only [sm,
      show (a >>> 1) >>> n = a >>> (1 + n) from (BitVec.shiftRight_add a 1 n).symm,
      show (b <<< 1) <<< n = b <<< (1 + n) from (BitVec.shiftLeft_add b 1 n).symm,
      show 1 + n = n + 1 from by omega,
      show 1 + (n + 1) = (n + 1) + 1 from by omega]
    rw [← BitVec.add_assoc, ih, sm, BitVec.add_assoc]

private theorem csa_sum (n : Nat) (rd0 rdx0 a b : BitVec 64) :
    (carrySaveN n rd0 rdx0 a b).1 + (carrySaveN n rd0 rdx0 a b).2.1 =
    rd0 + rdx0 + sm a b n := by
  induction n generalizing rd0 rdx0 a b with
  | zero => simp [carrySaveN, sm]
  | succ n ih =>
    simp only [carrySaveN, carrySaveStep]
    rw [ih, carrySave_add_eq_64, ← sm_cons, ← BitVec.add_assoc,
        BitVec.add_assoc (rd0 + rdx0)]

-- Helper: m * x + y < 2*m when x ≤ 1 and y < m
private theorem bound_helper (m x y : Nat) (hx : x ≤ 1) (hy : y < m) (hm : 0 < m) :
    m * x + y < 2 * m := by
  cases x with
  | zero => simp [Nat.mul_zero]; omega
  | succ x =>
    have : x = 0 := by omega
    subst this; simp [Nat.mul_one]; omega

-- Helper: a % (2*m) = m*(a/m%2) + a%m
private theorem mod_double (a m : Nat) (hm : 0 < m) :
    a % (2 * m) = m * (a / m % 2) + a % m := by
  have hlt := bound_helper m (a/m%2) (a%m)
    (by have := Nat.mod_lt (a/m) (show 0 < 2 by omega); omega)
    (Nat.mod_lt a hm) hm
  have h1 := (Nat.div_add_mod a m).symm
  have h2 := (Nat.div_add_mod (a/m) 2).symm
  -- m*(a/m) = m*(2*q'+b) = 2*m*q' + m*b where q'=a/m/2, b=a/m%2
  have h3 : m * (a/m) = 2 * m * (a/m/2) + m * (a/m%2) := by
    have := congrArg (m * ·) h2
    -- this : m * (a/m) = m * (2*(a/m/2) + a/m%2)
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at this ⊢
    omega
  have h5 : a = 2 * m * (a/m/2) + (m * (a/m%2) + a%m) := by omega
  calc a % (2*m)
      = (2*m*(a/m/2) + (m*(a/m%2)+a%m)) % (2*m) := by rw [← h5]
    _ = (m*(a/m%2)+a%m) := by
        rw [Nat.add_comm (2*m*(a/m/2)), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

-- Helper: 2^(n+1) = 2 * 2^n
private theorem two_pow_succ (n : Nat) : 2^(n+1) = 2 * 2^n := by
  simp [Nat.pow_succ, Nat.mul_comm]

private theorem sm_eq_mul (a b : BitVec 64) : sm a b 64 = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul]
  suffices h : ∀ n : Nat, n ≤ 64 →
    (sm a b n).toNat = (a.toNat % 2^n) * b.toNat % 2^64 by
    have := h 64 (by omega); rw [this]
    have ha := a.isLt
    rw [Nat.mod_eq_of_lt ha]
  intro n
  induction n with
  | zero =>
    intro _; simp only [sm]
    have : a.toNat % 1 = 0 := by omega
    simp [BitVec.toNat_ofNat, this]
  | succ n ih =>
    intro hn; have ihv := ih (by omega)
    have ha := a.isLt; have hb := b.isLt
    simp only [sm, BitVec.toNat_add, ihv]
    split <;> rename_i hc
    · -- bit n is set: add b <<< n
      rw [BitVec.toNat_shiftLeft]
      have hmd := mod_double a.toNat (2^n) (Nat.two_pow_pos n)
      have hbit : a.toNat / 2^n % 2 = 1 := by
        have h := hc
        rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD] at h
        -- h : a.toNat.testBit n = true, i.e. (a>>>n).testBit 0 = true
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, bne_iff_ne] at h
        have hlt := Nat.mod_lt (a.toNat / 2^n) (show 0 < 2 by omega)
        omega
      rw [hbit, Nat.mul_one] at hmd
      -- Now hmd: a.toNat % (2*2^n) = 2^n + a.toNat%2^n
      rw [Nat.shiftLeft_eq, ← Nat.add_mod]
      -- Goal: (a%2^n*b + b*2^n) % 2^64 = a%2^(n+1)*b % 2^64
      have h1 : a.toNat % 2^n * b.toNat + b.toNat * 2^n =
          (a.toNat % 2^n + 2^n) * b.toNat := by
        rw [Nat.add_mul]; simp [Nat.mul_comm]
      rw [h1, show (2:Nat)^(n+1) = 2 * 2^n from two_pow_succ n]
      -- Goal: (a%2^n+2^n)*b%M = a%(2*2^n)*b%M
      -- hmd: a%(2*2^n) = 2^n + a%2^n
      have hmd' : a.toNat % (2*2^n) = a.toNat%2^n + 2^n := by omega
      rw [hmd']
    · -- bit n is clear: add 0
      have hbit : a.toNat / 2^n % 2 = 0 := by
        have h := hc
        rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD] at h
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, bne_iff_ne,
          Bool.not_eq_true'] at h
        have hlt := Nat.mod_lt (a.toNat / 2^n) (show 0 < 2 by omega)
        omega
      have hmd := mod_double a.toNat (2^n) (Nat.two_pow_pos n)
      rw [hbit, Nat.mul_zero] at hmd
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0, Nat.add_zero, Nat.mod_mod]
      have hmd' : a.toNat % (2*2^n) = a.toNat % 2^n := by omega
      have h2 : 2^(n+1) = 2 * 2^n := two_pow_succ n
      rw [h2, hmd']

set_option maxRecDepth 4096 in
theorem MulOracleProof.csa64_main (a b : BitVec 64) :
    let (rd, rdx, _, _) := carrySaveN 64 (0 : BitVec 64) (0 : BitVec 64) a b
    rd + rdx = a * b := by
  have h := csa_sum 64 (0 : BitVec 64) (0 : BitVec 64) a b
  -- h : rd + rdx = 0 + 0 + sm a b 64
  have hsm := sm_eq_mul a b
  -- hsm : sm a b 64 = a * b
  rw [hsm] at h
  simp at h
  exact h
