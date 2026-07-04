/-
  IP.Crypto.Proof.P256PointTheorems — formal theorems that the
  pure-data P-256 elliptic-curve point arithmetic in
  `IP.Crypto.P256Point` satisfies the group laws it must.

  The P-256 HW scalar-multiplier / point-op (`P256ScalarMulHW`,
  `P256PointOpHW`) compute over the group E(F_p); these theorems
  certify the algebraic laws of that group, `∀`-quantified over
  ALL points — the "数体系が満たすべき性質" test, not value vectors.

  Proved here (cheap, definitional + the F_p field lemmas in
  `P256FieldTheorems`):
    * identity      : add ∞ P = P,  add P ∞ = P
    * double = P+P  : double P = add P P
    * neg on ∞      : neg ∞ = ∞
    * neg involutive: neg (neg P) = P   (for in-range coordinates)

  NOT proved here — these are large modular-polynomial identities
  in F_p that, without `ring`/mathlib, are infeasible by hand.
  They are validated by SIMULATION (the `P256PointJacTest`
  Jacobian-vs-affine cross-check and the `P256*HWTest` dataflow
  drivers), and are documented as such — NOT left as `sorry`:
    * commutativity  add P Q = add Q P   (slope/x3/y3 symmetry)
    * inverse        add P (neg P) = ∞   (branch + field facts)
    * closure        onCurve P → onCurve (double P)
    * associativity  add (add P Q) R = add P (add Q R)  (mathlib-scale)
    * full Jacobian ↔ affine equivalence for all inputs.
-/
import IP.Crypto.Proof.P256Point
import IP.Crypto.Proof.P256FieldTheorems

namespace Sparkle.IP.Crypto.P256Point

/-! ### Additive identity — ∞ is the group identity. -/

theorem add_infinity_left (P : Point) : add .infinity P = P := by
  cases P <;> rfl

theorem add_infinity_right (P : Point) : add P .infinity = P := by
  cases P <;> rfl

/-! ### Doubling is self-addition (definitional). -/

theorem double_eq_add_self (P : Point) : double P = add P P := rfl

/-! ### Negation. -/

theorem neg_infinity : neg .infinity = .infinity := rfl

/-- `neg` is an involution on affine points whose y-coordinate is
    in range `[0, p)`.  `neg (affine x y) = affine x (p - y mod p)`,
    and negating twice returns `y` when `y < p`.  Uses the F_p
    subtraction round-trip. -/
theorem neg_neg_affine (x y : Nat)
    (hy : y < Sparkle.IP.Crypto.P256Field.p) :
    neg (neg (.affine x y)) = .affine x y := by
  have h : Sparkle.IP.Crypto.P256Field.sub 0
             (Sparkle.IP.Crypto.P256Field.sub 0 y) = y := by
    unfold Sparkle.IP.Crypto.P256Field.sub Sparkle.IP.Crypto.P256Field.reduce
    have hp := Sparkle.IP.Crypto.P256Field.p_pos
    by_cases hy0 : y = 0
    · subst hy0; simp
    · have hpos : 0 < y := Nat.pos_of_ne_zero hy0
      -- inner: y > 0 ⇒ `if 0 < y` true ⇒ (0 + p - y) % p = p - y
      have hpy : Sparkle.IP.Crypto.P256Field.p - y
                   < Sparkle.IP.Crypto.P256Field.p := Nat.sub_lt hp hpos
      have hle : y ≤ Sparkle.IP.Crypto.P256Field.p := Nat.le_of_lt hy
      have e1 : (0 + Sparkle.IP.Crypto.P256Field.p - y)
                  % Sparkle.IP.Crypto.P256Field.p
                = Sparkle.IP.Crypto.P256Field.p - y := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hpy
      rw [if_pos hpos, e1]
      -- outer: p - y > 0 ⇒ if true ⇒ (0 + p - (p - y)) % p = y
      have hpyPos : 0 < Sparkle.IP.Crypto.P256Field.p - y :=
        Nat.sub_pos_of_lt hy
      have e2 : 0 + Sparkle.IP.Crypto.P256Field.p
                  - (Sparkle.IP.Crypto.P256Field.p - y) = y := by omega
      rw [if_pos hpyPos, e2, Nat.mod_eq_of_lt hy]
  show Point.affine x (fSub 0 (fSub 0 y)) = Point.affine x y
  simp only [fSub, h]

end Sparkle.IP.Crypto.P256Point
