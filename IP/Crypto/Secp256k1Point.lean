/-
  IP.Crypto.Secp256k1Point — short Weierstrass curve
  arithmetic for secp256k1.

  Curve: y² = x³ + 7  (mod p, where p is the secp256k1
  base-field prime).  The curve has order
    n = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE
        BAAEDCE6 AF48A03B BFD25E8C D0364141

  The Weierstrass curve has a genuine "point at infinity"
  (the group identity) — unlike twisted Edwards, where the
  identity is a normal affine point.  We represent it
  explicitly as `Point.infinity`.

  Affine pure-data reference.  HW projective/Jacobian-coords
  version follows in L.6.b.
-/

import IP.Crypto.Secp256k1Field

namespace Sparkle.IP.Crypto.Secp256k1Point

abbrev fAdd := Sparkle.IP.Crypto.Secp256k1Field.add
abbrev fSub := Sparkle.IP.Crypto.Secp256k1Field.sub
abbrev fMul := Sparkle.IP.Crypto.Secp256k1Field.mul
abbrev fSq  := Sparkle.IP.Crypto.Secp256k1Field.sq
abbrev fInv := Sparkle.IP.Crypto.Secp256k1Field.inv
abbrev fP   := Sparkle.IP.Crypto.Secp256k1Field.p

/-- A point on secp256k1: either the identity (∞) or an
    affine (x, y) pair with both ∈ Fp. -/
inductive Point
  | infinity
  | affine (x y : Nat)
  deriving DecidableEq, Repr

/-- The secp256k1 generator (well-known constants from
    SEC 2 §2.4.1). -/
def baseX : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def baseY : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def base : Point := .affine baseX baseY

/-- Curve order n. -/
def curveOrderN : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-! ### Group law in affine coordinates. -/

/-- Negation: -(x, y) = (x, -y). -/
def neg : Point → Point
  | .infinity      => .infinity
  | .affine x y    => .affine x (fSub 0 y)

/-- Point addition with full special-case handling
    (infinity, doubling, vertical-line). -/
def add (p1 p2 : Point) : Point :=
  match p1, p2 with
  | .infinity, _ => p2
  | _, .infinity => p1
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      -- Same x → either doubling or x-axis reflection.
      if y1 = y2 ∧ y1 ≠ 0 then
        -- Doubling: λ = (3 x² + a) / (2 y),  a = 0 for secp256k1
        let num := fMul 3 (fSq x1)
        let den := fMul 2 y1
        let lam := fMul num (fInv den)
        let x3 := fSub (fSq lam) (fMul 2 x1)
        let y3 := fSub (fMul lam (fSub x1 x3)) y1
        .affine x3 y3
      else
        -- y₁ = -y₂ (reflected) or y = 0 → infinity.
        .infinity
    else
      -- Generic add: λ = (y₂ - y₁) / (x₂ - x₁)
      let lam := fMul (fSub y2 y1) (fInv (fSub x2 x1))
      let x3 := fSub (fSub (fSq lam) x1) x2
      let y3 := fSub (fMul lam (fSub x1 x3)) y1
      .affine x3 y3

/-- Convenience doubling. -/
def double (p : Point) : Point := add p p

/-- Scalar multiplication via binary double-and-add. -/
def mulScalar (n : Nat) (p : Point) : Point := Id.run do
  let mut q : Point := .infinity
  let mut acc := p
  let mut k := n
  while k > 0 do
    if k % 2 = 1 then
      q := add q acc
    acc := double acc
    k := k / 2
  return q

/-- Curve membership: y² = x³ + 7 (mod p).  Returns true
    for the point at infinity. -/
def onCurve : Point → Bool
  | .infinity      => true
  | .affine x y =>
    let lhs := fSq y
    let rhs := fAdd (fMul x (fSq x)) 7
    decide (lhs = rhs)

end Sparkle.IP.Crypto.Secp256k1Point
