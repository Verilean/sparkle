/-
  IP.Crypto.Secp256k1PointJac — secp256k1 group law in
  Jacobian coordinates (X, Y, Z), affine (X/Z², Y/Z³).

  Curve: y² = x³ + 7 (mod p).  secp256k1 is an a = 0 curve, so
  the standard a = 0 Jacobian doubling (dbl-2009-l) and addition
  (add-2007-bl) formulas apply unchanged — the curve constant `b`
  never appears in `double`/`add`.  These are the *same* formulas
  the BLS12-381 `G1` reference uses (also an a = 0 curve); only
  the field and the `onCurve` constant differ.

  Why this exists.  The affine reference `Secp256k1Point` calls a
  field inversion (`fInv`, a ~256-squaring Fermat exponentiation)
  inside *every* point add/double.  For a HW scalar-multiply that
  is ~256 × (add + double) inversions — the dominant cost.  In
  Jacobian coordinates add/double use only mul/sq/add/sub and
  **zero** inversions; a whole scalar-multiply needs a *single*
  final inversion in `toAffine`.  This is the pure-data reference
  the HW point-op / scalar-mul controllers drive and cross-check
  against.
-/

import IP.Crypto.Secp256k1Field

namespace Sparkle.IP.Crypto.Secp256k1PointJac

abbrev fAdd := Sparkle.IP.Crypto.Secp256k1Field.add
abbrev fSub := Sparkle.IP.Crypto.Secp256k1Field.sub
abbrev fMul := Sparkle.IP.Crypto.Secp256k1Field.mul
abbrev fSq  := Sparkle.IP.Crypto.Secp256k1Field.sq
abbrev fInv := Sparkle.IP.Crypto.Secp256k1Field.inv

/-- Jacobian point (X, Y, Z); affine (X/Z², Y/Z³).  `inf = true`
    marks the point at infinity (identity). -/
structure Point where
  x : Nat
  y : Nat
  z : Nat
  inf : Bool
  deriving Repr

/-- The group identity. -/
def infinity : Point := ⟨0, 1, 0, true⟩

/-- The secp256k1 generator (affine, Z = 1). -/
def baseX : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def baseY : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def generator : Point := ⟨baseX, baseY, 1, false⟩

/-- Curve order n. -/
def curveOrderN : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Jacobian point doubling for the a = 0 curve (y² = x³ + b).
    Formula dbl-2009-l. -/
def double (p : Point) : Point :=
  if p.inf || p.y = 0 then infinity
  else
    let a := fSq p.x                            -- A = X²
    let b := fSq p.y                            -- B = Y²
    let c := fSq b                              -- C = B²
    let xb := fAdd p.x b
    let d := fMul 2 (fSub (fSq xb) (fAdd a c))  -- D = 2((X+B)² - A - C)
    let e := fMul 3 a                           -- E = 3A
    let f := fSq e                              -- F = E²
    let x3 := fSub f (fMul 2 d)                 -- X' = F - 2D
    let y3 := fSub (fMul e (fSub d x3)) (fMul 8 c) -- Y' = E(D-X') - 8C
    let z3 := fMul 2 (fMul p.y p.z)             -- Z' = 2 Y Z
    ⟨x3, y3, z3, false⟩

/-- Jacobian point addition (generic, a = 0).  Formula
    add-2007-bl, with the u₁ = u₂ special-cases (double /
    infinity) handled explicitly. -/
def add (p q : Point) : Point :=
  if p.inf then q
  else if q.inf then p
  else
    let z1z1 := fSq p.z
    let z2z2 := fSq q.z
    let u1 := fMul p.x z2z2
    let u2 := fMul q.x z1z1
    let s1 := fMul p.y (fMul q.z z2z2)
    let s2 := fMul q.y (fMul p.z z1z1)
    if u1 = u2 then
      if s1 = s2 then double p else infinity
    else
      let h := fSub u2 u1
      let i := fSq (fMul 2 h)
      let j := fMul h i
      let rr := fMul 2 (fSub s2 s1)
      let v := fMul u1 i
      let x3 := fSub (fSub (fSq rr) j) (fMul 2 v)
      let y3 := fSub (fMul rr (fSub v x3)) (fMul 2 (fMul s1 j))
      let z3 := fMul (fSub (fSq (fAdd p.z q.z)) (fAdd z1z1 z2z2)) h
      ⟨x3, y3, z3, false⟩

/-- Scalar multiplication, double-and-add (LSB-first). -/
def mulScalar (n : Nat) (p : Point) : Point := Id.run do
  let mut acc := infinity
  let mut base := p
  let mut k := n
  while k > 0 do
    if k % 2 = 1 then
      acc := add acc base
    base := double base
    k := k / 2
  return acc

/-- Convert Jacobian → affine (x, y).  Returns (0, 0) for
    infinity.  This is the *single* field inversion of a whole
    scalar-multiply. -/
def toAffine (p : Point) : Nat × Nat :=
  if p.inf || p.z = 0 then (0, 0)
  else
    let zi := fInv p.z
    let zi2 := fSq zi
    let zi3 := fMul zi2 zi
    (fMul p.x zi2, fMul p.y zi3)

/-- Point equality via affine normalisation. -/
def eq (p q : Point) : Bool :=
  if p.inf || q.inf then p.inf == q.inf
  else toAffine p == toAffine q

/-- Curve membership on the affine representation: y² = x³ + 7. -/
def onCurve (p : Point) : Bool :=
  if p.inf then true
  else
    let (x, y) := toAffine p
    fSq y == fAdd (fMul x (fSq x)) 7

end Sparkle.IP.Crypto.Secp256k1PointJac
