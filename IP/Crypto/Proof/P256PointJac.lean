/-
  IP.Crypto.P256PointJac — NIST P-256 group law in Jacobian
  coordinates (X, Y, Z), affine (X/Z², Y/Z³).

  Curve: y² = x³ - 3·x + b (mod p).  P-256 is an a = -3 curve, so
  the a = 0 doubling used by `Secp256k1PointJac` does NOT apply.
  We use the a = -3 doubling (dbl-2001-b), where the doubling
  coefficient is

      M = 3·X² + a·Z⁴ = 3·X² - 3·Z⁴ = 3·(X - Z²)·(X + Z²)

  so that only the *difference/sum with Z²* is needed (no explicit
  Z⁴ multiply).  Addition (add-2007-bl) is curve-independent and is
  copied verbatim from the secp256k1 Jacobian reference.

  Why this exists.  The affine `P256Point` reference calls a field
  inversion inside every add/double; in Jacobian coordinates a
  whole scalar-multiply needs a *single* final inversion in
  `toAffine`.  This is the pure-data reference the HW point-op /
  scalar-mul controllers drive and cross-check against, and — most
  importantly — it LOCKS the a = -3 doubling formula (validated in
  `P256PointJacTest` against the trusted affine `P256Point`) before
  it is transcribed into the bit-serial hardware schedule.
-/

import IP.Crypto.Proof.P256Field
import IP.Crypto.Proof.P256Point

namespace Sparkle.IP.Crypto.P256PointJac

abbrev fAdd := Sparkle.IP.Crypto.P256Field.add
abbrev fSub := Sparkle.IP.Crypto.P256Field.sub
abbrev fMul := Sparkle.IP.Crypto.P256Field.mul
abbrev fSq  := Sparkle.IP.Crypto.P256Field.sq
abbrev fInv := Sparkle.IP.Crypto.P256Field.inv

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

/-- P-256 generator (affine, Z = 1). -/
def baseX : Nat := Sparkle.IP.Crypto.P256Point.baseX
def baseY : Nat := Sparkle.IP.Crypto.P256Point.baseY

def generator : Point := ⟨baseX, baseY, 1, false⟩

/-- Curve order n. -/
def curveOrderN : Nat := Sparkle.IP.Crypto.P256Point.curveOrderN

/-- Jacobian point doubling for the a = -3 curve (dbl-2001-b).

      delta = Z²
      gamma = Y²
      beta  = X·gamma
      alpha = 3·(X - delta)·(X + delta)      (= 3X² + a·Z⁴, a = -3)
      X3    = alpha² - 8·beta
      Z3    = (Y + Z)² - gamma - delta        (= 2·Y·Z)
      Y3    = alpha·(4·beta - X3) - 8·gamma²
-/
def double (p : Point) : Point :=
  if p.inf || p.y = 0 then infinity
  else
    let delta := fSq p.z                          -- Z²
    let gamma := fSq p.y                           -- Y²
    let beta  := fMul p.x gamma                    -- X·Y²
    let alpha := fMul 3 (fMul (fSub p.x delta) (fAdd p.x delta))  -- 3(X-Z²)(X+Z²)
    let x3    := fSub (fSq alpha) (fMul 8 beta)    -- α² - 8β
    let z3    := fSub (fSub (fSq (fAdd p.y p.z)) gamma) delta      -- (Y+Z)² - γ - δ
    let y3    := fSub (fMul alpha (fSub (fMul 4 beta) x3)) (fMul 8 (fSq gamma))
    ⟨x3, y3, z3, false⟩

/-- Jacobian point addition (generic, curve-independent).  Formula
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
    infinity.  The single field inversion of a whole
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

/-- Curve membership on the affine representation:
    y² = x³ - 3·x + b. -/
def onCurve (p : Point) : Bool :=
  if p.inf then true
  else
    let (x, y) := toAffine p
    fSq y == fAdd (fAdd (fMul x (fSq x)) (fMul Sparkle.IP.Crypto.P256Point.curveA x))
                  Sparkle.IP.Crypto.P256Point.curveB

end Sparkle.IP.Crypto.P256PointJac
