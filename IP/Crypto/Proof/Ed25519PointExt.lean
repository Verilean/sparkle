/-
  IP.Crypto.Ed25519PointExt — Ed25519 point arithmetic in
  **extended twisted-Edwards coordinates** (X : Y : Z : T),
  the HW-friendly form promised in `Ed25519Point` §L.3.b.

  An extended point (X, Y, Z, T) represents the affine point
  (X/Z, Y/Z) with the auxiliary invariant T = X·Y/Z (so
  X·Y = Z·T).  Identity is (0, 1, 1, 0).

  The twisted-Edwards curve is a = -1:  -x² + y² = 1 + d x² y².
  The unified addition (add-2008-hwcd-3) and doubling
  (dbl-2008-hwcd) formulas below use only field mul/add/sub —
  **no per-operation inversion**.  A whole scalar-multiply
  therefore needs a *single* final inverse (in `toAffine`),
  exactly the property that makes the HW datapath practical
  (cf. `Secp256k1PointJac` for the a = 0 Weierstrass analogue).

  Because Edwards addition is *complete* (correct for equal
  points and the identity), the scalar-mul ladder needs no
  special-case handling — simpler than the Weierstrass case.

  This is the pure-data reference the HW point-op / scalar-mul
  controllers drive and cross-check against.
-/

import IP.Crypto.Proof.Ed25519Field
import IP.Crypto.Proof.Ed25519Point

namespace Sparkle.IP.Crypto.Ed25519PointExt

abbrev fAdd := Sparkle.IP.Crypto.Ed25519Field.add
abbrev fSub := Sparkle.IP.Crypto.Ed25519Field.sub
abbrev fMul := Sparkle.IP.Crypto.Ed25519Field.mul
abbrev fSq  := Sparkle.IP.Crypto.Ed25519Field.sq
abbrev fInv := Sparkle.IP.Crypto.Ed25519Field.inv

/-- The curve constant d (shared with the affine reference). -/
abbrev d : Nat := Sparkle.IP.Crypto.Ed25519Point.d

/-- Extended twisted-Edwards point (X : Y : Z : T), affine
    (X/Z, Y/Z), with T = X·Y/Z. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
  deriving Repr

/-- The group identity (affine (0, 1)). -/
def identity : Point := { x := 0, y := 1, z := 1, t := 0 }

/-- Lift an affine (x, y) to extended coords (Z = 1, T = x·y). -/
def fromAffine (x y : Nat) : Point :=
  { x := x, y := y, z := 1, t := fMul x y }

/-- The base point B in extended coords. -/
def generator : Point :=
  fromAffine Sparkle.IP.Crypto.Ed25519Point.baseX
             Sparkle.IP.Crypto.Ed25519Point.baseY

/-- Unified addition, add-2008-hwcd-3 (a = -1):

      A = (Y1-X1)(Y2-X2)   B = (Y1+X1)(Y2+X2)
      C = 2·T1·d·T2        D = 2·Z1·Z2
      E = B-A   F = D-C   G = D+C   H = B+A
      X3 = E·F  Y3 = G·H  Z3 = F·G  T3 = E·H

    9 field multiplies; the ±/×2 are field add/sub. -/
def add (p1 p2 : Point) : Point :=
  let a := fMul (fSub p1.y p1.x) (fSub p2.y p2.x)
  let b := fMul (fAdd p1.y p1.x) (fAdd p2.y p2.x)
  let c := fMul (fAdd p1.t p1.t) (fMul d p2.t)      -- (2·T1)·(d·T2)
  let e0 := fMul p1.z p2.z
  let dd := fAdd e0 e0                               -- 2·Z1·Z2
  let e := fSub b a
  let f := fSub dd c
  let g := fAdd dd c
  let h := fAdd b a
  { x := fMul e f, y := fMul g h, z := fMul f g, t := fMul e h }

/-- Doubling, dbl-2008-hwcd (a = -1):

      A = X1²   B = Y1²   C = 2·Z1²   D = -A
      E = (X1+Y1)² - A - B   G = D+B   F = G-C   H = D-B
      X3 = E·F  Y3 = G·H  Z3 = F·G  T3 = E·H

    ~8 field multiplies. -/
def double (p : Point) : Point :=
  let a := fSq p.x
  let b := fSq p.y
  let z2 := fSq p.z
  let c := fAdd z2 z2                                -- 2·Z1²
  let dneg := fSub 0 a                              -- D = -A
  let xy := fAdd p.x p.y
  let e := fSub (fSub (fSq xy) a) b                 -- (X+Y)² - A - B
  let g := fAdd dneg b                              -- G = D+B
  let f := fSub g c                                 -- F = G-C
  let h := fSub dneg b                              -- H = D-B
  { x := fMul e f, y := fMul g h, z := fMul f g, t := fMul e h }

/-- Scalar multiplication via double-and-add (LSB-first).
    Addition is complete, so no special cases are needed. -/
def mulScalar (n : Nat) (p : Point) : Point := Id.run do
  let mut q := identity
  let mut acc := p
  let mut k := n
  while k > 0 do
    if k % 2 = 1 then
      q := add q acc
    acc := double acc
    k := k / 2
  return q

/-- Convert extended → affine (x, y).  This is the *single*
    field inversion of a whole scalar-multiply. -/
def toAffine (p : Point) : Nat × Nat :=
  let zi := fInv p.z
  (fMul p.x zi, fMul p.y zi)

/-- Point equality via affine normalisation. -/
def eq (p q : Point) : Bool :=
  toAffine p == toAffine q

end Sparkle.IP.Crypto.Ed25519PointExt
