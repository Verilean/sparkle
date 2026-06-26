/-
  IP.Crypto.P256Point — short Weierstrass curve arithmetic
  for NIST P-256 (secp256r1).

  Curve: y² = x³ + a·x + b (mod p)
    a = -3            (= p - 3 in [0, p))
    b = 5AC635D8 AA3A93E7 B3EBBD55 7698 86BC
        651D06B0 CC53B0F6 3BCE3C3E 27D2604B
    p = 2^256 - 2^224 + 2^192 + 2^96 - 1
    n = FFFFFFFF 00000000 FFFFFFFF FFFFFFFF
        BCE6FAAD A7179E84 F3B9CAC2 FC632551
    G = (gx, gy) per SEC 2 §2.4.2.
-/

import IP.Crypto.P256Field

namespace Sparkle.IP.Crypto.P256Point

abbrev fAdd := Sparkle.IP.Crypto.P256Field.add
abbrev fSub := Sparkle.IP.Crypto.P256Field.sub
abbrev fMul := Sparkle.IP.Crypto.P256Field.mul
abbrev fSq  := Sparkle.IP.Crypto.P256Field.sq
abbrev fInv := Sparkle.IP.Crypto.P256Field.inv
abbrev fP   := Sparkle.IP.Crypto.P256Field.p

/-- Curve constant b. -/
def curveB : Nat :=
  0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B

/-- Curve constant a = -3 (= p - 3 in [0, p)). -/
def curveA : Nat := fP - 3

/-- P-256 generator. -/
def baseX : Nat :=
  0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
def baseY : Nat :=
  0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

inductive Point
  | infinity
  | affine (x y : Nat)
  deriving DecidableEq, Repr

def base : Point := .affine baseX baseY

/-- Order n of the base point. -/
def curveOrderN : Nat :=
  0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

def neg : Point → Point
  | .infinity      => .infinity
  | .affine x y    => .affine x (fSub 0 y)

/-- Point addition for short-Weierstrass with general `a`.
    Doubling slope: λ = (3·x² + a) / (2·y). -/
def add (p1 p2 : Point) : Point :=
  match p1, p2 with
  | .infinity, _ => p2
  | _, .infinity => p1
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if y1 = y2 ∧ y1 ≠ 0 then
        let num := fAdd (fMul 3 (fSq x1)) curveA
        let den := fMul 2 y1
        let lam := fMul num (fInv den)
        let x3 := fSub (fSq lam) (fMul 2 x1)
        let y3 := fSub (fMul lam (fSub x1 x3)) y1
        .affine x3 y3
      else
        .infinity
    else
      let lam := fMul (fSub y2 y1) (fInv (fSub x2 x1))
      let x3 := fSub (fSub (fSq lam) x1) x2
      let y3 := fSub (fMul lam (fSub x1 x3)) y1
      .affine x3 y3

def double (p : Point) : Point := add p p

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

/-- Curve membership: y² = x³ + a·x + b. -/
def onCurve : Point → Bool
  | .infinity      => true
  | .affine x y =>
    let lhs := fSq y
    let rhs := fAdd (fAdd (fMul x (fSq x)) (fMul curveA x)) curveB
    decide (lhs = rhs)

end Sparkle.IP.Crypto.P256Point
