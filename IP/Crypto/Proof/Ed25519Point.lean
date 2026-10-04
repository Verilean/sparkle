/-
  IP.Crypto.Ed25519Point — Edwards-curve point arithmetic
  over the prime field Fp25519.

  The Ed25519 curve in twisted Edwards form:
    -x² + y² = 1 + d · x² · y²
  with d = -121665 / 121666 mod p, p = 2^255 - 19.

  This file works in **affine coordinates** for clarity
  (point = pair of field elements (x, y) ∈ Fp × Fp).  Per-
  operation cost is dominated by a field inverse (Fermat
  powMod), so this is slow but correct — exactly what we
  need for sim-time validation against RFC 8032
  test vectors.

  A HW-friendly projective/extended-coords implementation
  follows in L.3.b once the affine reference is locked.
-/

import IP.Crypto.Proof.Ed25519Field

namespace Sparkle.IP.Crypto.Ed25519Point

/-- Local aliases for the field operations.  We don't
    `open Sparkle.IP.Crypto.Ed25519Field` because this
    namespace re-defines `add`, `sub`, `mul` at the
    point-arithmetic level, and the shadowing breaks
    the field-op call sites below.  Aliases keep the
    intent explicit. -/
abbrev fAdd := Sparkle.IP.Crypto.Ed25519Field.add
abbrev fSub := Sparkle.IP.Crypto.Ed25519Field.sub
abbrev fMul := Sparkle.IP.Crypto.Ed25519Field.mul
abbrev fSq  := Sparkle.IP.Crypto.Ed25519Field.sq
abbrev fInv := Sparkle.IP.Crypto.Ed25519Field.inv
abbrev fP   := Sparkle.IP.Crypto.Ed25519Field.p

/-- A point on the curve, in affine coordinates.  The
    identity element is `(0, 1)` (i.e. y = 1, x = 0). -/
structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

/-- The Ed25519 curve constant d = -121665 / 121666 mod p. -/
def d : Nat :=
  let dNum := fSub 0 121665   -- = p - 121665
  let dDen := 121666
  fMul dNum (fInv dDen)

/-- Identity element of the Edwards group: (0, 1). -/
def zero : Point := { x := 0, y := 1 }

/-- The base point B (generator) per RFC 8032 §5.1:
    B = (Bx, 4/5 mod p) where Bx is the unique x with
    x · 5 ≡ -4 mod p, even (x is the canonical sqrt by
    parity).

    Standard value (decimal):
      Bx = 15112221349535400772501151409588531511454012693041857206046113283949847762202
      By = 46316835694926478169428394003475163141307993866256225615783033603165251855960
-/
def baseX : Nat :=
  15112221349535400772501151409588531511454012693041857206046113283949847762202
def baseY : Nat :=
  46316835694926478169428394003475163141307993866256225615783033603165251855960

def base : Point := { x := baseX, y := baseY }

/-- Twisted-Edwards addition.  No special-case branches:
    formula is complete on the curve (Bernstein-Lange).

      x₃ = (x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂)
      y₃ = (y₁ y₂ + x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)

    where the leading sign comes from -x² + y² = ...
    (so the (y_1·y_2 + x_1·x_2) numerator).
-/
def add (p1 p2 : Point) : Point :=
  let x1 := p1.x
  let y1 := p1.y
  let x2 := p2.x
  let y2 := p2.y
  let x1y2 := fMul x1 y2
  let x2y1 := fMul x2 y1
  let y1y2 := fMul y1 y2
  let x1x2 := fMul x1 x2
  let dx1x2y1y2 := fMul d (fMul x1x2 y1y2)
  let numX := fAdd x1y2 x2y1
  let numY := fAdd y1y2 x1x2
  let denX := fAdd 1 dx1x2y1y2
  let denY := fSub 1 dx1x2y1y2
  { x := fMul numX (fInv denX)
  , y := fMul numY (fInv denY) }

/-- Point doubling = `add p p`.  Could be optimised with
    a dedicated formula; for the affine reference we keep
    it simple. -/
def double (p : Point) : Point := add p p

/-- Scalar multiplication via double-and-add over the
    binary expansion of `n`.  Bit-0 first (LSB). -/
def mulScalar (n : Nat) (p : Point) : Point := Id.run do
  let mut q := zero
  let mut acc := p
  let mut k := n
  while k > 0 do
    if k % 2 = 1 then
      q := add q acc
    acc := double acc
    k := k / 2
  return q

/-- Curve membership: -x² + y² = 1 + d x² y² (mod p). -/
def onCurve (pt : Point) : Bool :=
  let x2 := fSq pt.x
  let y2 := fSq pt.y
  let lhs := fAdd (fSub 0 x2) y2
  let rhs := fAdd 1 (fMul d (fMul x2 y2))
  decide (lhs = rhs)

/-! ### Point decompression (RFC 8032 §5.1.3).

    Given 32 little-endian bytes encoding y (low 255 bits)
    with the top bit of byte 31 holding x_0 (= parity of x),
    recover the full (x, y) point.

    For p = 2^255 - 19, p ≡ 5 (mod 8), so we can compute
    square roots via x = u·v³·(u·v⁷)^((p-5)/8) per RFC 8032
    §5.1.1, then fix parity.
-/

/-- I = 2^((p-1)/4) mod p — fourth root of unity.  Used to
    fix-up the square-root candidate when the first guess
    doesn't satisfy x² = a. -/
def fI : Nat :=
  Sparkle.IP.Crypto.Ed25519Field.powMod 2 ((Sparkle.IP.Crypto.Ed25519Field.p - 1) / 4)

/-- Recover the curve point from 32-byte little-endian
    encoding.  Returns `none` on:
      - non-canonical encoding (y ≥ p), or
      - no valid x (curve membership fails after candidate
        selection).
    Matches RFC 8032 §5.1.3 "Decoding". -/
def pointDecode (bytes : Array UInt8) : Option Point := Id.run do
  if bytes.size ≠ 32 then return none
  -- y is the low 255 bits, x_0 is bit 7 of byte 31.
  let mut yBytes := bytes
  let last := bytes[31]!.toNat
  let x0 := (last >>> 7) &&& 1
  yBytes := yBytes.set! 31 (UInt8.ofNat (last &&& 0x7F))
  -- Decode y as little-endian Nat.
  let mut y : Nat := 0
  for i in [:32] do
    y := y ||| (yBytes[i]!.toNat <<< (i * 8))
  -- Reject non-canonical y ≥ p.
  if y ≥ fP then return none
  -- u = y² - 1, v = d·y² + 1.
  let y2 := fSq y
  let u := fSub y2 1
  let v := fAdd (fMul d y2) 1
  -- Compute x = u · v³ · (u · v⁷)^((p-5)/8) per §5.1.1.
  let v2 := fSq v
  let v3 := fMul v v2
  let v7 := fMul v3 (fMul v3 v)
  let uv7 := fMul u v7
  let exp := (fP - 5) / 8
  let pow := Sparkle.IP.Crypto.Ed25519Field.powMod uv7 exp
  let mut x := fMul (fMul u v3) pow
  -- Check x² · v == u (mod p).  If x² · v == -u, multiply by I.
  let vx2 := fMul v (fSq x)
  if vx2 = u then
    pure ()
  else if vx2 = fSub 0 u then
    x := fMul x fI
  else
    return none
  -- Fix parity: if (x mod 2) ≠ x0, replace with -x.
  if x % 2 ≠ x0 then
    if x = 0 then return none  -- can't pick -0 with x0=1
    x := fSub 0 x
  return some { x := x, y := y }

end Sparkle.IP.Crypto.Ed25519Point
