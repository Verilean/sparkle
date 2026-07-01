/-
  IP.Crypto.BLS12_381 — pure-data reference implementation of
  BLS signatures on the BLS12-381 pairing-friendly curve.

  BLS12-381 is the curve used by Ethereum 2.0 consensus
  (validator aggregate signatures), zk-rollup proof
  verification (Zcash Sapling, Filecoin), and threshold
  signature schemes.  This file is the load-bearing pure-data
  reference — NO `Signal` / `circuit do`.  (A HW module for the
  pairing — 381-bit modmul + Miller loop on an FPGA — is a
  research project and is explicitly OUT OF SCOPE.  BLS's value
  here is the verified reference + IP-catalog presence.)

  It is layered as a tower, each layer building on the last,
  mirroring `Ed25519Field → Ed25519Point → Ed25519Sign`:

    Fp    — prime field mod the 381-bit base prime p.
    Fp2   — quadratic extension Fp[u]/(u²+1).
    Fp6   — cubic  extension over Fp2, Fp2[v]/(v³-ξ), ξ = u+1.
    Fp12  — quadratic over Fp6, Fp6[w]/(w²-v).  This is GT.
    G1    — points on E(Fp): y² = x³ + 4.
    G2    — points on the twist E'(Fp2): y² = x³ + 4(u+1).
    Pairing — optimal ate: Miller loop + final exponentiation.
    Sign/Verify/Aggregate.

  Modelling choice (following Ed25519Field's idiom): field
  elements are `Nat` representatives in [0, p), reduced after
  each op.  This keeps the arithmetic and the round-trip test
  tractable at sim time (BitVec 384 would only add width
  bookkeeping without helping the proofs).

  Curve constants are the standard BLS12-381 parameters
  (draft-irtf-cfrg-pairing-friendly-curves / the zkcrypto
  `bls12_381` and `blst` references).
-/

import Sparkle
import IP.Crypto.SHA256

namespace Sparkle.IP.Crypto.BLS12_381

/-! ## Layer 1 — Fp, the 381-bit prime field. -/

namespace Fp

/-- The BLS12-381 base-field prime (381-bit):
    p = 0x1a0111ea397fe69a4b1ba7b6434bacd7 64774b84f38512bf 6730d2a0f6b0f624 1eabfffeb153ffff b9feffffffffaaab -/
def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

@[inline] def reduce (n : Nat) : Nat := n % p

@[inline] def ofNat (n : Nat) : Nat := reduce n

@[inline] def add (a b : Nat) : Nat := reduce (a + b)

@[inline] def sub (a b : Nat) : Nat :=
  if a < b then reduce (a + p - b) else reduce (a - b)

@[inline] def neg (a : Nat) : Nat := if a = 0 then 0 else p - reduce a

@[inline] def mul (a b : Nat) : Nat := reduce (a * b)

@[inline] def sq (a : Nat) : Nat := mul a a

/-- Square-and-multiply modular exponentiation. -/
def powMod (base exp : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := reduce base
  let mut e := exp
  while e > 0 do
    if e % 2 = 1 then
      result := mul result b
    b := sq b
    e := e / 2
  return result

/-- Fermat inverse: a^(p-2) ≡ a⁻¹ (mod p). -/
@[inline] def inv (a : Nat) : Nat := powMod a (p - 2)

end Fp

/-! ## Layer 2 — Fp2 = Fp[u]/(u²+1).

    Elements `(c0, c1)` denote `c0 + c1·u` with `u² = -1`. -/

namespace Fp2

/-- An Fp2 element `c0 + c1·u`. -/
structure El where
  c0 : Nat
  c1 : Nat
  deriving DecidableEq, Repr

def zero : El := ⟨0, 0⟩
def one  : El := ⟨1, 0⟩

/-- Embed an Fp scalar. -/
def ofFp (a : Nat) : El := ⟨Fp.reduce a, 0⟩

def add (a b : El) : El := ⟨Fp.add a.c0 b.c0, Fp.add a.c1 b.c1⟩
def sub (a b : El) : El := ⟨Fp.sub a.c0 b.c0, Fp.sub a.c1 b.c1⟩
def neg (a : El) : El := ⟨Fp.neg a.c0, Fp.neg a.c1⟩

/-- (a0 + a1 u)(b0 + b1 u) = (a0 b0 - a1 b1) + (a0 b1 + a1 b0) u,
    using u² = -1. -/
def mul (a b : El) : El :=
  let t0 := Fp.mul a.c0 b.c0
  let t1 := Fp.mul a.c1 b.c1
  let c0 := Fp.sub t0 t1
  let cross := Fp.mul (Fp.add a.c0 a.c1) (Fp.add b.c0 b.c1)
  let c1 := Fp.sub cross (Fp.add t0 t1)   -- a0b1 + a1b0
  ⟨c0, c1⟩

def sq (a : El) : El := mul a a

/-- Multiply by u+1 (= ξ, the Fp6 non-residue).
      (c0 + c1 u)(1 + u) = (c0 - c1) + (c0 + c1) u. -/
def mulByXi (a : El) : El :=
  ⟨Fp.sub a.c0 a.c1, Fp.add a.c0 a.c1⟩

/-- Conjugate: c0 - c1 u. -/
def conj (a : El) : El := ⟨a.c0, Fp.neg a.c1⟩

/-- Inverse: (c0 - c1 u)/(c0² + c1²). -/
def inv (a : El) : El :=
  let norm := Fp.add (Fp.sq a.c0) (Fp.sq a.c1)
  let ni := Fp.inv norm
  ⟨Fp.mul a.c0 ni, Fp.mul (Fp.neg a.c1) ni⟩

def scaleFp (a : El) (k : Nat) : El := ⟨Fp.mul a.c0 k, Fp.mul a.c1 k⟩

end Fp2

/-! ## Layer 3 — Fp6 = Fp2[v]/(v³-ξ), ξ = u+1.

    Elements `(c0, c1, c2)` denote `c0 + c1·v + c2·v²`. -/

namespace Fp6

abbrev E2 := Fp2.El

structure El where
  c0 : E2
  c1 : E2
  c2 : E2
  deriving DecidableEq, Repr

def zero : El := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
def one  : El := ⟨Fp2.one,  Fp2.zero, Fp2.zero⟩

def ofFp2 (a : E2) : El := ⟨a, Fp2.zero, Fp2.zero⟩

def add (a b : El) : El := ⟨Fp2.add a.c0 b.c0, Fp2.add a.c1 b.c1, Fp2.add a.c2 b.c2⟩
def sub (a b : El) : El := ⟨Fp2.sub a.c0 b.c0, Fp2.sub a.c1 b.c1, Fp2.sub a.c2 b.c2⟩
def neg (a : El) : El := ⟨Fp2.neg a.c0, Fp2.neg a.c1, Fp2.neg a.c2⟩

/-- Schoolbook Fp6 multiply with v³ = ξ = u+1 reduction. -/
def mul (a b : El) : El :=
  let a0 := a.c0; let a1 := a.c1; let a2 := a.c2
  let b0 := b.c0; let b1 := b.c1; let b2 := b.c2
  let v0 := Fp2.mul a0 b0
  let v1 := Fp2.mul a1 b1
  let v2 := Fp2.mul a2 b2
  -- c0 = v0 + ξ·((a1+a2)(b1+b2) - v1 - v2)
  let t0 := Fp2.sub (Fp2.mul (Fp2.add a1 a2) (Fp2.add b1 b2)) (Fp2.add v1 v2)
  let c0 := Fp2.add v0 (Fp2.mulByXi t0)
  -- c1 = (a0+a1)(b0+b1) - v0 - v1 + ξ·v2
  let t1 := Fp2.sub (Fp2.mul (Fp2.add a0 a1) (Fp2.add b0 b1)) (Fp2.add v0 v1)
  let c1 := Fp2.add t1 (Fp2.mulByXi v2)
  -- c2 = (a0+a2)(b0+b2) - v0 - v2 + v1
  let t2 := Fp2.sub (Fp2.mul (Fp2.add a0 a2) (Fp2.add b0 b2)) (Fp2.add v0 v2)
  let c2 := Fp2.add t2 v1
  ⟨c0, c1, c2⟩

def sq (a : El) : El := mul a a

/-- Multiply an Fp6 element by v (shift up one degree, wrap
    the v² coefficient into c0 via ξ). -/
def mulByV (a : El) : El :=
  ⟨Fp2.mulByXi a.c2, a.c0, a.c1⟩

/-- Inverse of an Fp6 element (standard cubic-extension formula). -/
def inv (a : El) : El :=
  let a0 := a.c0; let a1 := a.c1; let a2 := a.c2
  -- t0 = a0² - ξ·a1·a2
  let t0 := Fp2.sub (Fp2.sq a0) (Fp2.mulByXi (Fp2.mul a1 a2))
  -- t1 = ξ·a2² - a0·a1
  let t1 := Fp2.sub (Fp2.mulByXi (Fp2.sq a2)) (Fp2.mul a0 a1)
  -- t2 = a1² - a0·a2
  let t2 := Fp2.sub (Fp2.sq a1) (Fp2.mul a0 a2)
  -- factor = a0·t0 + ξ·(a2·t1 + a1·t2)
  let factor :=
    Fp2.add (Fp2.mul a0 t0)
      (Fp2.mulByXi (Fp2.add (Fp2.mul a2 t1) (Fp2.mul a1 t2)))
  let fi := Fp2.inv factor
  ⟨Fp2.mul t0 fi, Fp2.mul t1 fi, Fp2.mul t2 fi⟩

end Fp6

/-! ## Layer 4 — Fp12 = Fp6[w]/(w²-v).

    Elements `(c0, c1)` denote `c0 + c1·w` with `w² = v`.
    This is the pairing target group GT. -/

namespace Fp12

abbrev E6 := Fp6.El

structure El where
  c0 : E6
  c1 : E6
  deriving DecidableEq, Repr

def zero : El := ⟨Fp6.zero, Fp6.zero⟩
def one  : El := ⟨Fp6.one,  Fp6.zero⟩

def ofFp6 (a : E6) : El := ⟨a, Fp6.zero⟩

def add (a b : El) : El := ⟨Fp6.add a.c0 b.c0, Fp6.add a.c1 b.c1⟩
def sub (a b : El) : El := ⟨Fp6.sub a.c0 b.c0, Fp6.sub a.c1 b.c1⟩

/-- (a0 + a1 w)(b0 + b1 w) = (a0 b0 + v·a1 b1) + (a0 b1 + a1 b0) w,
    with w² = v. -/
def mul (a b : El) : El :=
  let v0 := Fp6.mul a.c0 b.c0
  let v1 := Fp6.mul a.c1 b.c1
  let c0 := Fp6.add v0 (Fp6.mulByV v1)
  let cross := Fp6.mul (Fp6.add a.c0 a.c1) (Fp6.add b.c0 b.c1)
  let c1 := Fp6.sub cross (Fp6.add v0 v1)
  ⟨c0, c1⟩

def sq (a : El) : El := mul a a

/-- Conjugate over the w-extension: c0 - c1 w. -/
def conj (a : El) : El := ⟨a.c0, Fp6.neg a.c1⟩

/-- Inverse: (c0 - c1 w) / (c0² - v·c1²). -/
def inv (a : El) : El :=
  let c0sq := Fp6.sq a.c0
  let c1sq := Fp6.sq a.c1
  let factor := Fp6.sub c0sq (Fp6.mulByV c1sq)
  let fi := Fp6.inv factor
  ⟨Fp6.mul a.c0 fi, Fp6.mul (Fp6.neg a.c1) fi⟩

/-- Fp12 exponentiation by a Nat exponent (square-and-multiply). -/
def pow (a : El) (exp : Nat) : El := Id.run do
  let mut result := one
  let mut b := a
  let mut e := exp
  while e > 0 do
    if e % 2 = 1 then
      result := mul result b
    b := sq b
    e := e / 2
  return result

end Fp12

/-! ## Curve group order and BLS loop parameter. -/

/-- The subgroup order r (= scalar-field prime) of both G1 and G2. -/
def r : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The BLS12-381 loop parameter x = -0xd201000000010000 (the
    absolute value).  Informational: the Miller loop below
    iterates the `pseudoBinaryEncoding` of |x| (see
    `Pairing.millerLoop`), matching py_ecc; no explicit sign
    correction is applied — the final exponentiation absorbs it. -/
def absX : Nat := 0xd201000000010000

/-! ## Layer 5 — G1: E(Fp): y² = x³ + 4, Jacobian coordinates. -/

namespace G1

/-- Jacobian point (X, Y, Z); affine (X/Z², Y/Z³).  `inf = true`
    marks the point at infinity (identity). -/
structure Point where
  x : Nat
  y : Nat
  z : Nat
  inf : Bool
  deriving Repr

def infinity : Point := ⟨0, 1, 0, true⟩

/-- The standard G1 generator (affine), Z = 1. -/
def genX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
def genY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

def generator : Point := ⟨genX, genY, 1, false⟩

/-- Jacobian point doubling for a = 0 curve (y² = x³ + b). -/
def double (p : Point) : Point :=
  if p.inf || p.y = 0 then infinity
  else
    let a := Fp.sq p.x                        -- A = X²
    let b := Fp.sq p.y                        -- B = Y²
    let c := Fp.sq b                          -- C = B²
    let xb := Fp.add p.x b
    let d := Fp.mul 2 (Fp.sub (Fp.sq xb) (Fp.add a c))   -- D = 2((X+B)² - A - C)
    let e := Fp.mul 3 a                       -- E = 3A
    let f := Fp.sq e                          -- F = E²
    let x3 := Fp.sub f (Fp.mul 2 d)           -- X' = F - 2D
    let y3 := Fp.sub (Fp.mul e (Fp.sub d x3)) (Fp.mul 8 c) -- Y' = E(D-X') - 8C
    let z3 := Fp.mul 2 (Fp.mul p.y p.z)       -- Z' = 2 Y Z
    ⟨x3, y3, z3, false⟩

/-- Jacobian point addition (generic, a = 0). -/
def add (p q : Point) : Point :=
  if p.inf then q
  else if q.inf then p
  else
    let z1z1 := Fp.sq p.z
    let z2z2 := Fp.sq q.z
    let u1 := Fp.mul p.x z2z2
    let u2 := Fp.mul q.x z1z1
    let s1 := Fp.mul p.y (Fp.mul q.z z2z2)
    let s2 := Fp.mul q.y (Fp.mul p.z z1z1)
    if u1 = u2 then
      if s1 = s2 then double p else infinity
    else
      let h := Fp.sub u2 u1
      let i := Fp.sq (Fp.mul 2 h)
      let j := Fp.mul h i
      let rr := Fp.mul 2 (Fp.sub s2 s1)
      let v := Fp.mul u1 i
      let x3 := Fp.sub (Fp.sub (Fp.sq rr) j) (Fp.mul 2 v)
      let y3 := Fp.sub (Fp.mul rr (Fp.sub v x3)) (Fp.mul 2 (Fp.mul s1 j))
      let z3 := Fp.mul (Fp.sub (Fp.sq (Fp.add p.z q.z)) (Fp.add z1z1 z2z2)) h
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

/-- Convert Jacobian → affine (x, y).  Returns (0,0) for infinity. -/
def toAffine (p : Point) : Nat × Nat :=
  if p.inf || p.z = 0 then (0, 0)
  else
    let zi := Fp.inv p.z
    let zi2 := Fp.sq zi
    let zi3 := Fp.mul zi2 zi
    (Fp.mul p.x zi2, Fp.mul p.y zi3)

/-- Point equality via affine normalisation. -/
def eq (p q : Point) : Bool :=
  if p.inf || q.inf then p.inf == q.inf
  else toAffine p == toAffine q

/-- Curve membership check on the affine representation:
    y² = x³ + 4. -/
def onCurve (p : Point) : Bool :=
  if p.inf then true
  else
    let (x, y) := toAffine p
    Fp.sq y == Fp.add (Fp.mul x (Fp.sq x)) 4

end G1

/-! ## Layer 6 — G2: E'(Fp2): y² = x³ + 4(u+1). -/

namespace G2

abbrev E2 := Fp2.El

structure Point where
  x : E2
  y : E2
  z : E2
  inf : Bool
  deriving Repr

def infinity : Point := ⟨Fp2.one, Fp2.one, Fp2.zero, true⟩

/-- b' = 4(u+1) on the twist. -/
def bTwist : E2 := ⟨4, 4⟩

/-- The standard G2 generator (affine), Z = 1.  Coordinates are
    Fp2 elements (c0 + c1 u). -/
def genX : E2 :=
  ⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
   0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩
def genY : E2 :=
  ⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
   0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩

def generator : Point := ⟨genX, genY, Fp2.one, false⟩

/-- Jacobian doubling over Fp2 (a = 0). -/
def double (p : Point) : Point :=
  if p.inf || p.y = Fp2.zero then infinity
  else
    let a := Fp2.sq p.x
    let b := Fp2.sq p.y
    let c := Fp2.sq b
    let xb := Fp2.add p.x b
    let d := Fp2.scaleFp (Fp2.sub (Fp2.sq xb) (Fp2.add a c)) 2
    let e := Fp2.scaleFp a 3
    let f := Fp2.sq e
    let x3 := Fp2.sub f (Fp2.scaleFp d 2)
    let y3 := Fp2.sub (Fp2.mul e (Fp2.sub d x3)) (Fp2.scaleFp c 8)
    let z3 := Fp2.scaleFp (Fp2.mul p.y p.z) 2
    ⟨x3, y3, z3, false⟩

def add (p q : Point) : Point :=
  if p.inf then q
  else if q.inf then p
  else
    let z1z1 := Fp2.sq p.z
    let z2z2 := Fp2.sq q.z
    let u1 := Fp2.mul p.x z2z2
    let u2 := Fp2.mul q.x z1z1
    let s1 := Fp2.mul p.y (Fp2.mul q.z z2z2)
    let s2 := Fp2.mul q.y (Fp2.mul p.z z1z1)
    if u1 = u2 then
      if s1 = s2 then double p else infinity
    else
      let h := Fp2.sub u2 u1
      let i := Fp2.sq (Fp2.scaleFp h 2)
      let j := Fp2.mul h i
      let rr := Fp2.scaleFp (Fp2.sub s2 s1) 2
      let v := Fp2.mul u1 i
      let x3 := Fp2.sub (Fp2.sub (Fp2.sq rr) j) (Fp2.scaleFp v 2)
      let y3 := Fp2.sub (Fp2.mul rr (Fp2.sub v x3)) (Fp2.scaleFp (Fp2.mul s1 j) 2)
      let z3 := Fp2.mul (Fp2.sub (Fp2.sq (Fp2.add p.z q.z)) (Fp2.add z1z1 z2z2)) h
      ⟨x3, y3, z3, false⟩

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

/-- Affine (x, y) as Fp2 pair; (0,0) for infinity. -/
def toAffine (p : Point) : E2 × E2 :=
  if p.inf || p.z = Fp2.zero then (Fp2.zero, Fp2.zero)
  else
    let zi := Fp2.inv p.z
    let zi2 := Fp2.sq zi
    let zi3 := Fp2.mul zi2 zi
    (Fp2.mul p.x zi2, Fp2.mul p.y zi3)

def eq (p q : Point) : Bool :=
  if p.inf || q.inf then p.inf == q.inf
  else toAffine p == toAffine q

/-- Curve membership on the twist: y² = x³ + 4(u+1). -/
def onCurve (p : Point) : Bool :=
  if p.inf then true
  else
    let (x, y) := toAffine p
    Fp2.sq y == Fp2.add (Fp2.mul x (Fp2.sq x)) bTwist

end G2

/-! ## Layer 7 — Optimal ate pairing.

    Straightforward (unoptimised) Miller loop over the BLS loop
    parameter, followed by the full final exponentiation
    e = (p^12 - 1)/r.  Correctness, not speed, is the goal.

    IMPLEMENTATION APPROACH (verified against py_ecc's
    `optimized_bls12_381`):  rather than hand-place sparse line
    coefficients into Fp12 (the classic bug source), we UNTWIST
    the running G2 point into a full point of E(Fp12) and run a
    single GENERIC homogeneous-projective line function entirely
    in Fp12 arithmetic.  The line function returns a
    (numerator, denominator) pair so the whole Miller loop needs
    zero Fp12 inversions; we divide once at the end.

    Untwisting isomorphism (D-type twist, standard tower
    Fp12 = Fp6[w]/(w²-v), Fp6 = Fp2[v]/(v³-ξ)):
      ψ(x', y') = (x'·w², y'·w³)
    so x' lands in the Fp6-c1 (v) slot of Fp12's c0, and y' in
    the Fp6-c1 (v) slot of Fp12's c1.

    Sign of the loop parameter: py_ecc iterates the positive
    magnitude and applies NO sign correction, letting the naive
    (p^12-1)/r final exponentiation absorb it.  This yields a
    bilinear, non-degenerate pairing — exactly what
    sign/verify/aggregate self-consistency needs. -/

namespace Pairing

abbrev E2 := Fp2.El
abbrev E12 := Fp12.El

/-- Homogeneous-projective point over Fp12 (X : Y : Z). -/
structure P12 where
  x : E12
  y : E12
  z : E12

/-- Embed a G1 affine point (xP, yP) ∈ Fp × Fp into Fp12 as a
    projective point with Z = 1.  Both coords sit in the base
    (real) slot. -/
def embedG1 (px py : Nat) : P12 :=
  let xe : E12 := ⟨⟨Fp2.ofFp px, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩
  let ye : E12 := ⟨⟨Fp2.ofFp py, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩
  ⟨xe, ye, Fp12.one⟩

/-- The Fp12 generator `w` (= 0 + 1·w). -/
def wElt : E12 := ⟨Fp6.zero, Fp6.one⟩

/-- Untwist a G2 affine point (x', y') ∈ Fp2 × Fp2 into a
    projective point of E(Fp12) with Z = 1.

    BLS12-381 uses the D-type twist with twist-curve constant
    b' = 4(u+1) = 4ξ.  For this twist the untwisting isomorphism
    E'(Fp2) → E(Fp12) [where E : y² = x³ + 4] is
      ψ(x', y') = (x'·w⁻², y'·w⁻³),
    since (y'w⁻³)² = (x'w⁻²)³ + 4  ⟺  y'² = x'³ + 4·w⁶ = x'³ + 4ξ.
    We embed x', y' into the Fp12 base slot and multiply by the
    (precomputed) inverse powers of w. -/
def untwist (xq yq : E2) : P12 :=
  let xEmb : E12 := ⟨Fp6.ofFp2 xq, Fp6.zero⟩
  let yEmb : E12 := ⟨Fp6.ofFp2 yq, Fp6.zero⟩
  let w2 := Fp12.mul wElt wElt
  let w3 := Fp12.mul w2 wElt
  let xe := Fp12.mul xEmb (Fp12.inv w2)
  let ye := Fp12.mul yEmb (Fp12.inv w3)
  ⟨xe, ye, Fp12.one⟩

/-- Generic homogeneous-projective line function over Fp12.
    Evaluates the line through P1, P2 (or tangent at P1 when
    P1 = P2) at the point T, returning (numerator, denominator)
    both in Fp12.  Direct transcription of py_ecc's `linefunc`.
    Curve constant `b` does not appear (a = 0 curve). -/
def linefunc (P1 P2 T : P12) : E12 × E12 :=
  let x1 := P1.x; let y1 := P1.y; let z1 := P1.z
  let x2 := P2.x; let y2 := P2.y; let z2 := P2.z
  let xt := T.x;  let yt := T.y;  let zt := T.z
  let mNum0 := Fp12.sub (Fp12.mul y2 z1) (Fp12.mul y1 z2)
  let mDen0 := Fp12.sub (Fp12.mul x2 z1) (Fp12.mul x1 z2)
  -- xt·z1 - x1·zt  and  yt·z1 - y1·zt (shared subexpressions).
  let sx := Fp12.sub (Fp12.mul xt z1) (Fp12.mul x1 zt)
  let sy := Fp12.sub (Fp12.mul yt z1) (Fp12.mul y1 zt)
  if mDen0 ≠ Fp12.zero then
    -- add / chord
    let num := Fp12.sub (Fp12.mul mNum0 sx) (Fp12.mul mDen0 sy)
    let den := Fp12.mul mDen0 (Fp12.mul zt z1)
    (num, den)
  else if mNum0 = Fp12.zero then
    -- double / tangent: m = 3·x1² / (2·y1·z1)
    let mNum := Fp12.mul ⟨⟨⟨3, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩ (Fp12.mul x1 x1)
    let mDen := Fp12.mul ⟨⟨⟨2, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩ (Fp12.mul y1 z1)
    let num := Fp12.sub (Fp12.mul mNum sx) (Fp12.mul mDen sy)
    let den := Fp12.mul mDen (Fp12.mul zt z1)
    (num, den)
  else
    -- vertical line (P1 = -P2)
    (sx, Fp12.mul z1 zt)

/-- Projective doubling over Fp12 (a = 0 curve, y²z = x³ + b z³).
    Standard homogeneous doubling; used to advance the running
    untwisted point. -/
def double12 (P : P12) : P12 :=
  let x := P.x; let y := P.y; let z := P.z
  let w := Fp12.mul ⟨⟨⟨3, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩ (Fp12.mul x x)  -- W = 3X²
  let s := Fp12.mul y z                                                      -- S = Y Z
  let b := Fp12.mul x (Fp12.mul y s)                                         -- B = X Y S
  let eight := ⟨⟨⟨8, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩
  let four  := ⟨⟨⟨4, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩
  let two   := ⟨⟨⟨2, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩
  let h := Fp12.sub (Fp12.mul w w) (Fp12.mul eight b)                        -- H = W² - 8B
  let sSq := Fp12.mul s s
  let xNew := Fp12.mul two (Fp12.mul h s)                                    -- X' = 2 H S
  -- Y' = W(4B - H) - 8 Y² S²
  let yNew := Fp12.sub (Fp12.mul w (Fp12.sub (Fp12.mul four b) h))
                (Fp12.mul eight (Fp12.mul (Fp12.mul y y) sSq))
  let zNew := Fp12.mul eight (Fp12.mul s sSq)                                -- Z' = 8 S³
  ⟨xNew, yNew, zNew⟩

/-- Projective addition over Fp12 (a = 0 curve). -/
def add12 (P Q : P12) : P12 :=
  let x1 := P.x; let y1 := P.y; let z1 := P.z
  let x2 := Q.x; let y2 := Q.y; let z2 := Q.z
  let u := Fp12.sub (Fp12.mul y2 z1) (Fp12.mul y1 z2)     -- U = Y2 Z1 - Y1 Z2
  let v := Fp12.sub (Fp12.mul x2 z1) (Fp12.mul x1 z2)     -- V = X2 Z1 - X1 Z2
  let vSq := Fp12.mul v v
  let vCube := Fp12.mul vSq v
  let w := Fp12.mul z1 z2
  let two := ⟨⟨⟨2, 0⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩
  -- A = U² W - V³ - 2 V² X1 Z2
  let a := Fp12.sub (Fp12.sub (Fp12.mul (Fp12.mul u u) w) vCube)
             (Fp12.mul two (Fp12.mul vSq (Fp12.mul x1 z2)))
  let xNew := Fp12.mul v a
  -- Y' = U(V² X1 Z2 - A) - V³ Y1 Z2
  let yNew := Fp12.sub (Fp12.mul u (Fp12.sub (Fp12.mul vSq (Fp12.mul x1 z2)) a))
                (Fp12.mul vCube (Fp12.mul y1 z2))
  let zNew := Fp12.mul vCube w
  ⟨xNew, yNew, zNew⟩

/-- The BLS12-381 ate-loop `pseudo_binary_encoding` (64 entries,
    little-endian, entries ∈ {0,1}), verbatim from py_ecc's
    `optimized_bls12_381`.  The Miller loop iterates entries
    62..0 (i.e. `[62::-1]`). -/
def pseudoBinaryEncoding : Array Nat := #[
  0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
  1,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
  1,0,0,0,0,0,0,0, 0,1,0,0,1,0,1,1]

/-- Miller loop, transcribed line-for-line from py_ecc's
    `miller_loop`.  P ∈ G1, Q ∈ G2.  The running point R stays
    in G2 (Jacobian) and is untwisted to Fp12 (via its affine
    form, Z = 1) for each line evaluation.  Accumulates
    numerator and denominator separately, divides once. -/
def millerLoop (P : G1.Point) (Q : G2.Point) : Fp12.El := Id.run do
  let (px, py) := G1.toAffine P
  let castP := embedG1 px py
  let untwistPt := fun (pt : G2.Point) =>
    let (ax, ay) := G2.toAffine pt
    untwist ax ay
  let twistQ := untwistPt Q
  let mut fNum := Fp12.one
  let mut fDen := Fp12.one
  let mut R := Q
  let mut twistR := twistQ
  -- Iterate pseudo_binary_encoding[62::-1] = indices 62 down to 0.
  for i in [:63] do
    let v := pseudoBinaryEncoding.getD (62 - i) 0
    -- DOUBLE step
    let (n, d) := linefunc twistR twistR castP
    fNum := Fp12.mul (Fp12.mul fNum fNum) n
    fDen := Fp12.mul (Fp12.mul fDen fDen) d
    R := G2.double R
    twistR := untwistPt R
    if v == 1 then
      -- ADD step
      let (n2, d2) := linefunc twistR twistQ castP
      fNum := Fp12.mul fNum n2
      fDen := Fp12.mul fDen d2
      R := G2.add R Q
      twistR := untwistPt R
  return Fp12.mul fNum (Fp12.inv fDen)

/-- Final exponentiation: raise to (p^12 - 1)/r via naive
    square-and-multiply.  Slow but correct — the
    reference-implementation trade-off. -/
def finalExp (f : Fp12.El) : Fp12.El :=
  let exp := (Fp.p ^ 12 - 1) / r
  Fp12.pow f exp

/-- The optimal ate pairing e(P, Q), P ∈ G1, Q ∈ G2.  Following
    py_ecc: loop over the positive magnitude, no sign correction,
    then final exponentiation. -/
def pairing (P : G1.Point) (Q : G2.Point) : Fp12.El :=
  if P.inf || Q.inf then Fp12.one
  else finalExp (millerLoop P Q)

end Pairing

/-! ## Layer 8 — Hash-to-curve, Sign, Verify, Aggregate.

    HASH-TO-CURVE CHOICE (be explicit): this reference uses a
    SIMPLE, DETERMINISTIC placeholder `hashToG2` rather than the
    full RFC 9380 `hash_to_curve` suite
    (`BLS12381G2_XMD:SHA-256_SSWU_RO_`).  We DO build a real
    RFC 9380 §5.3 `expand_message_xmd` (SHA-256) to derive a
    uniform scalar from the message, then map it onto G2 as
    `t · G2.generator`.

    This is NOT the standard encoding — a spec-compliant
    implementation needs the SSWU map + isogeny + cofactor
    clearing.  But it IS a deterministic map ByteArray → G2 that
    lands in the correct prime-order subgroup, which is exactly
    what sign/verify/aggregate need to be *self-consistent*
    (e(g1, sk·H(m)) = e(sk·g1, H(m))).  The pairing check below
    is fully real; only the message→point encoding is
    simplified.  A follow-up can drop in the SSWU map without
    touching sign/verify. -/

open Sparkle.IP.Crypto.SHA256 (sha256OfBytes)

/-- SHA-256 of a byte array → 32-byte digest. -/
def sha256Bytes (input : Array UInt8) : Array UInt8 := Id.run do
  let words := sha256OfBytes input
  let mut out : Array UInt8 := #[]
  for w in words do
    for i in [:4] do
      let shift := (3 - i) * 8
      out := out.push (UInt8.ofNat ((w.toNat >>> shift) &&& 0xFF))
  return out

/-- RFC 9380 §5.3 `expand_message_xmd` with SHA-256.
    Produces `lenInBytes` pseudo-random bytes from `msg` and a
    domain-separation tag `dst`. -/
def expandMessageXmd (msg : Array UInt8) (dst : Array UInt8)
    (lenInBytes : Nat) : Array UInt8 := Id.run do
  let bInBytes := 32          -- SHA-256 output size
  let sInBytes := 64          -- SHA-256 block size
  let ell := (lenInBytes + bInBytes - 1) / bInBytes
  -- DST_prime = DST || I2OSP(len(DST), 1)
  let dstPrime := dst.push (UInt8.ofNat dst.size)
  -- Z_pad = I2OSP(0, s_in_bytes)
  let zPad : Array UInt8 := Array.replicate sInBytes 0
  -- l_i_b_str = I2OSP(len_in_bytes, 2)
  let libStr : Array UInt8 :=
    #[UInt8.ofNat ((lenInBytes >>> 8) &&& 0xFF), UInt8.ofNat (lenInBytes &&& 0xFF)]
  -- b_0 = H(Z_pad || msg || l_i_b_str || I2OSP(0,1) || DST_prime)
  let b0Input := zPad ++ msg ++ libStr ++ #[(0 : UInt8)] ++ dstPrime
  let b0 := sha256Bytes b0Input
  -- b_1 = H(b_0 || I2OSP(1,1) || DST_prime)
  let mut bPrev := sha256Bytes (b0 ++ #[(1 : UInt8)] ++ dstPrime)
  let mut uniform := bPrev
  for i in [2:ell+1] do
    -- b_i = H((b_0 XOR b_{i-1}) || I2OSP(i,1) || DST_prime)
    let mut xored : Array UInt8 := #[]
    for j in [:bInBytes] do
      xored := xored.push (UInt8.xor (b0.getD j 0) (bPrev.getD j 0))
    bPrev := sha256Bytes (xored ++ #[UInt8.ofNat i] ++ dstPrime)
    uniform := uniform ++ bPrev
  return uniform.extract 0 lenInBytes

/-- The domain-separation tag we use for hash-to-G2. -/
def dstG2 : Array UInt8 :=
  "BLS_SIG_BLS12381G2_XMD:SHA-256_SIMPLE_RO_".toUTF8.toList.toArray

/-- Big-endian bytes → Nat. -/
def beBytesToNat (bs : Array UInt8) : Nat := Id.run do
  let mut acc : Nat := 0
  for b in bs do
    acc := acc * 256 + b.toNat
  return acc

/-- SIMPLIFIED hash-to-G2 (see the module note above).  Derives
    a uniform 48-byte scalar via `expand_message_xmd`, reduces it
    mod the subgroup order r, and multiplies the G2 generator.
    Deterministic, lands in the prime-order subgroup — suitable
    for a self-consistent sign/verify reference, NOT for
    interop with spec-compliant BLS implementations. -/
def hashToG2 (msg : Array UInt8) : G2.Point :=
  let bytes := expandMessageXmd msg dstG2 48
  let t := (beBytesToNat bytes) % r
  let t := if t = 0 then 1 else t   -- avoid the identity
  G2.mulScalar t G2.generator

/-- A BLS public key is a G1 point pk = sk · g1. -/
def derivePublicKey (sk : Nat) : G1.Point :=
  G1.mulScalar (sk % r) G1.generator

/-- Sign: σ = sk · H(msg) ∈ G2. -/
def sign (sk : Nat) (msg : Array UInt8) : G2.Point :=
  G2.mulScalar (sk % r) (hashToG2 msg)

/-- Verify: accept iff e(g1, σ) = e(pk, H(msg)). -/
def verify (pk : G1.Point) (msg : Array UInt8) (sig : G2.Point) : Bool :=
  let hm := hashToG2 msg
  let lhs := Pairing.pairing G1.generator sig
  let rhs := Pairing.pairing pk hm
  lhs == rhs

/-- Aggregate a list of G2 signatures by point addition. -/
def aggregate (sigs : List G2.Point) : G2.Point :=
  sigs.foldl G2.add G2.infinity

/-- Aggregate a list of G1 public keys. -/
def aggregatePubkeys (pks : List G1.Point) : G1.Point :=
  pks.foldl G1.add G1.infinity

/-- Verify an aggregate signature over the SAME message signed by
    every key: accept iff e(g1, aggSig) = e(aggPk, H(msg)). -/
def verifyAggregate (pks : List G1.Point) (msg : Array UInt8)
    (aggSig : G2.Point) : Bool :=
  let aggPk := aggregatePubkeys pks
  let hm := hashToG2 msg
  Pairing.pairing G1.generator aggSig == Pairing.pairing aggPk hm

end Sparkle.IP.Crypto.BLS12_381
