/-
  IP.Crypto.Goldilocks — pure-data field arithmetic
  modulo the Goldilocks prime
    p = 2^64 - 2^32 + 1 = 0xFFFFFFFF00000001

  Used by Plonky2, RISC Zero, and other STARK-style ZK
  systems for its HW-friendly properties:
    * Fits in 64 bits.
    * 2^64 ≡ 2^32 - 1 (mod p), so reduction of a 128-bit
      product is a single shift + add + sub — no division
      or wide modular reduction.
    * Has a 2^32-th root of unity, useful for FFT-based
      polynomial commitment schemes.

  This file ships the pure-data reference using `Nat % p`.
  The HW-friendly 64-bit reduction is documented but not
  yet specialised — the `Nat` path is correct by inspection
  and matches what a HW limb-based engine would produce.
-/

import Sparkle

namespace Sparkle.IP.Crypto.Goldilocks

/-- The Goldilocks prime: 2^64 - 2^32 + 1. -/
def p : Nat := 2^64 - 2^32 + 1

/-- Reduce a Nat into [0, p). -/
@[inline] def reduce (n : Nat) : Nat := n % p

/-- Field representative from a 64-bit BV (`x` is the raw
    bit pattern; if `x = p..2^64-1` it's still reduced). -/
@[inline] def ofBitVec (x : BitVec 64) : Nat := reduce x.toNat

/-- Convert a Nat (assumed in [0, p)) back into 64-bit BV. -/
@[inline] def toBitVec (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-! ### Field operations. -/

@[inline] def add (a b : Nat) : Nat := reduce (a + b)

@[inline] def sub (a b : Nat) : Nat :=
  if a < b then reduce (a + p - b) else reduce (a - b)

@[inline] def mul (a b : Nat) : Nat := reduce (a * b)

@[inline] def sq (a : Nat) : Nat := mul a a

/-- powMod via square-and-multiply. -/
def powMod (base : Nat) (exp : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := reduce base
  let mut e := exp
  while e > 0 do
    if e % 2 = 1 then
      result := mul result b
    b := sq b
    e := e / 2
  return result

/-- Fermat inverse: a^(p-2). -/
@[inline] def inv (a : Nat) : Nat := powMod a (p - 2)

/-! ### Primitive root of unity.

    The Goldilocks prime has order p - 1 = 2^32 · ((2^32 -
    1)/2^0).  Since (p - 1) / 2^32 is odd, there's a
    primitive 2^32-th root of unity g.  One such is
    g = 7^((p - 1) / 2^32) mod p = (computable; commonly
    given as 1753635133440165772 in published references). -/
def gen2pow32 : Nat := 1753635133440165772

end Sparkle.IP.Crypto.Goldilocks
