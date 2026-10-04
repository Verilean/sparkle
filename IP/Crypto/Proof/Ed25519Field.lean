/-
  IP.Crypto.Ed25519Field — pure-data field arithmetic mod
  p = 2^255 - 19.

  We model field elements as `BitVec 256` for simplicity
  (the top bit is always 0 after reduction).  Operations
  reduce modulo p after each step.  This is the "schoolbook"
  pure-data reference used to validate the HW limb-based
  implementation that follows.

  Phase L.2 ships this pure-data reference + sim test
  against RFC 7748 / 8032 known-answer values.  The HW
  engine (5-limb 51-bit radix on `BitVec 51` × 5 or a wide
  255-bit reg with a multi-cycle long-multiplication
  pipeline) follows in L.2.b.
-/

import Sparkle

namespace Sparkle.IP.Crypto.Ed25519Field

/-- The Curve25519 prime: p = 2^255 - 19. -/
def p : Nat := 2^255 - 19

/-- Reduce a Nat modulo p. -/
@[inline] def reduce (n : Nat) : Nat := n % p

/-- Pack a 256-bit BitVec into the field representative
    in [0, p).  Treats the input as an unsigned 256-bit
    integer; equivalent to `n % p`. -/
@[inline] def ofBitVec (x : BitVec 256) : Nat := reduce x.toNat

/-- Convert a Nat (assumed in [0, p)) back into a 256-bit
    BitVec (zero-extending the top bit, which p never sets). -/
@[inline] def toBitVec (n : Nat) : BitVec 256 := BitVec.ofNat 256 n

/-! ### Field operations. -/

@[inline] def add (a b : Nat) : Nat := reduce (a + b)

@[inline] def sub (a b : Nat) : Nat :=
  -- a - b mod p = a + (p - b) mod p when a < b
  if a < b then reduce (a + p - b) else reduce (a - b)

@[inline] def mul (a b : Nat) : Nat := reduce (a * b)

@[inline] def sq (a : Nat) : Nat := mul a a

/-- Pow modulo p via square-and-multiply, exponent in
    standard Nat.  Used to compute inverses via Fermat
    (a^(p-2) ≡ a^(-1) mod p when p is prime). -/
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

/-- Modular inverse via Fermat's little theorem:
    a^(-1) ≡ a^(p-2) mod p. -/
@[inline] def inv (a : Nat) : Nat := powMod a (p - 2)

end Sparkle.IP.Crypto.Ed25519Field
