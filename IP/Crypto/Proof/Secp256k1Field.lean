/-
  IP.Crypto.Secp256k1Field — pure-data field arithmetic
  modulo the secp256k1 prime
    p = 2^256 - 2^32 - 977
      = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF
        FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F

  Layout mirrors `IP.Crypto.Ed25519Field`: a field element
  is just a `Nat` representative in [0, p).  Operations
  reduce mod p after each step.  The HW limb-based engine
  (8-limb × 32-bit radix) lands later in L.5.b.
-/

import Sparkle

namespace Sparkle.IP.Crypto.Secp256k1Field

/-- The secp256k1 base-field prime. -/
def p : Nat := 2^256 - 2^32 - 977

@[inline] def reduce (n : Nat) : Nat := n % p

@[inline] def ofBitVec (x : BitVec 256) : Nat := reduce x.toNat

@[inline] def toBitVec (n : Nat) : BitVec 256 := BitVec.ofNat 256 n

/-! ### Field operations. -/

@[inline] def add (a b : Nat) : Nat := reduce (a + b)

@[inline] def sub (a b : Nat) : Nat :=
  if a < b then reduce (a + p - b) else reduce (a - b)

@[inline] def mul (a b : Nat) : Nat := reduce (a * b)

@[inline] def sq (a : Nat) : Nat := mul a a

/-- Pow modulo p (square-and-multiply). -/
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

/-- Modular inverse via Fermat: a^(-1) ≡ a^(p-2) mod p. -/
@[inline] def inv (a : Nat) : Nat := powMod a (p - 2)

end Sparkle.IP.Crypto.Secp256k1Field
