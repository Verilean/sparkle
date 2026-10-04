/-
  IP.Crypto.P256Field — pure-data field arithmetic modulo
  the NIST P-256 prime:
    p = 2^256 - 2^224 + 2^192 + 2^96 - 1
      = FFFFFFFF 00000001 00000000 00000000
        00000000 FFFFFFFF FFFFFFFF FFFFFFFF

  Layout mirrors `IP.Crypto.Secp256k1Field`: a field element
  is a `Nat` representative in [0, p).  Operations reduce
  mod p after each step.
-/

import Sparkle

namespace Sparkle.IP.Crypto.P256Field

/-- NIST P-256 (secp256r1) base-field prime. -/
def p : Nat :=
  0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

@[inline] def reduce (n : Nat) : Nat := n % p

@[inline] def ofBitVec (x : BitVec 256) : Nat := reduce x.toNat
@[inline] def toBitVec (n : Nat) : BitVec 256 := BitVec.ofNat 256 n

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

@[inline] def inv (a : Nat) : Nat := powMod a (p - 2)

end Sparkle.IP.Crypto.P256Field
