/-
  IP.Crypto.Secp256k1ECDSA — ECDSA signing + verification
  on secp256k1.

  RFC 6979 deterministic nonce derivation is NOT implemented
  here for the demo: callers pass `k` (the per-signature
  nonce) explicitly.  A production implementation would
  derive `k` from (private key, message) via the RFC 6979
  HMAC-DRBG construction.  Deterministic-`k` vectors from
  RFC 6979 §A.2.5 are still the easiest test inputs since
  they avoid pulling RNG state into the sim.

  Sign:
    z = hash truncated to 256 bits (we accept it as a Nat
        directly to keep the API independent of SHA-256
        binding)
    (x1, _) = k · G
    r = x1 mod n
    s = k^(-1) (z + r · d) mod n
    signature = (r, s)

  Verify:
    Check 0 < r < n, 0 < s < n.
    w  = s^(-1) mod n
    u1 = z · w mod n
    u2 = r · w mod n
    P  = u1 · G + u2 · Q  (Q is the public key)
    Valid iff P ≠ infinity AND (P.x mod n) = r.
-/

import IP.Crypto.Secp256k1Point

namespace Sparkle.IP.Crypto.Secp256k1ECDSA

open Sparkle.IP.Crypto.Secp256k1Point
  (Point base curveOrderN add mulScalar)

/-- Curve order. -/
def n : Nat := curveOrderN

/-- Modular inverse mod n (Fermat — n is prime, so
    a^(n-2) ≡ a^(-1) mod n). -/
def invModN (a : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := a % n
  let mut e := n - 2
  while e > 0 do
    if e % 2 = 1 then
      result := (result * b) % n
    b := (b * b) % n
    e := e / 2
  return result

/-- Derive the public key Q = d · G from a private key. -/
def derivePublicKey (d : Nat) : Point := mulScalar d base

/-- ECDSA sign with a caller-provided nonce `k`.
    Returns `(r, s)`; callers must check r ≠ 0 ∧ s ≠ 0. -/
def sign (d k z : Nat) : Option (Nat × Nat) :=
  let kg := mulScalar k base
  match kg with
  | .infinity => none
  | .affine x1 _ =>
    let r := x1 % n
    if r = 0 then none
    else
      let kInv := invModN k
      let s := (kInv * ((z + r * d) % n)) % n
      if s = 0 then none
      else some (r, s)

/-- ECDSA verify.  `Q` is the public key, `z` the (already-
    truncated-to-Nat) hash of the message, `(r, s)` the
    signature. -/
def verify (q : Point) (z : Nat) (r s : Nat) : Bool :=
  if r = 0 ∨ r ≥ n ∨ s = 0 ∨ s ≥ n then false
  else
    let w := invModN s
    let u1 := (z * w) % n
    let u2 := (r * w) % n
    let p1 := mulScalar u1 base
    let p2 := mulScalar u2 q
    let pSum := add p1 p2
    match pSum with
    | .infinity => false
    | .affine x1 _ => x1 % n = r

end Sparkle.IP.Crypto.Secp256k1ECDSA
