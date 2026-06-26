/-
  IP.Crypto.P256ECDSA — ECDSA verification on NIST P-256
  (secp256r1).  Targets the TLS 1.3
  ecdsa_secp256r1_sha256 (0x0403) signature scheme.

  Verify:
    Check 0 < r < n, 0 < s < n.
    w  = s^(-1) mod n
    u1 = z · w mod n  (z = leftmost 256 bits of SHA-256(msg))
    u2 = r · w mod n
    P  = u1 · G + u2 · Q
    Valid iff P ≠ ∞ ∧ (P.x mod n) = r.
-/

import IP.Crypto.P256Point

namespace Sparkle.IP.Crypto.P256ECDSA

open Sparkle.IP.Crypto.P256Point
  (Point base curveOrderN add mulScalar)

def n : Nat := curveOrderN

/-- Modular inverse mod n via Fermat. -/
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

/-- Derive Q = d · G from a private scalar d. -/
def derivePublicKey (d : Nat) : Point := mulScalar d base

/-- ECDSA verify.  `q` is the public-key point, `z` the
    message digest as a Nat (caller hashes), `(r, s)` the
    signature components. -/
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

/-- Parse a raw uncompressed public-key encoding per SEC1 §2.3.3:
    `04 || X (32 bytes) || Y (32 bytes)` (65 bytes).
    Returns `none` on bad encoding. -/
def parsePubkeyRaw (bytes : Array UInt8) : Option Point := Id.run do
  if bytes.size ≠ 65 then return none
  if bytes[0]! ≠ 0x04 then return none
  let mut x : Nat := 0
  let mut y : Nat := 0
  for i in [:32] do
    x := (x <<< 8) ||| bytes[1 + i]!.toNat
  for i in [:32] do
    y := (y <<< 8) ||| bytes[33 + i]!.toNat
  return some (.affine x y)

/-- Parse a TLS 1.3 ECDSA signature (ASN.1 DER `SEQUENCE { r,
    s }`).  TLS sends this as the raw DER-encoded structure
    inside `CertificateVerify.signature`.  Returns `(r, s)`
    or `none` on malformed input. -/
def parseDerSignature (bytes : Array UInt8) : Option (Nat × Nat) := Id.run do
  -- Outer: 0x30 <len> ...
  if bytes.size < 8 then return none
  if bytes[0]! ≠ 0x30 then return none
  -- Skip len (1 byte for typical TLS signatures < 0x80).
  -- Real DER may need extended-length parsing; for TLS 1.3
  -- ECDSA-P256 signatures the SEQUENCE length is < 80 bytes
  -- (typically 0x44 to 0x46 = 68-70).
  let totalLen := bytes[1]!.toNat
  if bytes.size < 2 + totalLen then return none
  -- First INTEGER (r).
  let mut p := 2
  if bytes[p]! ≠ 0x02 then return none
  p := p + 1
  let rLen := bytes[p]!.toNat
  p := p + 1
  let mut r : Nat := 0
  for i in [:rLen] do
    r := (r <<< 8) ||| bytes[p + i]!.toNat
  p := p + rLen
  -- Second INTEGER (s).
  if p ≥ bytes.size ∨ bytes[p]! ≠ 0x02 then return none
  p := p + 1
  if p ≥ bytes.size then return none
  let sLen := bytes[p]!.toNat
  p := p + 1
  let mut s : Nat := 0
  for i in [:sLen] do
    if p + i < bytes.size then
      s := (s <<< 8) ||| bytes[p + i]!.toNat
  return some (r, s)

/-- Pack a 32-byte big-endian message digest as a Nat. -/
def digestToNat (digest : Array UInt8) : Nat := Id.run do
  let mut z : Nat := 0
  for i in [:digest.size] do
    z := (z <<< 8) ||| digest[i]!.toNat
  return z

end Sparkle.IP.Crypto.P256ECDSA
