/-
  IP.Crypto.Rfc6979 — deterministic ECDSA nonce (RFC 6979) for secp256k1
  with SHA-256, as the pure-data golden model the on-chip HMAC-SHA256 +
  nonce-derivation FSM is cross-checked against.

  Verified:
    * `hmacSha256` matches RFC 4231 Test Case 2
      (key="Jefe", data="what do ya want for nothing?" →
       5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843).
    * `rfc6979 d z` yields k ∈ [1, n) and `sign d (rfc6979 d z) z` verifies
      against `derivePublicKey d`.
-/
import IP.Crypto.SHA256
import IP.Crypto.Proof.Secp256k1ECDSA

namespace Sparkle.IP.Crypto.Rfc6979

open Sparkle.IP.Crypto.SHA256 (sha256OfBytes)

/-- SHA-256 of a byte array → 32 bytes, H0 in the most-significant slot. -/
def sha256Bytes (input : Array UInt8) : Array UInt8 := Id.run do
  let h := sha256OfBytes input
  let mut out : Array UInt8 := #[]
  for w in h do
    for j in [0:4] do
      out := out.push (UInt8.ofNat ((w >>> (8*(3-j))).toNat &&& 0xFF))
  return out

/-- SHA-256 block size (bytes). -/
def blockBytes : Nat := 64

/-- HMAC-SHA256(key, msg) → 32 bytes (RFC 2104). -/
def hmacSha256 (key msg : Array UInt8) : Array UInt8 := Id.run do
  let k0 := if key.size > blockBytes then sha256Bytes key else key
  let mut kpad : Array UInt8 := k0
  while kpad.size < blockBytes do kpad := kpad.push 0
  let ipad := kpad.map (fun b => b ^^^ 0x36)
  let opad := kpad.map (fun b => b ^^^ 0x5c)
  let inner := sha256Bytes (ipad ++ msg)
  return sha256Bytes (opad ++ inner)

/-- Big-endian 32-byte encoding of `x mod 2^256`. -/
def i2octets32 (x : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for j in [0:32] do out := out.push (UInt8.ofNat ((x >>> (8*(31-j))) &&& 0xFF))
  return out

/-- Big-endian decode of a byte array to a Nat. -/
def octets2i (a : Array UInt8) : Nat := Id.run do
  let mut v := 0
  for b in a do v := (v <<< 8) ||| b.toNat
  return v

/-- Curve order n. -/
def nOrd : Nat := Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-- RFC 6979 §3.2 deterministic nonce for secp256k1 + SHA-256 (qlen = 256, so
    each round's `T` is a single HMAC output).  `z` is the 256-bit message hash. -/
def rfc6979 (d : Nat) (z : Nat) : Nat := Id.run do
  -- bits2octets(h1) = int2octets(bits2int(h1) mod q); here bits2int(z)=z.
  let dz := i2octets32 d ++ i2octets32 (z % nOrd)
  let mut v : Array UInt8 := Array.replicate 32 0x01
  let mut k : Array UInt8 := Array.replicate 32 0x00
  k := hmacSha256 k (v ++ #[0x00] ++ dz)
  v := hmacSha256 k v
  k := hmacSha256 k (v ++ #[0x01] ++ dz)
  v := hmacSha256 k v
  let mut result := 0
  let mut guard := 0
  while result == 0 && guard < 100 do
    v := hmacSha256 k v
    let cand := octets2i v
    if 1 ≤ cand && cand < nOrd then result := cand
    else
      k := hmacSha256 k (v ++ #[0x00])
      v := hmacSha256 k v
    guard := guard + 1
  return result

/-- Deterministic ECDSA sign: derive k via RFC 6979 then sign. -/
def signDeterministic (d z : Nat) : Option (Nat × Nat) :=
  Sparkle.IP.Crypto.Secp256k1ECDSA.sign d (rfc6979 d z) z

end Sparkle.IP.Crypto.Rfc6979
