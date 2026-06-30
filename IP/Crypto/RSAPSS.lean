/-
  IP.Crypto.RSAPSS — RSA-PSS signature verification with
  MGF1-SHA256 (RFC 8017 §8.1.2 / §9.1.2).  Targets the TLS
  1.3 `rsa_pss_rsae_sha256` (0x0804) signature scheme.

  Verify operation (RSASSA-PSS-VERIFY, RFC 8017 §8.1.2):
    1. Length checks: signature length = k (modulus size).
    2. EMSA-PSS-Decode the signature representative:
       a. m = sig^e mod n   (RSAVP1 — public-key op)
       b. EM = I2OSP(m, emLen)
       c. Parse EM as: maskedDB || H || 0xBC
       d. dbMask = MGF1(H, emLen - hLen - 1)
       e. DB = maskedDB XOR dbMask
       f. Clear leading bits of DB to match (8·emLen - emBits)
       g. Check DB has form: 0..0 0x01 salt
       h. Compute M' = (0x00 × 8) || mHash || salt
       i. H' = SHA-256(M')
       j. Accept iff H == H'.

  Public key is (n, e).  TLS 1.3 typically uses e = 65537.

  Note: this is a software reference for sim-time TLS handshake
  verification.  HW acceleration of RSA modpow is well outside
  Sparkle's current scope — TLS HW boxes generally use ECDSA or
  Ed25519 for the cert chain because RSA modpow is huge.
-/

import IP.Crypto.HKDF

namespace Sparkle.IP.Crypto.RSAPSS

open Sparkle.IP.Crypto.HKDF (sha256)

/-- Hash output length for SHA-256 (32 bytes). -/
def hLen : Nat := 32

/-- I2OSP: integer to big-endian octet string of length `xLen`. -/
def i2osp (x : Nat) (xLen : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate xLen 0
  let mut v := x
  for i in [:xLen] do
    out := out.set! (xLen - 1 - i) (UInt8.ofNat (v &&& 0xFF))
    v := v >>> 8
  return out

/-- OS2IP: big-endian octet string → Nat. -/
def os2ip (bytes : Array UInt8) : Nat := Id.run do
  let mut acc : Nat := 0
  for b in bytes do
    acc := (acc <<< 8) ||| b.toNat
  return acc

/-- Modular exponentiation (square-and-multiply).  Used for
    RSAVP1 (signature^e mod n). -/
def modPow (base exp m : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := base % m
  let mut e := exp
  while e > 0 do
    if e % 2 = 1 then
      result := (result * b) % m
    b := (b * b) % m
    e := e / 2
  return result

/-- MGF1 with SHA-256 (RFC 8017 §B.2.1).  Produce `maskLen`
    bytes of mask from `seed`. -/
def mgf1 (seed : Array UInt8) (maskLen : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  let n := (maskLen + hLen - 1) / hLen
  for i in [:n] do
    let c : Array UInt8 :=
      #[ UInt8.ofNat ((i >>> 24) &&& 0xFF)
       , UInt8.ofNat ((i >>> 16) &&& 0xFF)
       , UInt8.ofNat ((i >>>  8) &&& 0xFF)
       , UInt8.ofNat ( i         &&& 0xFF) ]
    out := out ++ sha256 (seed ++ c)
  -- Truncate to maskLen bytes.
  let mut truncated : Array UInt8 := Array.replicate maskLen 0
  for i in [:maskLen] do
    if i < out.size then
      truncated := truncated.set! i out[i]!
  return truncated

/-- XOR two byte arrays (truncated to min length). -/
def xorBytes (a b : Array UInt8) : Array UInt8 := Id.run do
  let n := min a.size b.size
  let mut out : Array UInt8 := Array.replicate n 0
  for i in [:n] do
    out := out.set! i (a[i]! ^^^ b[i]!)
  return out

/-- Compute the bit-length of n. -/
def bitLength (n : Nat) : Nat := Id.run do
  let mut k := 0
  let mut v := n
  while v > 0 do
    k := k + 1
    v := v >>> 1
  return k

/-- EMSA-PSS-Decode (RFC 8017 §9.1.2).  `mHash` is the SHA-256
    of the message (32 bytes).  `em` is the encoded message
    (a `emLen`-byte string).  `emBits` is the bit-length of
    the modulus minus 1.

    Returns `true` iff the encoding is valid for the given
    `mHash`. -/
def emsaPssVerify (mHash em : Array UInt8) (emBits : Nat) (sLen : Nat) : Bool := Id.run do
  let emLen := em.size
  -- Length sanity: emLen ≥ hLen + sLen + 2.
  if emLen < hLen + sLen + 2 then return false
  -- Last byte must be 0xBC.
  if em[emLen - 1]! ≠ 0xBC then return false
  -- Split: maskedDB = em[0..emLen - hLen - 1], H = em[emLen - hLen - 1..emLen - 1]
  let dbLen := emLen - hLen - 1
  let mut maskedDB : Array UInt8 := Array.replicate dbLen 0
  for i in [:dbLen] do
    maskedDB := maskedDB.set! i em[i]!
  let mut h : Array UInt8 := Array.replicate hLen 0
  for i in [:hLen] do
    h := h.set! i em[dbLen + i]!
  -- Check leading masked bits.  Number of bits to zero out =
  -- 8·emLen - emBits.
  let topZeroBits := 8 * emLen - emBits
  let topMask := UInt8.ofNat ((0xFF >>> topZeroBits) &&& 0xFF)
  if (maskedDB[0]! &&& (UInt8.ofNat (0xFF ^^^ topMask.toNat))) ≠ 0 then return false
  -- dbMask = MGF1(H, dbLen)
  let dbMask := mgf1 h dbLen
  -- DB = maskedDB XOR dbMask, then zero the leading bits.
  let mut db := xorBytes maskedDB dbMask
  db := db.set! 0 (db[0]! &&& topMask)
  -- Check: DB[0..dbLen - sLen - 2] all 0, DB[dbLen - sLen - 1] = 0x01.
  for i in [:dbLen - sLen - 1] do
    if db[i]! ≠ 0 then return false
  if db[dbLen - sLen - 1]! ≠ 0x01 then return false
  -- Extract salt.
  let mut salt : Array UInt8 := Array.replicate sLen 0
  for i in [:sLen] do
    salt := salt.set! i db[dbLen - sLen + i]!
  -- M' = (0x00 × 8) || mHash || salt
  let prefix0 : Array UInt8 := Array.replicate 8 0
  let m' := prefix0 ++ mHash ++ salt
  let h' := sha256 m'
  -- Compare H == H'.
  if h.size ≠ h'.size then return false
  let mut equal := true
  for i in [:h.size] do
    if h[i]! ≠ h'[i]! then equal := false
  return equal

/-- RSASSA-PSS-VERIFY (RFC 8017 §8.1.2).

    Inputs:
      `n` : RSA modulus
      `e` : public exponent (typically 65537)
      `msg` : the message that was signed
      `signature` : the RSA-PSS signature (k bytes, where k is the
                    modulus size in bytes)
      `sLen` : the salt length (TLS 1.3 mandates sLen = hLen = 32) -/
def verify (n e : Nat) (msg signature : Array UInt8) (sLen : Nat := 32) : Bool := Id.run do
  let k := signature.size
  let modBits := bitLength n
  -- Modulus size check.
  let kFromN := (modBits + 7) / 8
  if k ≠ kFromN then return false
  -- Signature must be < n.
  let m := os2ip signature
  if m ≥ n then return false
  -- RSAVP1: recover the encoded message.
  let mInt := modPow m e n
  -- emBits = modBits - 1; emLen = ceil(emBits / 8).
  let emBits := modBits - 1
  let emLen := (emBits + 7) / 8
  let em := i2osp mInt emLen
  -- Hash the message.
  let mHash := sha256 msg
  -- EMSA-PSS-Decode.
  emsaPssVerify mHash em emBits sLen

/-- Parse a DER-encoded RSAPublicKey:
      SEQUENCE { n INTEGER, e INTEGER }
    Returns `(n, e)` or `none` on malformed input.

    This is the inner key encoding (the body of the
    SubjectPublicKeyInfo's BIT STRING for an RSA key).
    Handles modulus sizes up to ~4096 bits via the standard
    DER short/long-form length encoding. -/
def parsePubkeyDer (bytes : Array UInt8) : Option (Nat × Nat) := Id.run do
  if bytes.size < 8 then return none
  -- Outer SEQUENCE.
  if bytes[0]! ≠ 0x30 then return none
  let mut p := 1
  -- Length of outer SEQUENCE — may be long form (0x82 LL LL).
  let len0 := bytes[p]!.toNat
  p := p + 1
  if len0 ≥ 0x80 then
    -- Long form: low 7 bits = number of len bytes.
    let nLen := len0 &&& 0x7F
    if p + nLen > bytes.size then return none
    let mut acc := 0
    for i in [:nLen] do
      acc := (acc <<< 8) ||| bytes[p + i]!.toNat
    p := p + nLen
    let _ := acc  -- we don't actually need the outer length
  -- First INTEGER (n).
  if p ≥ bytes.size ∨ bytes[p]! ≠ 0x02 then return none
  p := p + 1
  let nLen0 := bytes[p]!.toNat
  p := p + 1
  let mut nLen := nLen0
  if nLen0 ≥ 0x80 then
    let nl := nLen0 &&& 0x7F
    if p + nl > bytes.size then return none
    let mut acc := 0
    for i in [:nl] do
      acc := (acc <<< 8) ||| bytes[p + i]!.toNat
    p := p + nl
    nLen := acc
  if p + nLen > bytes.size then return none
  let mut n : Nat := 0
  for i in [:nLen] do
    n := (n <<< 8) ||| bytes[p + i]!.toNat
  p := p + nLen
  -- Second INTEGER (e).
  if p ≥ bytes.size ∨ bytes[p]! ≠ 0x02 then return none
  p := p + 1
  if p ≥ bytes.size then return none
  let eLen := bytes[p]!.toNat
  p := p + 1
  if eLen ≥ 0x80 then return none  -- e is small, no long form expected
  if p + eLen > bytes.size then return none
  let mut e : Nat := 0
  for i in [:eLen] do
    e := (e <<< 8) ||| bytes[p + i]!.toNat
  return some (n, e)

end Sparkle.IP.Crypto.RSAPSS
