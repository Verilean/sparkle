/-
  IP.Crypto.Ed25519Sign — RFC 8032 §5.1 Ed25519 signing
  (pure-Ed25519, no context, no PureEdDSA-vs-HashEdDSA
  variant distinction beyond the basic algorithm).

  Algorithm (signing):
    1. h = SHA-512(privkey)  (64 bytes)
       a-bytes = h[0..32]
       prefix  = h[32..64]
    2. Clamp a-bytes (set bit 254, clear bits 0,1,2 and 255).
    3. a = little-endian integer of clamped a-bytes (a scalar).
    4. A = a · B  (the public key point).
       pubkey-encoded = pointEncode A   (32 bytes).
    5. r = SHA-512(prefix || M) mod l
    6. R = r · B; R-encoded = pointEncode R  (32 bytes).
    7. k = SHA-512(R-encoded || pubkey-encoded || M) mod l
    8. S = (r + k · a) mod l
    9. Signature = R-encoded || S-encoded  (64 bytes).

  Point encoding (RFC 8032 §5.1.2):
    32 little-endian bytes = y || (x mod 2).
    The high bit of the last byte carries x's sign bit.
-/

import IP.Crypto.SHA512
import IP.Crypto.Ed25519Point

namespace Sparkle.IP.Crypto.Ed25519Sign

open Sparkle.IP.Crypto.SHA512 (sha512Bytes)
open Sparkle.IP.Crypto.Ed25519Field (p)
open Sparkle.IP.Crypto.Ed25519Point (Point base zero add mulScalar baseX baseY pointDecode)

/-- The curve order l per RFC 8032 §5.1. -/
def curveOrderL : Nat :=
  2^252 + 27742317777372353535851937790883648493

/-- Decode 32 little-endian bytes into a Nat. -/
def leBytesToNat (bytes : Array UInt8) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:bytes.size] do
    acc := acc ||| ((bytes.getD i 0).toNat <<< (i * 8))
  return acc

/-- Encode a Nat into `n` little-endian bytes. -/
def natToLeBytes (x : Nat) (n : Nat) : Array UInt8 := Id.run do
  let mut acc : Array UInt8 := #[]
  for i in [:n] do
    let b := (x >>> (i * 8)) &&& 0xFF
    acc := acc.push (UInt8.ofNat b)
  return acc

/-- Reduce a Nat mod l (curve order). -/
@[inline] def modL (x : Nat) : Nat := x % curveOrderL

/-- Clamp the scalar per RFC 8032 §5.1.5:
      a[0]  &= 0xF8   (clear low 3 bits)
      a[31] &= 0x7F   (clear bit 255)
      a[31] |= 0x40   (set bit 254)
    Operates on the 32-byte little-endian scalar. -/
def clampScalar (bytes : Array UInt8) : Array UInt8 := Id.run do
  let mut b := bytes
  let b0 := (b.getD 0 0).toNat &&& 0xF8
  b := b.set! 0 (UInt8.ofNat b0)
  let b31 := ((b.getD 31 0).toNat &&& 0x7F) ||| 0x40
  b := b.set! 31 (UInt8.ofNat b31)
  return b

/-- Encode a curve point per RFC 8032 §5.1.2:
    32 little-endian bytes representing y, with the top bit
    of the last byte set to the parity of x. -/
def pointEncode (pt : Point) : Array UInt8 := Id.run do
  let mut bytes := natToLeBytes pt.y 32
  -- Set top bit of byte 31 to (x mod 2).
  let xBit := pt.x &&& 1
  let last := (bytes.getD 31 0).toNat ||| (xBit <<< 7)
  bytes := bytes.set! 31 (UInt8.ofNat last)
  return bytes

/-- RFC 8032 §5.1.6 — full sign function.

    Inputs:
      privkey : 32-byte secret key
      msg     : arbitrary-length message
    Output: 64-byte signature R || S. -/
def sign (privkey : Array UInt8) (msg : Array UInt8) : Array UInt8 := Id.run do
  -- Step 1: hash privkey to 64 bytes.
  let h := sha512Bytes privkey
  let aBytes := h.extract 0 32
  let pfx    := h.extract 32 64
  -- Step 2 & 3: clamp and decode as scalar.
  let clamped := clampScalar aBytes
  let a := leBytesToNat clamped
  -- Step 4: A = a · B; encode.
  let pubKey := mulScalar a base
  let aEnc := pointEncode pubKey
  -- Step 5: r = SHA-512(prefix || M) mod l.
  let r := modL (leBytesToNat (sha512Bytes (pfx ++ msg)))
  -- Step 6: R = r · B; encode.
  let pointR := mulScalar r base
  let rEnc := pointEncode pointR
  -- Step 7: k = SHA-512(R-enc || A-enc || M) mod l.
  let kInput := rEnc ++ aEnc ++ msg
  let k := modL (leBytesToNat (sha512Bytes kInput))
  -- Step 8: S = (r + k · a) mod l.
  let s := modL (r + k * a)
  -- Step 9: signature = R-enc || S-enc (32 bytes each).
  return rEnc ++ natToLeBytes s 32

/-- Derive the 32-byte public key from a 32-byte private key. -/
def derivePublicKey (privkey : Array UInt8) : Array UInt8 :=
  let h := sha512Bytes privkey
  let aBytes := h.extract 0 32
  let clamped := clampScalar aBytes
  let a := leBytesToNat clamped
  pointEncode (mulScalar a base)

/-- RFC 8032 §5.1.7 — verify(A, M, R || S).

    1. Decode A → point P_A (reject on non-canonical encoding).
    2. Decode R → point P_R (reject on non-canonical encoding).
    3. Parse S as little-endian; reject if S ≥ L.
    4. k = SHA-512(R || A || M) mod L.
    5. Accept iff S·B = R + k·A.

    Returns `true` on valid sig, `false` otherwise. -/
def verify (pubkey msg sig : Array UInt8) : Bool := Id.run do
  if pubkey.size ≠ 32 then return false
  if sig.size ≠ 64 then return false
  -- Step 1: decode public key.
  let pa? := pointDecode pubkey
  match pa? with
  | none => return false
  | some pa =>
    -- Step 2: split sig into R-enc (32) and S-enc (32).
    let rEnc := sig.extract 0 32
    let sEnc := sig.extract 32 64
    -- Step 3: decode R.
    let pr? := pointDecode rEnc
    match pr? with
    | none => return false
    | some pr =>
      -- Parse S; reject if ≥ L.
      let s := leBytesToNat sEnc
      if s ≥ curveOrderL then return false
      -- Step 4: k = SHA-512(R || A || M) mod L.
      let k := modL (leBytesToNat (sha512Bytes (rEnc ++ pubkey ++ msg)))
      -- Step 5: check S·B = R + k·A.
      let lhs := mulScalar s base
      let kA := mulScalar k pa
      let rhs := add pr kA
      return decide (lhs = rhs)

end Sparkle.IP.Crypto.Ed25519Sign
