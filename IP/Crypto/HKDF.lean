/-
  IP.Crypto.HKDF — HMAC-SHA-256, HKDF (RFC 5869), and the
  TLS 1.3 key-schedule primitives (RFC 8446 §7.1).

  Layered:
    1. `hmacSha256 K m`         — HMAC-SHA-256 (RFC 2104)
    2. `hkdfExtract salt IKM`   — RFC 5869 §2.2 (= HMAC)
    3. `hkdfExpand PRK info L`  — RFC 5869 §2.3
    4. `hkdfExpandLabel secret label context L`
                                — TLS 1.3 §7.1
    5. `deriveSecret secret label transcriptHash`
                                — TLS 1.3 §7.1

  Validated against:
    * RFC 5869 Appendix A test cases 1, 2
    * (TLS 1.3 trace KAT lives in T.6 once we have transcripts)
-/

import IP.Crypto.SHA256

namespace Sparkle.IP.Crypto.HKDF

open Sparkle.IP.Crypto.SHA256 (sha256OfBytes)

/-! ### Byte helpers shared with the SHA-256 reference. -/

/-- Convert the SHA-256 8-word digest to a 32-byte array
    (big-endian per word). -/
def digestToBytes (digest : Array (BitVec 32)) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate 32 0
  for i in [:8] do
    let w := digest[i]!.toNat
    for j in [:4] do
      let shift := (3 - j) * 8
      out := out.set! (i * 4 + j) (UInt8.ofNat ((w >>> shift) &&& 0xFF))
  return out

/-- SHA-256 as a byte-array → byte-array function. -/
def sha256 (input : Array UInt8) : Array UInt8 :=
  digestToBytes (sha256OfBytes input)

/-! ### HMAC-SHA-256 (RFC 2104). -/

/-- HMAC block size for SHA-256 = 64 bytes. -/
def blockSize : Nat := 64

/-- HMAC output size for SHA-256 = 32 bytes. -/
def outSize : Nat := 32

/-- Prepare the HMAC key: if longer than blockSize, hash;
    then pad with zeros to exactly blockSize bytes. -/
def hmacKeyPad (key : Array UInt8) : Array UInt8 := Id.run do
  let k0 :=
    if key.size > blockSize then sha256 key
    else key
  let mut out : Array UInt8 := Array.replicate blockSize 0
  for i in [:k0.size] do
    out := out.set! i k0[i]!
  return out

/-- HMAC-SHA-256(K, m). -/
def hmacSha256 (key msg : Array UInt8) : Array UInt8 := Id.run do
  let k := hmacKeyPad key
  let mut ipad : Array UInt8 := Array.replicate blockSize 0
  let mut opad : Array UInt8 := Array.replicate blockSize 0
  for i in [:blockSize] do
    ipad := ipad.set! i (k[i]! ^^^ 0x36)
    opad := opad.set! i (k[i]! ^^^ 0x5C)
  let inner := sha256 (ipad ++ msg)
  let outer := sha256 (opad ++ inner)
  return outer

/-! ### HKDF (RFC 5869). -/

/-- HKDF-Extract per RFC 5869 §2.2: PRK = HMAC(salt, IKM).
    If salt is empty, RFC says use a zero-byte string of
    HashLen length. -/
def hkdfExtract (salt ikm : Array UInt8) : Array UInt8 :=
  let effectiveSalt :=
    if salt.size = 0 then Array.replicate outSize 0 else salt
  hmacSha256 effectiveSalt ikm

/-- HKDF-Expand per RFC 5869 §2.3:
      N = ceil(L / HashLen)
      T(0) = empty
      T(i) = HMAC(PRK, T(i-1) || info || octet(i))
      output = first L bytes of T(1) || T(2) || ... || T(N) -/
def hkdfExpand (prk info : Array UInt8) (length : Nat) : Array UInt8 := Id.run do
  let n := (length + outSize - 1) / outSize
  let mut out : Array UInt8 := #[]
  let mut t : Array UInt8 := #[]
  for i in [1:n + 1] do
    let block := hmacSha256 prk (t ++ info ++ #[UInt8.ofNat i])
    t := block
    out := out ++ block
  -- Truncate to L bytes.
  let mut truncated : Array UInt8 := Array.replicate length 0
  for i in [:length] do
    truncated := truncated.set! i out[i]!
  return truncated

/-! ### TLS 1.3 key schedule (RFC 8446 §7.1). -/

/-- Encode a Nat as a 2-byte big-endian length prefix. -/
private def be16 (n : Nat) : Array UInt8 :=
  #[UInt8.ofNat ((n >>> 8) &&& 0xFF), UInt8.ofNat (n &&& 0xFF)]

/-- Encode a byte array as `<u8 length> || bytes`. -/
private def vec8 (bs : Array UInt8) : Array UInt8 :=
  #[UInt8.ofNat bs.size] ++ bs

/-- HKDF-Expand-Label per RFC 8446 §7.1.

      struct {
        uint16 length = Length;
        opaque label<7..255> = "tls13 " + Label;
        opaque context<0..255> = Context;
      } HkdfLabel;

      HKDF-Expand-Label(Secret, Label, Context, Length) =
        HKDF-Expand(Secret, HkdfLabel, Length) -/
def hkdfExpandLabel
    (secret : Array UInt8) (label : String) (context : Array UInt8)
    (length : Nat) : Array UInt8 :=
  let fullLabel : Array UInt8 := "tls13 ".toUTF8.toList.toArray ++ label.toUTF8.toList.toArray
  let hkdfLabel : Array UInt8 := be16 length ++ vec8 fullLabel ++ vec8 context
  hkdfExpand secret hkdfLabel length

/-- Derive-Secret per RFC 8446 §7.1:
      Derive-Secret(Secret, Label, Messages) =
        HKDF-Expand-Label(Secret, Label, Transcript-Hash(Messages), Hash.length)

    Here `transcriptHash` is the pre-computed SHA-256 of the
    handshake transcript (caller's responsibility). -/
def deriveSecret
    (secret : Array UInt8) (label : String) (transcriptHash : Array UInt8) :
    Array UInt8 :=
  hkdfExpandLabel secret label transcriptHash outSize

end Sparkle.IP.Crypto.HKDF
