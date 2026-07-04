/-
  IP.Crypto.DerSig — ASN.1 DER encoder for an ECDSA signature.

  CTAP2 (and TLS 1.3, X.509) carry an ECDSA signature as the
  DER encoding of

    SEQUENCE { INTEGER r, INTEGER s }

  i.e. `30 <len> 02 <rlen> <r-bytes> 02 <slen> <s-bytes>`.

  The one subtlety is the DER INTEGER rule: the value is a
  big-endian two's-complement integer with the MINIMUM number of
  bytes, so a positive value whose most-significant byte has its
  high bit set (≥ 0x80) must be prefixed with a `0x00` byte to
  keep it positive.  Getting this wrong is the classic ECDSA-DER
  interop bug; `P256ECDSA.parseDerSignature` decodes exactly this
  shape, so the round-trip test is the oracle.

  This is the *encode* direction (the repo already had
  `parseDerSignature`); it produces the `sig` bytes that CTAP2's
  attStmt / assertion responses carry.
-/
import IP.Crypto.Codec.RLP
import IP.Crypto.Proof.P256ECDSA

namespace Sparkle.IP.Crypto.DerSig

open Sparkle.IP.Crypto.RLP (beBytes)

/-- Big-endian minimal bytes of `n`, with a leading `0x00` when
    the top byte's high bit is set (DER positive-INTEGER rule).
    `0` encodes as a single `0x00` byte. -/
def intBytes (n : Nat) : Array UInt8 :=
  let raw := beBytes n
  if raw.isEmpty then #[0x00]
  else if raw[0]!.toNat ≥ 0x80 then #[0x00] ++ raw
  else raw

/-- Encode one DER INTEGER: `02 <len> <intBytes>`. -/
def encodeIntDer (n : Nat) : Array UInt8 :=
  let body := intBytes n
  #[0x02, UInt8.ofNat body.size] ++ body

/-- Encode an ECDSA signature `(r, s)` as DER
    `SEQUENCE { INTEGER r, INTEGER s }`.

    P-256 signatures are ≤ 72 bytes total, so the SEQUENCE length
    fits in one byte (< 0x80) — matching the single-byte-length
    assumption in `P256ECDSA.parseDerSignature`. -/
def encodeDerSig (r s : Nat) : Array UInt8 :=
  let inner := encodeIntDer r ++ encodeIntDer s
  #[0x30, UInt8.ofNat inner.size] ++ inner

end Sparkle.IP.Crypto.DerSig
