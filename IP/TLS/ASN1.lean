/-
  IP.TLS.ASN1 — minimal ASN.1 DER parser.

  Covers the subset of DER (Distinguished Encoding Rules)
  needed for X.509 certificates:
    * Universal tags: INTEGER, OCTET STRING, BIT STRING,
      NULL, OBJECT IDENTIFIER, UTCTime, GeneralizedTime,
      PrintableString, UTF8String, IA5String, BMPString,
      SEQUENCE, SET, BOOLEAN
    * Context-specific tags via tag-class detection
    * Short-form (≤ 127 bytes) and long-form length encoding

  Not covered (BER-only, X.509 doesn't use):
    * Indefinite-length encoding
    * Constructed string types

  Reference: ITU-T X.690 (DER subset).
-/

namespace Sparkle.IP.TLS.ASN1

/-- ASN.1 element class (top 2 bits of the tag byte). -/
inductive Class where
  | universal       : Class  -- 0b00
  | application     : Class  -- 0b01
  | contextSpecific : Class  -- 0b10
  | private_        : Class  -- 0b11
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether the element is primitive or constructed
    (bit 5 of the tag byte). -/
inductive Construction where
  | primitive    : Construction
  | constructed  : Construction
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An ASN.1 element header.  The value follows immediately
    in the source byte array. -/
structure Header where
  cls          : Class
  construction : Construction
  /-- Tag number (low 5 bits of the tag byte; we don't
      support multi-byte tags since X.509 doesn't use any). -/
  tag          : Nat
  /-- Offset where the value bytes start (= header end). -/
  valueOffset  : Nat
  /-- Length of the value in bytes. -/
  valueLength  : Nat
  deriving Repr, Inhabited

/-- Decode the class from the top 2 bits of a tag byte. -/
def decodeClass (b : UInt8) : Class :=
  match (b.toNat >>> 6) &&& 0b11 with
  | 0 => .universal
  | 1 => .application
  | 2 => .contextSpecific
  | _ => .private_

/-- Decode construction from bit 5 of a tag byte. -/
def decodeConstruction (b : UInt8) : Construction :=
  if (b.toNat &&& 0x20) ≠ 0 then .constructed else .primitive

/-- Tag number = low 5 bits of the tag byte. -/
def decodeTagNum (b : UInt8) : Nat := b.toNat &&& 0x1F

/-- Parse a length field starting at `off`.  Returns
    `(length, bytesConsumed)` or `none` if malformed.

    Short form (`< 0x80`): the byte IS the length, 1 byte
    consumed.
    Long form (`0x8N`): N (low 7 bits) is the count of
    big-endian length bytes that follow.  `0x80` (indefinite
    length) is rejected — DER forbids it. -/
def parseLength (bytes : Array UInt8) (off : Nat) : Option (Nat × Nat) := Id.run do
  if off ≥ bytes.size then return none
  let b0 := bytes[off]!.toNat
  if b0 < 0x80 then
    return some (b0, 1)
  else if b0 = 0x80 then
    return none  -- indefinite length not allowed in DER
  else
    let nBytes := b0 &&& 0x7F
    if off + 1 + nBytes > bytes.size then return none
    let mut len := 0
    for i in [:nBytes] do
      len := (len <<< 8) ||| bytes[off + 1 + i]!.toNat
    return some (len, 1 + nBytes)

/-- Parse a single ASN.1 header starting at `off`.  Returns
    a `Header` describing the element + the absolute offset
    where the NEXT element starts (= valueOffset + valueLength). -/
def parseHeader (bytes : Array UInt8) (off : Nat) : Option Header := Id.run do
  if off ≥ bytes.size then return none
  let tagByte := bytes[off]!
  -- We don't handle multi-byte tags (low 5 bits = 0x1F = "extended").
  if (tagByte.toNat &&& 0x1F) = 0x1F then return none
  match parseLength bytes (off + 1) with
  | none => return none
  | some (len, lenBytes) =>
    let valueOff := off + 1 + lenBytes
    if valueOff + len > bytes.size then return none
    return some
      { cls := decodeClass tagByte
      , construction := decodeConstruction tagByte
      , tag := decodeTagNum tagByte
      , valueOffset := valueOff
      , valueLength := len }

/-- The end offset (exclusive) of the element described by
    `h`. -/
@[inline] def Header.endOffset (h : Header) : Nat :=
  h.valueOffset + h.valueLength

/-- Slice `bytes[h.valueOffset .. h.endOffset]` as a fresh
    Array.  Bounds-safe. -/
def Header.value (bytes : Array UInt8) (h : Header) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate h.valueLength 0
  for i in [:h.valueLength] do
    if h.valueOffset + i < bytes.size then
      out := out.set! i bytes[h.valueOffset + i]!
  return out

/-! ### Universal tag numbers used in X.509. -/

def tagBoolean         : Nat := 0x01
def tagInteger         : Nat := 0x02
def tagBitString       : Nat := 0x03
def tagOctetString     : Nat := 0x04
def tagNull            : Nat := 0x05
def tagObjectId        : Nat := 0x06
def tagUTF8String      : Nat := 0x0C
def tagSequence        : Nat := 0x10
def tagSet             : Nat := 0x11
def tagPrintableString : Nat := 0x13
def tagIA5String       : Nat := 0x16
def tagUTCTime         : Nat := 0x17
def tagGeneralizedTime : Nat := 0x18
def tagBMPString       : Nat := 0x1E

/-! ### High-level helpers. -/

/-- Walk the direct children of a SEQUENCE/SET starting at
    `seqHeader`.  Returns all child headers in order, or
    `none` on malformed input. -/
def children (bytes : Array UInt8) (parent : Header) : Option (Array Header) := Id.run do
  let endOff := parent.endOffset
  let mut out : Array Header := #[]
  let mut p := parent.valueOffset
  while p < endOff do
    match parseHeader bytes p with
    | none => return none
    | some h =>
      if h.endOffset > endOff then return none
      out := out.push h
      p := h.endOffset
  return some out

/-- Read an INTEGER value as a Nat.  Assumes non-negative;
    a leading 0x00 byte (DER padding to disambiguate sign)
    is stripped if present. -/
def readInteger (bytes : Array UInt8) (h : Header) : Nat := Id.run do
  let mut start := h.valueOffset
  let mut len := h.valueLength
  -- Strip DER sign-padding leading 0x00.
  if len > 1 ∧ bytes[start]!.toNat = 0x00 then
    start := start + 1
    len := len - 1
  let mut acc : Nat := 0
  for i in [:len] do
    acc := (acc <<< 8) ||| bytes[start + i]!.toNat
  return acc

/-- Read an OBJECT IDENTIFIER as a list of arc numbers.
    The first two arcs are packed into one byte
    (`first*40 + second`); subsequent arcs use base-128
    encoding with the high bit set on continuation bytes. -/
def readObjectId (bytes : Array UInt8) (h : Header) : Array Nat := Id.run do
  if h.valueLength = 0 then return #[]
  let mut out : Array Nat := #[]
  let b0 := bytes[h.valueOffset]!.toNat
  out := out.push (b0 / 40)
  out := out.push (b0 % 40)
  let mut acc : Nat := 0
  for i in [1:h.valueLength] do
    let b := bytes[h.valueOffset + i]!.toNat
    acc := (acc <<< 7) ||| (b &&& 0x7F)
    if (b &&& 0x80) = 0 then
      out := out.push acc
      acc := 0
  return out

/-- Read a BIT STRING value, dropping the leading
    "number of unused bits" byte.  Returns the raw bit-payload
    as an Array UInt8. -/
def readBitString (bytes : Array UInt8) (h : Header) : Option (Array UInt8) := Id.run do
  if h.valueLength = 0 then return none
  -- First byte = number of unused trailing bits (0..7).
  let _unused := bytes[h.valueOffset]!.toNat
  let mut out : Array UInt8 := Array.replicate (h.valueLength - 1) 0
  for i in [:h.valueLength - 1] do
    out := out.set! i bytes[h.valueOffset + 1 + i]!
  return some out

/-- Read an OCTET STRING value as a byte array. -/
def readOctetString (bytes : Array UInt8) (h : Header) : Array UInt8 :=
  h.value bytes

/-- Check that an OID equals a given list of arcs. -/
def oidEquals (oid : Array Nat) (expected : List Nat) : Bool :=
  oid.toList = expected

/-! ### Well-known OIDs (RFC 5280, RFC 8410). -/

/-- Ed25519: 1.3.101.112 -/
def oidEd25519 : List Nat := [1, 3, 101, 112]

/-- ECDSA with SHA-256 (signature algorithm): 1.2.840.10045.4.3.2 -/
def oidEcdsaWithSha256 : List Nat := [1, 2, 840, 10045, 4, 3, 2]

/-- EC public key algorithm: 1.2.840.10045.2.1 -/
def oidEcPublicKey : List Nat := [1, 2, 840, 10045, 2, 1]

/-- P-256 (secp256r1) curve: 1.2.840.10045.3.1.7 -/
def oidP256 : List Nat := [1, 2, 840, 10045, 3, 1, 7]

/-- RSA encryption: 1.2.840.113549.1.1.1 -/
def oidRsaEncryption : List Nat := [1, 2, 840, 113549, 1, 1, 1]

/-- RSA-PSS: 1.2.840.113549.1.1.10 -/
def oidRsaPss : List Nat := [1, 2, 840, 113549, 1, 1, 10]

/-- SHA-256: 2.16.840.1.101.3.4.2.1 -/
def oidSha256 : List Nat := [2, 16, 840, 1, 101, 3, 4, 2, 1]

end Sparkle.IP.TLS.ASN1
