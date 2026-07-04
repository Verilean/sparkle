/-
  IP.Crypto.CBOR — CTAP2-subset canonical CBOR encoder (RFC 8949).

  FIDO2/CTAP2 messages are CBOR.  CTAP2 mandates the *canonical*
  (CTAP2 "deterministic") form:
    * definite-length arrays / maps only,
    * integers / lengths encoded in the SHORTEST form,
    * map keys sorted by their canonically-encoded byte order
      (shorter encodings first, then lexicographic).

  We implement exactly the subset a minimal authenticator emits:
  unsigned ints, negative ints (for COSE labels like -7), byte
  strings, text strings, arrays, and maps.

  The initial byte is `(major << 5) | additionalInfo`, where the
  argument (an unsigned value: the int itself, or a length) is
  encoded like RLP's length-class prefix (`RLP.encodeLength`):
    0..23   inline in additionalInfo
    24      +1 byte    (0x18)
    25      +2 bytes   (0x19)
    26      +4 bytes   (0x1a)
    27      +8 bytes   (0x1b)
-/
import IP.Crypto.Codec.RLP

namespace Sparkle.IP.Crypto.CBOR

/-- Major types. -/
def majUint : UInt8 := 0   -- unsigned integer
def majNint : UInt8 := 1   -- negative integer
def majBstr : UInt8 := 2   -- byte string
def majTstr : UInt8 := 3   -- text string
def majArray : UInt8 := 4  -- array
def majMap : UInt8 := 5    -- map

/-- Big-endian `arg` in exactly `w` bytes (zero-padded). -/
private def bePad (arg : Nat) (w : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for i in [:w] do
    out := out.push (UInt8.ofNat ((arg >>> ((w - 1 - i) * 8)) &&& 0xFF))
  return out

/-- The CBOR head: `(major << 5) | ai` followed by 0/1/2/4/8
    argument bytes, in the shortest form. -/
def hdr (major : UInt8) (arg : Nat) : Array UInt8 :=
  let m := major.toNat <<< 5
  if arg < 24 then
    #[UInt8.ofNat (m ||| arg)]
  else if arg < 0x100 then
    #[UInt8.ofNat (m ||| 24)] ++ bePad arg 1
  else if arg < 0x10000 then
    #[UInt8.ofNat (m ||| 25)] ++ bePad arg 2
  else if arg < 0x100000000 then
    #[UInt8.ofNat (m ||| 26)] ++ bePad arg 4
  else
    #[UInt8.ofNat (m ||| 27)] ++ bePad arg 8

/-- Unsigned integer. -/
def uint (n : Nat) : Array UInt8 := hdr majUint n

/-- Negative integer `-1 - n₀` for `n₀ ≥ 0`; the CBOR argument is
    `-1 - value`.  E.g. COSE alg ES256 = -7 → `negInt 7` (arg 6). -/
def negIntOfMag (mag : Nat) : Array UInt8 :=
  -- value = -(mag);  arg encoded = mag - 1.
  hdr majNint (mag - 1)

/-- Byte string. -/
def bstr (b : Array UInt8) : Array UInt8 := hdr majBstr b.size ++ b

/-- Text string (ASCII). -/
def tstr (s : String) : Array UInt8 :=
  let b := s.toUTF8.toList.toArray
  hdr majTstr b.size ++ b

/-- Definite-length array of already-encoded items. -/
def array (items : List (Array UInt8)) : Array UInt8 :=
  hdr majArray items.length ++ (items.foldl (· ++ ·) (#[] : Array UInt8))

/-- Canonical key ordering: shorter encoded key first, then
    bytewise lexicographic (CTAP2 length-first rule). -/
private def keyLe (a b : Array UInt8) : Bool :=
  if a.size ≠ b.size then a.size < b.size
  else Id.run do
    for i in [:a.size] do
      let x := a[i]!; let y := b[i]!
      if x ≠ y then return x < y
    return true

/-- Definite-length map from already-encoded `(key, value)` pairs.
    Keys are re-sorted into CTAP2 canonical order so callers may
    pass pairs in any order. -/
def mapPairs (pairs : List (Array UInt8 × Array UInt8)) : Array UInt8 :=
  let sorted := pairs.toArray.qsort (fun p q => keyLe p.1 q.1) |>.toList
  hdr majMap sorted.length ++
    (sorted.foldl (fun acc (k, v) => acc ++ k ++ v) (#[] : Array UInt8))

end Sparkle.IP.Crypto.CBOR
