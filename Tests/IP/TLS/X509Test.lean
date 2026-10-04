/-
  Sim test for IP.TLS.X509.extractEd25519Pubkey.

  Validates extraction against:
    1. A canonical Ed25519 SubjectPublicKeyInfo block
       (RFC 8410 §4 minimal example).
    2. The same SPKI embedded inside a larger byte string
       (simulating a full X.509 cert with TBSCertificate
       prefix and signature suffix wrapping the SPKI).
    3. Negative cases: cert with no Ed25519 marker.
-/

import IP.TLS.X509

open Sparkle.IP.TLS.X509

namespace Sparkle.Tests.IP.TLS.X509Test

private def bytesOfHex (s : String) : Array UInt8 := Id.run do
  let chars := s.toList.toArray
  let nibble (c : Char) : Nat :=
    if c.isDigit then c.toNat - 0x30
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 0x61 + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 0x41 + 10
    else 0
  let mut out : Array UInt8 := #[]
  let n := chars.size / 2
  for i in [:n] do
    let hi := nibble chars[2 * i]!
    let lo := nibble chars[2 * i + 1]!
    out := out.push (UInt8.ofNat (hi * 16 + lo))
  return out

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

def main : IO Unit := do
  IO.println "=== X.509 Ed25519 SPKI extraction sim ==="

  let mut ok := true

  -- The published RFC 8410 §10.1 sample Ed25519 SubjectPublicKeyInfo:
  --   30 2a 30 05 06 03 2b 65 70 03 21 00 <32 byte pubkey>
  -- Outer SEQUENCE (0x30 0x2a), then AlgorithmIdentifier
  -- SEQUENCE, then OID, then BIT STRING with the key.
  let samplePubkey : Array UInt8 := bytesOfHex
    "19bf44096984cdfe8541bac167dc3b96c85086aa30b6b6cb0c5c38ad703166e1"
  let spki : Array UInt8 :=
    #[0x30, 0x2a]                              -- SubjectPublicKeyInfo SEQUENCE, length 42
    ++ #[0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70]  -- AlgorithmIdentifier
    ++ #[0x03, 0x21, 0x00]                     -- BIT STRING, length 33, 0 unused bits
    ++ samplePubkey

  -- Test 1: extract from bare SPKI.
  match extractEd25519Pubkey spki with
  | some pub =>
    if pub = samplePubkey then
      IO.println "  ✓ extracted from bare SPKI"
    else
      IO.println s!"  ✗ extracted bytes don't match: got {hexOfBytes pub}"
      ok := false
  | none =>
    IO.println "  ✗ failed to find Ed25519 SPKI in bare encoding"
    ok := false

  -- Test 2: embed inside a larger cert-like blob.
  let tbsBytes := bytesOfHex (
    -- Synthetic TBSCertificate prefix (won't parse as real cert,
    -- but mimics ~100 bytes of "stuff before SPKI").
    "30820150a003020102020900b69e1a3f5e72f6b8300d06092a864886f70d01" ++
    "01050500301c310b3009060355040613024a50310d300b060355040a13044a" ++
    "534c3220301e170d3232303130313030303030305a170d3332303130313030" ++
    "3030305a301c310b3009060355040613024a50310d300b060355040a13044a")
  let suffix := bytesOfHex (
    -- Synthetic signature suffix.
    "300d06092a864886f70d01010505000382010100abcdef0123456789abcdef" ++
    "0123456789abcdef0123456789abcdef")
  let fullCert := tbsBytes ++ spki ++ suffix
  match extractEd25519Pubkey fullCert with
  | some pub =>
    if pub = samplePubkey then
      IO.println s!"  ✓ extracted from embedded SPKI ({fullCert.size}-byte blob)"
    else
      IO.println s!"  ✗ embedded extraction mismatch"
      ok := false
  | none =>
    IO.println "  ✗ failed to find Ed25519 SPKI in embedded cert"
    ok := false

  -- Test 3: negative — no Ed25519 marker present.
  let noMarker := bytesOfHex (
    "30820150a00302010202090012345678300d06092a864886f70d0101050500" ++
    "301c310b3009060355040613024a50310d300b060355040a13044a534c322")
  match extractEd25519Pubkey noMarker with
  | none =>
    IO.println "  ✓ correctly rejected blob without Ed25519 marker"
  | some _ =>
    IO.println "  ✗ false-positive extraction"
    ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.TLS.X509Test
