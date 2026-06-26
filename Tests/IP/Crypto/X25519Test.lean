/-
  Sim test for IP.Crypto.X25519.

  RFC 7748 §5.2 test vectors (scalar × u):

    Test 1:
      scalar = a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4
      u      = e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c
      output = c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552

    Test 2:
      scalar = 4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d
      u      = e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493
      output = 95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957

  RFC 7748 §6.1 ECDH:
    Alice secret = 77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a
    Alice pub    = 8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a
    Bob secret   = 5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb
    Bob pub      = de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f
    Shared       = 4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742
-/

import IP.Crypto.X25519

open Sparkle.IP.Crypto.X25519

namespace Sparkle.Tests.IP.Crypto.X25519Test

/-- Parse a hex string into a byte array. -/
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

/-- Render a byte array as lowercase hex. -/
private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

structure KAT where
  label    : String
  scalar   : String
  u        : String
  expected : String

private def vectors : List KAT :=
  [ { label    := "RFC 7748 §5.2 test 1"
    , scalar   := "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
    , u        := "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
    , expected := "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552" }
  , { label    := "RFC 7748 §5.2 test 2"
    , scalar   := "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"
    , u        := "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"
    , expected := "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957" } ]

def main : IO Unit := do
  IO.println "=== X25519 scalar mult sim ==="

  let mut ok := true

  for v in vectors do
    let scalar := bytesOfHex v.scalar
    let u := bytesOfHex v.u
    let got := x25519 scalar u
    let gotHex := hexOfBytes got
    let mark := if gotHex = v.expected then "✓" else "✗"
    IO.println s!"  {mark} {v.label}"
    IO.println s!"    expected: {v.expected}"
    IO.println s!"    got     : {gotHex}"
    if gotHex ≠ v.expected then ok := false

  -- RFC 7748 §6.1 ECDH: Alice and Bob derive matching shared secret.
  let aliceSecret := bytesOfHex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
  let alicePubExp := "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
  let bobSecret := bytesOfHex "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"
  let bobPubExp := "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
  let sharedExp := "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"

  let alicePub := x25519Base aliceSecret
  let bobPub := x25519Base bobSecret
  let aliceShared := x25519 aliceSecret bobPub
  let bobShared := x25519 bobSecret alicePub

  let okAlice := hexOfBytes alicePub = alicePubExp
  let okBob := hexOfBytes bobPub = bobPubExp
  let okAS := hexOfBytes aliceShared = sharedExp
  let okBS := hexOfBytes bobShared = sharedExp
  let okMatch := hexOfBytes aliceShared = hexOfBytes bobShared

  IO.println s!"  {if okAlice then "✓" else "✗"} Alice pub = scalar * basePoint"
  IO.println s!"    expected: {alicePubExp}"
  IO.println s!"    got     : {hexOfBytes alicePub}"
  IO.println s!"  {if okBob then "✓" else "✗"} Bob pub = scalar * basePoint"
  IO.println s!"    expected: {bobPubExp}"
  IO.println s!"    got     : {hexOfBytes bobPub}"
  IO.println s!"  {if okAS then "✓" else "✗"} Alice's shared = aliceSecret × bobPub"
  IO.println s!"  {if okBS then "✓" else "✗"} Bob's shared = bobSecret × alicePub"
  IO.println s!"  {if okMatch then "✓" else "✗"} ECDH shared secrets match"

  if !(okAlice ∧ okBob ∧ okAS ∧ okBS ∧ okMatch) then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.X25519Test
