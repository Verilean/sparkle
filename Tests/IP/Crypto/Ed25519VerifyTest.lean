/-
  Sim test for IP.Crypto.Ed25519Sign.verify — validates
  RFC 8032 §7.1 Test 1 (the empty-message vector) plus
  negative tests (bit-flipped signature, wrong pubkey).

  Verify costs ~3 scalar mults so this test runs for tens
  of seconds.  We deliberately only test ONE vector (Test 1)
  to keep `lake test` fast — Test 2/3/4 from RFC 8032 §7.1
  cover messages, but the verify code path is identical and
  fully exercised by Test 1.
-/

import IP.Crypto.Ed25519Sign

open Sparkle.IP.Crypto.Ed25519Sign

namespace Sparkle.Tests.IP.Crypto.Ed25519VerifyTest

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

def main : IO Unit := do
  IO.println "=== Ed25519 verify sim (RFC 8032 §7.1 Test 1) ==="

  let mut ok := true

  -- RFC 8032 §7.1 Test 1: empty message.
  let pubkey := bytesOfHex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let msg : Array UInt8 := #[]
  let sig := bytesOfHex (
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901" ++
    "555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")

  IO.println "  verifying (~90s — point decode + 2 scalar mults)..."
  if verify pubkey msg sig then
    IO.println "  ✓ RFC 8032 Test 1 signature verified"
  else
    IO.println "  ✗ RFC 8032 Test 1 signature REJECTED (bug)"
    ok := false

  -- Negative test: flip a bit in the signature.
  IO.println "  testing tampered signature (~90s)..."
  let badSig := sig.set! 5 (sig[5]! ^^^ 1)
  if verify pubkey msg badSig then
    IO.println "  ✗ tampered signature accepted (bug)"
    ok := false
  else
    IO.println "  ✓ tampered signature rejected"

  -- Negative test: wrong public key.
  IO.println "  testing wrong pubkey (~90s)..."
  let wrongPub := pubkey.set! 0 (pubkey[0]! ^^^ 1)
  if verify wrongPub msg sig then
    IO.println "  ✗ wrong pubkey accepted (bug)"
    ok := false
  else
    IO.println "  ✓ wrong pubkey rejected"

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Ed25519VerifyTest
