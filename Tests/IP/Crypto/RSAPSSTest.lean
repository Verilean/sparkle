/-
  Sim test for IP.Crypto.RSAPSS.verify.

  KAT generated via OpenSSL 3.6.2 (RSA-2048-PSS-SHA256, sLen=32):
    msg = "hello sparkle TLS world"
    n   = (2048-bit modulus, hex below)
    e   = 65537
    sig = (256-byte PSS signature, hex below)

  This is one instance of `rsa_pss_rsae_sha256` (TLS 1.3 sig
  scheme 0x0804).
-/

import IP.Crypto.Codec.RSAPSS

open Sparkle.IP.Crypto.RSAPSS

namespace Sparkle.Tests.IP.Crypto.RSAPSSTest

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

private def natOfHex (s : String) : Nat := Id.run do
  let chars := s.toList.toArray
  let nibble (c : Char) : Nat :=
    if c.isDigit then c.toNat - 0x30
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 0x61 + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 0x41 + 10
    else 0
  let mut acc : Nat := 0
  for c in chars do
    acc := (acc <<< 4) ||| nibble c
  return acc

def main : IO Unit := do
  IO.println "=== RSA-PSS-SHA256 verify (OpenSSL-generated KAT) ==="

  let mut ok := true

  let n := natOfHex (
    "d5a9d55ccc0fdc53eb48ecf847a805563a3e766029860c86db38556baea46a68" ++
    "6c1ba712e6d98269ceeb1269710f0a5ffa9a5f270ae173220b4d451bed26c167" ++
    "91ca01281e56ae8a9ebe3b6d2ac0034a331eb9600f7e6c29f7d8e3915182ff88" ++
    "d5829108ee3ab53281e6a2c665c948bb0e7e3871595b71c669e32a7fd5b052d9" ++
    "535061050df89e61db29d035fdb8d9bb91215441d7b015cdfed3d92f8dca8713" ++
    "2d6b4a719aa9a223d9d4f5d82b60125a6857c525056932d35ab509fc137f82cd" ++
    "a453ec9467b4a4600e019089cf46cd505462e2f1c018365c930bda31e4f3130c" ++
    "32f8b9b0d5c771acd874cf473c84fec7c235b3655c7e0fa37a5ef29d6d97b375")
  let e := 65537
  let msg : Array UInt8 := "hello sparkle TLS world".toUTF8.toList.toArray
  let sig := bytesOfHex (
    "88c6786b93a8d86ba0db98d4ffafcad497f3286250e548cebb82dfef2ae1e227" ++
    "6083997acd43db547921fb9f88d274ca10adb7f1545869686100e8e3135d373e" ++
    "32bd9541764507e4d29085dfb0b0541f5ac556438ec730a268a4abf65819c551" ++
    "43a595ab6543febdd3f222b02ea583df232a9d9b3c95f68ba2f6fd6b2da1211b" ++
    "e0b3209c4a889155f2830dc2853f2245f02b6fb4c8ca70073cda9315a8e0cc2f" ++
    "45750cc8f0987eb2faa3069e5f802a6803f16cc00e2c4bfe8a34a0c6eec66d4c" ++
    "f34f70edb20c1ae5c139fcbe61d0dbe3733eb268762be476bc75bb09ab4fc9c0" ++
    "62ae40b4b86e91ba4a97632ef84cba2f2336c07a0a2131b0e870c35c086c251d")

  IO.println s!"  modulus bits = {(Nat.log2 n) + 1} (expected ~2048)"
  IO.println s!"  sig length   = {sig.size} (expected 256)"

  -- Verify the genuine signature.
  if verify n e msg sig then
    IO.println "  ✓ OpenSSL-generated RSA-PSS-SHA256 sig verified"
  else
    IO.println "  ✗ valid sig REJECTED (bug)"
    ok := false

  -- Negative test: tampered signature.
  let badSig := sig.set! 5 (sig[5]! ^^^ 1)
  if verify n e msg badSig then
    IO.println "  ✗ tampered sig accepted (bug)"
    ok := false
  else
    IO.println "  ✓ tampered sig rejected"

  -- Negative test: wrong message.
  let badMsg : Array UInt8 := "hello sparkle TLS WRONG".toUTF8.toList.toArray
  if verify n e badMsg sig then
    IO.println "  ✗ wrong msg accepted (bug)"
    ok := false
  else
    IO.println "  ✓ wrong msg rejected"

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.RSAPSSTest
