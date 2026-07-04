/-
  Sim test for IP.Crypto.Bip39.

  Cross-checks against the canonical BIP-39 reference vectors
  from the Trezor test corpus (the spec-defining wallet).

  Vector 1 (the universal BIP-39 sanity check):
    mnemonic   = "abandon abandon abandon abandon abandon abandon
                  abandon abandon abandon abandon abandon about"
    passphrase = "TREZOR"
    seed       =
      c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e534955
      31f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04

  Vector 2 (empty passphrase):
    mnemonic   = same as above
    passphrase = ""
    Expected seed prefix: 5eb00bbddcf069084889a8ab9155568165f5c453ccb85
    (full vector: 5eb00bbddcf069084889a8ab9155568165f5c453ccb85e70811aaed6f6da5fc1
                  9a5ac40b389cd370d086206dec8aa6c43daea6690f20ad3d8d48b2d2ce9e38e4)

  We also smoke-test HMAC-SHA-512 against RFC 4231 test case 1
  (key "Hi There"-style) to verify the HMAC path independently
  of the PBKDF2 wrapper.

  WARNING: each invocation of `mnemonicToSeed` runs 2048
  rounds of HMAC-SHA-512 in pure Lean.  Expect ~10-30 s per
  vector on a workstation.  This is fine for a release-gate
  test (run once per CI build) but you would not want to
  hammer it in a hot loop.
-/

import IP.Crypto.Codec.Bip39

open Sparkle.IP.Crypto.Bip39

namespace Sparkle.Tests.IP.Crypto.Bip39Test

private def hexByte (b : Nat) : String :=
  let lo := b &&& 0xF
  let hi := (b >>> 4) &&& 0xF
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  String.mk [digit hi, digit lo]

private def bytesToHex (bs : Array UInt8) : String := Id.run do
  let mut out := ""
  for b in bs do
    out := out ++ hexByte b.toNat
  return out

def main : IO Unit := do
  IO.println "=== BIP-39 mnemonic → seed sim ==="
  let mut allOk := true

  -- HMAC-SHA-512 sanity (RFC 4231 §4.2 — key 20×0x0b, msg "Hi There")
  let key := Array.replicate 20 (UInt8.ofNat 0x0b)
  let msg := "Hi There".toUTF8.toList.toArray
  let mac := hmacSha512 key msg
  let expectedMac :=
    "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"
  if bytesToHex mac == expectedMac then
    IO.println "  ✓ HMAC-SHA-512 RFC 4231 case 1"
  else
    IO.println "  ✗ HMAC-SHA-512 RFC 4231 case 1"
    IO.println s!"    expected: {expectedMac}"
    IO.println s!"    got     : {bytesToHex mac}"
    allOk := false

  let mnemonic :=
    "abandon abandon abandon abandon abandon abandon " ++
    "abandon abandon abandon abandon abandon about"

  -- BIP-39 vector 1: passphrase = "TREZOR".
  IO.println s!"\n  Running PBKDF2-HMAC-SHA-512 (2048 rounds, may take 10-30 s)..."
  let seed1 := mnemonicToSeed mnemonic "TREZOR"
  let expected1 :=
    "c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04"
  let got1 := bytesToHex seed1
  let mark1 := if got1 == expected1 then "✓" else "✗"
  IO.println s!"  {mark1} BIP-39 vector 1 (passphrase=\"TREZOR\")"
  IO.println s!"    expected: {expected1}"
  IO.println s!"    got     : {got1}"
  if got1 ≠ expected1 then allOk := false

  -- BIP-39 vector 2: empty passphrase.
  IO.println s!"\n  Second PBKDF2 invocation..."
  let seed2 := mnemonicToSeed mnemonic ""
  let expected2 :=
    "5eb00bbddcf069084889a8ab9155568165f5c453ccb85e70811aaed6f6da5fc19a5ac40b389cd370d086206dec8aa6c43daea6690f20ad3d8d48b2d2ce9e38e4"
  let got2 := bytesToHex seed2
  let mark2 := if got2 == expected2 then "✓" else "✗"
  IO.println s!"  {mark2} BIP-39 vector 2 (passphrase=\"\")"
  IO.println s!"    expected: {expected2}"
  IO.println s!"    got     : {got2}"
  if got2 ≠ expected2 then allOk := false

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Bip39Test
