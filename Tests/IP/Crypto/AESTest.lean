/-
  Sim test for IP.Crypto.AES (AES-128 only for now).

  FIPS 197 Appendix B (worked example):
    key       = 2b7e151628aed2a6abf7158809cf4f3c
    plaintext = 3243f6a8885a308d313198a2e0370734
    ciphertext= 3925841d02dc09fbdc118597196a0b32

  FIPS 197 Appendix C.1 (KAT):
    key       = 000102030405060708090a0b0c0d0e0f
    plaintext = 00112233445566778899aabbccddeeff
    ciphertext= 69c4e0d86a7b0430d8cdb78070b4c55a

  Round-trip: encrypt then decrypt yields the plaintext.
-/

import IP.Crypto.Codec.AES

open Sparkle.IP.Crypto.AES

namespace Sparkle.Tests.IP.Crypto.AESTest

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

structure KAT where
  label    : String
  key      : String
  plain    : String
  cipher   : String

private def vectors : List KAT :=
  [ { label  := "FIPS 197 Appendix B"
    , key    := "2b7e151628aed2a6abf7158809cf4f3c"
    , plain  := "3243f6a8885a308d313198a2e0370734"
    , cipher := "3925841d02dc09fbdc118597196a0b32" }
  , { label  := "FIPS 197 Appendix C.1"
    , key    := "000102030405060708090a0b0c0d0e0f"
    , plain  := "00112233445566778899aabbccddeeff"
    , cipher := "69c4e0d86a7b0430d8cdb78070b4c55a" } ]

def main : IO Unit := do
  IO.println "=== AES-128 sim ==="

  let mut ok := true

  for v in vectors do
    let key := bytesOfHex v.key
    let plain := bytesOfHex v.plain
    let got := encryptBlock key plain
    let gotHex := hexOfBytes got
    let okEnc := gotHex = v.cipher
    let mark := if okEnc then "✓" else "✗"
    IO.println s!"  {mark} {v.label} — encrypt"
    IO.println s!"    expected: {v.cipher}"
    IO.println s!"    got     : {gotHex}"
    if !okEnc then ok := false

    -- Round-trip: decrypt(encrypt(p)) = p
    let back := decryptBlock key got
    let backHex := hexOfBytes back
    let okDec := backHex = v.plain
    let mark2 := if okDec then "✓" else "✗"
    IO.println s!"  {mark2} {v.label} — decrypt round-trip"
    IO.println s!"    expected: {v.plain}"
    IO.println s!"    got     : {backHex}"
    if !okDec then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.AESTest
