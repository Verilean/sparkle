/-
  Sim test for IP.Crypto.GHASH.

  NIST AES-GCM test vectors (NIST SP 800-38D, also
  McGrew–Viega GCM paper Appendix B):

  Test Case 1: empty AAD, empty C
    K = 00 × 16
    H = 66e94bd4ef8a2c3b884cfa59ca342b2e   (= AES-128(0, 0))
    AAD = ()
    C   = ()
    GHASH = 00000000000000000000000000000000

  Test Case 2: empty AAD, single zero block
    K = 00 × 16
    H = 66e94bd4ef8a2c3b884cfa59ca342b2e
    AAD = ()
    C   = 0388dace60b6a392f328c2b971b2fe78
    GHASH = f38cbb1ad69223dcc3457ae5b6b0f885

  Test Case 3: 4 blocks of plaintext, no AAD
    K = feffe9928665731c6d6a8f9467308308
    H = b83b533708bf535d0aa6e52980d53b78
    AAD = ()
    C   = 42831ec2217774244b7221b784d0d49c
          e3aa212f2c02a4e035c17e2329aca12e
          21d514b25466931c7d8f6a5aac84aa05
          1ba30b396a0aac973d58e091473f5985
    GHASH = 7f1b32b81b820d02614f8895ac1d4eac

  These match Table I of McGrew–Viega and NIST SP 800-38D
  Appendix B.
-/

import IP.Crypto.GHASH

open Sparkle.IP.Crypto.GHASH

namespace Sparkle.Tests.IP.Crypto.GHASHTest

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

private def hOfHex (s : String) : BitVec 128 := bytesToBlock (bytesOfHex s)

structure KAT where
  label    : String
  hHex     : String
  aadHex   : String
  cHex     : String
  expected : String

private def vectors : List KAT :=
  [ { label    := "NIST Test Case 1 (empty AAD, empty C)"
    , hHex     := "66e94bd4ef8a2c3b884cfa59ca342b2e"
    , aadHex   := ""
    , cHex     := ""
    , expected := "00000000000000000000000000000000" }
  , { label    := "NIST Test Case 2 (empty AAD, 16-byte C)"
    , hHex     := "66e94bd4ef8a2c3b884cfa59ca342b2e"
    , aadHex   := ""
    , cHex     := "0388dace60b6a392f328c2b971b2fe78"
    , expected := "f38cbb1ad69223dcc3457ae5b6b0f885" }
  , { label    := "NIST Test Case 3 (empty AAD, 4 × 16-byte C)"
    , hHex     := "b83b533708bf535d0aa6e52980d53b78"
    , aadHex   := ""
    , cHex     := "42831ec2217774244b7221b784d0d49c" ++
                  "e3aa212f2c02a4e035c17e2329aca12e" ++
                  "21d514b25466931c7d8f6a5aac84aa05" ++
                  "1ba30b396a0aac973d58e091473f5985"
    , expected := "7f1b32b81b820d02614f8895ac1d4eac" } ]

def main : IO Unit := do
  IO.println "=== GHASH (GF(2^128)) sim ==="

  let mut ok := true

  for v in vectors do
    let h := hOfHex v.hHex
    let aad := bytesOfHex v.aadHex
    let c := bytesOfHex v.cHex
    let got := ghashFull h aad c
    let gotHex := hexOfBytes (blockToBytes got)
    let okV := gotHex = v.expected
    let mark := if okV then "✓" else "✗"
    IO.println s!"  {mark} {v.label}"
    IO.println s!"    expected: {v.expected}"
    IO.println s!"    got     : {gotHex}"
    if !okV then ok := false

  -- Sanity: gmul is commutative (GF(2^n) multiplication is)
  let a := bytesToBlock (bytesOfHex "0102030405060708090a0b0c0d0e0f10")
  let b := bytesToBlock (bytesOfHex "1112131415161718191a1b1c1d1e1f20")
  let ab := gmul a b
  let ba := gmul b a
  let okComm := ab = ba
  IO.println s!"  {if okComm then "✓" else "✗"} gmul commutative on random pair"
  if !okComm then ok := false

  -- Sanity: gmul X 0 = 0
  let z := gmul a 0
  let okZero := z = 0
  IO.println s!"  {if okZero then "✓" else "✗"} gmul x 0 = 0"
  if !okZero then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.GHASHTest
