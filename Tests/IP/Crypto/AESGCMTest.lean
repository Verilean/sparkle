/-
  Sim test for IP.Crypto.AESGCM.

  NIST SP 800-38D Appendix B (also McGrew–Viega GCM paper):

  Test Case 1: empty plaintext, empty AAD
    K   = 00 × 16
    IV  = 00 × 12
    P   = ()
    AAD = ()
    C   = ()
    T   = 58e2fccefa7e3061367f1d57a4e7455a

  Test Case 2: 16-byte zero plaintext, empty AAD
    K   = 00 × 16
    IV  = 00 × 12
    P   = 00 × 16
    AAD = ()
    C   = 0388dace60b6a392f328c2b971b2fe78
    T   = ab6e47d42cec13bdf53a67b21257bddf

  Test Case 3: 64-byte plaintext, empty AAD
    K   = feffe9928665731c6d6a8f9467308308
    IV  = cafebabefacedbaddecaf888
    P   = d9313225f88406e5a55909c5aff5269a
          86a7a9531534f7da2e4c303d8a318a72
          1c3c0c95956809532fcf0e2449a6b525
          b16aedf5aa0de657ba637b391aafd255
    AAD = ()
    C   = 42831ec2217774244b7221b784d0d49c
          e3aa212f2c02a4e035c17e2329aca12e
          21d514b25466931c7d8f6a5aac84aa05
          1ba30b396a0aac973d58e091473f5985
    T   = 4d5c2af327cd64a62cf35abd2ba6fab4

  Test Case 4: 60-byte plaintext + 20-byte AAD (most complete)
    K   = feffe9928665731c6d6a8f9467308308
    IV  = cafebabefacedbaddecaf888
    P   = d9313225f88406e5a55909c5aff5269a
          86a7a9531534f7da2e4c303d8a318a72
          1c3c0c95956809532fcf0e2449a6b525
          b16aedf5aa0de657ba637b39           (60 bytes)
    AAD = feedfacedeadbeeffeedfacedeadbeef
          abaddad2                            (20 bytes)
    C   = 42831ec2217774244b7221b784d0d49c
          e3aa212f2c02a4e035c17e2329aca12e
          21d514b25466931c7d8f6a5aac84aa05
          1ba30b396a0aac973d58e091           (60 bytes)
    T   = 5bc94fbc3221a5db94fae95ae7121a47
-/

import IP.Crypto.Codec.AESGCM

open Sparkle.IP.Crypto.AESGCM

namespace Sparkle.Tests.IP.Crypto.AESGCMTest

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
  label   : String
  keyHex  : String
  ivHex   : String
  pHex    : String
  aadHex  : String
  cHex    : String
  tHex    : String
  deriving Inhabited

private def vectors : List KAT :=
  [ { label  := "NIST Test Case 1 (empty P, empty AAD)"
    , keyHex := "00000000000000000000000000000000"
    , ivHex  := "000000000000000000000000"
    , pHex   := ""
    , aadHex := ""
    , cHex   := ""
    , tHex   := "58e2fccefa7e3061367f1d57a4e7455a" }
  , { label  := "NIST Test Case 2 (16-byte zero P, empty AAD)"
    , keyHex := "00000000000000000000000000000000"
    , ivHex  := "000000000000000000000000"
    , pHex   := "00000000000000000000000000000000"
    , aadHex := ""
    , cHex   := "0388dace60b6a392f328c2b971b2fe78"
    , tHex   := "ab6e47d42cec13bdf53a67b21257bddf" }
  , { label  := "NIST Test Case 3 (64-byte P, empty AAD)"
    , keyHex := "feffe9928665731c6d6a8f9467308308"
    , ivHex  := "cafebabefacedbaddecaf888"
    , pHex   := "d9313225f88406e5a55909c5aff5269a" ++
                "86a7a9531534f7da2e4c303d8a318a72" ++
                "1c3c0c95956809532fcf0e2449a6b525" ++
                "b16aedf5aa0de657ba637b391aafd255"
    , aadHex := ""
    , cHex   := "42831ec2217774244b7221b784d0d49c" ++
                "e3aa212f2c02a4e035c17e2329aca12e" ++
                "21d514b25466931c7d8f6a5aac84aa05" ++
                "1ba30b396a0aac973d58e091473f5985"
    , tHex   := "4d5c2af327cd64a62cf35abd2ba6fab4" }
  , { label  := "NIST Test Case 4 (60-byte P, 20-byte AAD)"
    , keyHex := "feffe9928665731c6d6a8f9467308308"
    , ivHex  := "cafebabefacedbaddecaf888"
    , pHex   := "d9313225f88406e5a55909c5aff5269a" ++
                "86a7a9531534f7da2e4c303d8a318a72" ++
                "1c3c0c95956809532fcf0e2449a6b525" ++
                "b16aedf5aa0de657ba637b39"
    , aadHex := "feedfacedeadbeeffeedfacedeadbeef" ++
                "abaddad2"
    , cHex   := "42831ec2217774244b7221b784d0d49c" ++
                "e3aa212f2c02a4e035c17e2329aca12e" ++
                "21d514b25466931c7d8f6a5aac84aa05" ++
                "1ba30b396a0aac973d58e091"
    , tHex   := "5bc94fbc3221a5db94fae95ae7121a47" } ]

def main : IO Unit := do
  IO.println "=== AES-128-GCM AEAD sim ==="

  let mut ok := true

  for v in vectors do
    let key := bytesOfHex v.keyHex
    let iv := bytesOfHex v.ivHex
    let p := bytesOfHex v.pHex
    let aad := bytesOfHex v.aadHex
    let res := encryptAead key iv p aad
    let gotC := hexOfBytes res.ciphertext
    let gotT := hexOfBytes res.tag
    let okC := gotC = v.cHex
    let okT := gotT = v.tHex
    IO.println s!"  {if okC then "✓" else "✗"} {v.label} — C"
    IO.println s!"    expected: {v.cHex}"
    IO.println s!"    got     : {gotC}"
    IO.println s!"  {if okT then "✓" else "✗"} {v.label} — T"
    IO.println s!"    expected: {v.tHex}"
    IO.println s!"    got     : {gotT}"
    if !(okC ∧ okT) then ok := false

    -- Round-trip: decrypt-and-verify should return the original P.
    match decryptAead key iv res.ciphertext aad res.tag with
    | some p' =>
      let okRt := hexOfBytes p' = v.pHex
      IO.println s!"  {if okRt then "✓" else "✗"} {v.label} — decrypt round-trip"
      if !okRt then ok := false
    | none =>
      IO.println s!"  ✗ {v.label} — decrypt FAILED tag check"
      ok := false

  -- Tag-tamper test: flip a bit in the tag, decrypt should return none.
  let v := vectors[1]!  -- Test Case 2 (has non-empty C)
  let key := bytesOfHex v.keyHex
  let iv := bytesOfHex v.ivHex
  let aad := bytesOfHex v.aadHex
  let c := bytesOfHex v.cHex
  let t := bytesOfHex v.tHex
  let tBad := t.set! 0 (t[0]! ^^^ 1)
  match decryptAead key iv c aad tBad with
  | some _ =>
    IO.println s!"  ✗ tag-tamper test: decrypt accepted bad tag (should reject)"
    ok := false
  | none =>
    IO.println s!"  ✓ tag-tamper test: bad tag rejected"

  -- Ciphertext-tamper test.
  let cBad := c.set! 0 (c[0]! ^^^ 1)
  match decryptAead key iv cBad aad t with
  | some _ =>
    IO.println s!"  ✗ ciphertext-tamper test: decrypt accepted modified C (should reject)"
    ok := false
  | none =>
    IO.println s!"  ✓ ciphertext-tamper test: modified C rejected"

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.AESGCMTest
