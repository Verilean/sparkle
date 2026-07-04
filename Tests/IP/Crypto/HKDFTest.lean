/-
  Sim test for IP.Crypto.HKDF.

  KAT sources:
    * RFC 4231 — HMAC-SHA-256 test vectors
    * RFC 5869 Appendix A — HKDF-SHA-256 test vectors
-/

import IP.Crypto.Codec.HKDF

open Sparkle.IP.Crypto.HKDF

namespace Sparkle.Tests.IP.Crypto.HKDFTest

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
  IO.println "=== HMAC-SHA-256 + HKDF sim ==="

  let mut ok := true

  -- ============================================================
  -- RFC 4231 HMAC-SHA-256 Test Case 1
  -- ============================================================
  let key1 := bytesOfHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
  let data1 := bytesOfHex "4869205468657265"  -- "Hi There"
  let expected1 := "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
  let got1 := hexOfBytes (hmacSha256 key1 data1)
  let ok1 := got1 = expected1
  IO.println s!"  {if ok1 then "✓" else "✗"} RFC 4231 HMAC-SHA-256 Test Case 1"
  IO.println s!"    expected: {expected1}"
  IO.println s!"    got     : {got1}"
  if !ok1 then ok := false

  -- ============================================================
  -- RFC 4231 HMAC-SHA-256 Test Case 2
  --   key = "Jefe"
  --   data = "what do ya want for nothing?"
  --   HMAC = 5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843
  -- ============================================================
  let key2 := "Jefe".toUTF8.toList.toArray
  let data2 := "what do ya want for nothing?".toUTF8.toList.toArray
  let expected2 := "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
  let got2 := hexOfBytes (hmacSha256 key2 data2)
  let ok2 := got2 = expected2
  IO.println s!"  {if ok2 then "✓" else "✗"} RFC 4231 HMAC-SHA-256 Test Case 2"
  IO.println s!"    expected: {expected2}"
  IO.println s!"    got     : {got2}"
  if !ok2 then ok := false

  -- ============================================================
  -- RFC 5869 Appendix A.1 — HKDF-SHA-256 basic
  -- ============================================================
  let ikm := bytesOfHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
  let salt := bytesOfHex "000102030405060708090a0b0c"
  let info := bytesOfHex "f0f1f2f3f4f5f6f7f8f9"
  let prkExp := "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
  let okmExp := "3cb25f25faacd57a90434f64d0362f2a" ++
                "2d2d0a90cf1a5a4c5db02d56ecc4c5bf" ++
                "34007208d5b887185865"
  let prk := hkdfExtract salt ikm
  let okPrk := hexOfBytes prk = prkExp
  IO.println s!"  {if okPrk then "✓" else "✗"} RFC 5869 A.1 — PRK"
  IO.println s!"    expected: {prkExp}"
  IO.println s!"    got     : {hexOfBytes prk}"
  if !okPrk then ok := false
  let okm := hkdfExpand prk info 42
  let okOkm := hexOfBytes okm = okmExp
  IO.println s!"  {if okOkm then "✓" else "✗"} RFC 5869 A.1 — OKM (42 bytes)"
  IO.println s!"    expected: {okmExp}"
  IO.println s!"    got     : {hexOfBytes okm}"
  if !okOkm then ok := false

  -- ============================================================
  -- RFC 5869 Appendix A.2 — HKDF-SHA-256 longer inputs
  -- ============================================================
  let ikm2 := bytesOfHex (
    "000102030405060708090a0b0c0d0e0f" ++
    "101112131415161718191a1b1c1d1e1f" ++
    "202122232425262728292a2b2c2d2e2f" ++
    "303132333435363738393a3b3c3d3e3f" ++
    "404142434445464748494a4b4c4d4e4f")
  let salt2 := bytesOfHex (
    "606162636465666768696a6b6c6d6e6f" ++
    "707172737475767778797a7b7c7d7e7f" ++
    "808182838485868788898a8b8c8d8e8f" ++
    "909192939495969798999a9b9c9d9e9f" ++
    "a0a1a2a3a4a5a6a7a8a9aaabacadaeaf")
  let info2 := bytesOfHex (
    "b0b1b2b3b4b5b6b7b8b9babbbcbdbebf" ++
    "c0c1c2c3c4c5c6c7c8c9cacbcccdcecf" ++
    "d0d1d2d3d4d5d6d7d8d9dadbdcdddedf" ++
    "e0e1e2e3e4e5e6e7e8e9eaebecedeeef" ++
    "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")
  let prkExp2 := "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244"
  let okmExp2 :=
    "b11e398dc80327a1c8e7f78c596a4934" ++
    "4f012eda2d4efad8a050cc4c19afa97c" ++
    "59045a99cac7827271cb41c65e590e09" ++
    "da3275600c2f09b8367793a9aca3db71" ++
    "cc30c58179ec3e87c14c01d5c1f3434f" ++
    "1d87"
  let prk2 := hkdfExtract salt2 ikm2
  let okPrk2 := hexOfBytes prk2 = prkExp2
  IO.println s!"  {if okPrk2 then "✓" else "✗"} RFC 5869 A.2 — PRK"
  IO.println s!"    expected: {prkExp2}"
  IO.println s!"    got     : {hexOfBytes prk2}"
  if !okPrk2 then ok := false
  let okm2 := hkdfExpand prk2 info2 82
  let okOkm2 := hexOfBytes okm2 = okmExp2
  IO.println s!"  {if okOkm2 then "✓" else "✗"} RFC 5869 A.2 — OKM (82 bytes)"
  IO.println s!"    expected: {okmExp2}"
  IO.println s!"    got     : {hexOfBytes okm2}"
  if !okOkm2 then ok := false

  -- ============================================================
  -- RFC 5869 Appendix A.3 — HKDF-SHA-256 zero-length salt and info
  -- ============================================================
  let ikm3 := bytesOfHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
  let prkExp3 := "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"
  let okmExp3 :=
    "8da4e775a563c18f715f802a063c5a31" ++
    "b8a11f5c5ee1879ec3454e5f3c738d2d" ++
    "9d201395faa4b61a96c8"
  let prk3 := hkdfExtract #[] ikm3
  let okPrk3 := hexOfBytes prk3 = prkExp3
  IO.println s!"  {if okPrk3 then "✓" else "✗"} RFC 5869 A.3 — PRK (empty salt)"
  IO.println s!"    expected: {prkExp3}"
  IO.println s!"    got     : {hexOfBytes prk3}"
  if !okPrk3 then ok := false
  let okm3 := hkdfExpand prk3 #[] 42
  let okOkm3 := hexOfBytes okm3 = okmExp3
  IO.println s!"  {if okOkm3 then "✓" else "✗"} RFC 5869 A.3 — OKM (empty info, 42 bytes)"
  IO.println s!"    expected: {okmExp3}"
  IO.println s!"    got     : {hexOfBytes okm3}"
  if !okOkm3 then ok := false

  -- ============================================================
  -- TLS 1.3 HKDF-Expand-Label smoke test (label format only).
  -- We don't have a published TLS 1.3 trace KAT here yet; this
  -- just confirms the call doesn't crash and returns the right
  -- length.  Real KAT moves to T.6 with handshake transcripts.
  -- ============================================================
  let secret := bytesOfHex "0102030405060708090a0b0c0d0e0f10111213141516171819202122232425262"
  let label : Array UInt8 := hkdfExpandLabel secret "derived" #[] 32
  let okLabel := label.size = 32
  IO.println s!"  {if okLabel then "✓" else "✗"} TLS 1.3 HKDF-Expand-Label smoke (32-byte output)"
  if !okLabel then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.HKDFTest
