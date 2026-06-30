/-
  Sim test for IP.Crypto.Keccak256 (Ethereum Keccak-256).

  Validates the pure-data Keccak-256 against the canonical
  test vectors that every Ethereum library cross-checks against:

    1. keccak256("") =
       c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
    2. keccak256("abc") =
       4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
    3. keccak256("testing") =
       5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02
    4. ERC-20 `Transfer(address,address,uint256)` event topic =
       ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
       — checks the keccak-of-canonical-signature path used to
       derive ABI event topics.

  Source: ethereum/tests, web3.utils.keccak256, OpenZeppelin
  ERC-20 reference.
-/

import IP.Crypto.Keccak256

open Sparkle.IP.Crypto.Keccak256

namespace Sparkle.Tests.IP.Crypto.Keccak256Test

private def bytesOfString (s : String) : Array UInt8 :=
  s.toUTF8.toList.toArray

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
  IO.println "=== Keccak-256 (Ethereum) pure-data sim ==="

  let mut allOk := true
  let cases : List (String × String × String) :=
    [ ( ""
      , "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
      , "empty string" )
    , ( "abc"
      , "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
      , "\"abc\"" )
    , ( "testing"
      , "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
      , "\"testing\"" )
    , ( "Transfer(address,address,uint256)"
      , "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef"
      , "ERC-20 Transfer event topic" ) ]

  for (input, expected, label) in cases do
    let got := bytesToHex (keccak256OfBytes (bytesOfString input))
    let mark := if got = expected then "✓" else "✗"
    IO.println s!"  {mark} {label}"
    IO.println s!"    expected: {expected}"
    IO.println s!"    got     : {got}"
    if got ≠ expected then allOk := false

  -- Multi-block stress: 200 'a' bytes is one full 136-byte
  -- block plus 64 bytes spilled into the second, exercising
  -- the absorb loop's block-boundary handling.
  let manyAs : Array UInt8 := Array.replicate 200 (UInt8.ofNat 0x61)
  let got200 := keccak256OfBytes manyAs
  let allZero := got200.all (fun b => b = 0)
  if allZero then
    IO.println "  ✗ 200 'a' bytes: digest is all zeros (bug)"
    allOk := false
  else
    IO.println s!"  ✓ 200 'a' bytes: multi-block digest = {bytesToHex got200}"

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Keccak256Test
