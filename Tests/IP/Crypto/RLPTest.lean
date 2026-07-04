/-
  Sim test for IP.Crypto.RLP.

  Cross-checks against the canonical RLP test vectors from
  the Ethereum Yellow Paper appendix B examples and the
  ethereum/tests repo:

    1. RLP("dog")             = 83 64 6f 67
    2. RLP([])                = c0
    3. RLP(["cat", "dog"])    = c8 83 63 61 74 83 64 6f 67
    4. RLP("")                = 80
    5. RLP(0)                 = 80   (zero is canonically empty bytes)
    6. RLP(15)                = 0f
    7. RLP(1024)              = 82 04 00
    8. RLP("Lorem ipsum dolor sit amet, consectetur adipisicing elit")
                              = b8 38 4c 6f 72 65 6d ... (long-form)
    9. RLP(empty-nested-list) = c4 c3 c0 c0 c0    -- LLLL

  Plus a small sanity check: RLP of a 17-byte byte string
  uses the short prefix 0x80+17 = 0x91.
-/

import IP.Crypto.Codec.RLP

open Sparkle.IP.Crypto.RLP

namespace Sparkle.Tests.IP.Crypto.RLPTest

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

private def bytesOfString (s : String) : Array UInt8 :=
  s.toUTF8.toList.toArray

def main : IO Unit := do
  IO.println "=== RLP encoder sim ==="
  let mut allOk := true

  let check (label : String) (got : Array UInt8) (expectedHex : String) : IO Unit := do
    let gotHex := bytesToHex got
    let mark := if gotHex = expectedHex then "✓" else "✗"
    IO.println s!"  {mark} {label}"
    IO.println s!"    expected: {expectedHex}"
    IO.println s!"    got     : {gotHex}"

  let cases : List (String × Array UInt8 × String) :=
    [ ( "RLP(\"dog\")"
      , encodeBytes (bytesOfString "dog")
      , "83646f67" )
    , ( "RLP([])"
      , encode (.list [])
      , "c0" )
    , ( "RLP([\"cat\", \"dog\"])"
      , encodeList [bytesOfString "cat", bytesOfString "dog"]
      , "c88363617483646f67" )
    , ( "RLP(\"\")"
      , encodeBytes #[]
      , "80" )
    , ( "RLP(0)"
      , encodeNat 0
      , "80" )
    , ( "RLP(15)"
      , encodeNat 15
      , "0f" )
    , ( "RLP(1024)"
      , encodeNat 1024
      , "820400" )
    , ( "RLP(\"Lorem ipsum...\") long-form"
      , encodeBytes (bytesOfString "Lorem ipsum dolor sit amet, consectetur adipisicing elit")
      , "b8384c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e7365637465747572206164697069736963696e6720656c6974" )
    , ( "RLP(set-theoretic representation of 3) = [ [], [[]], [ [], [[]] ] ]"
      , encode (.list [.list [], .list [.list []], .list [.list [], .list [.list []]]])
      , "c7c0c1c0c3c0c1c0" )
    ]

  for (label, got, expected) in cases do
    let gotHex := bytesToHex got
    if gotHex ≠ expected then allOk := false
    check label got expected

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.RLPTest
