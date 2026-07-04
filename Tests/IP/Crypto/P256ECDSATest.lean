/-
  Sim test for IP.Crypto.P256ECDSA.verify.

  RFC 6979 §A.2.5 test vector (P-256, SHA-256, msg="sample"):
    pub.x  = 60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6
    pub.y  = 7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299
    digest = AF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF
    r      = EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716
    s      = F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8
-/

import IP.Crypto.Proof.P256ECDSA

open Sparkle.IP.Crypto.P256ECDSA
open Sparkle.IP.Crypto.P256Point (Point)

namespace Sparkle.Tests.IP.Crypto.P256ECDSATest

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
  IO.println "=== ECDSA P-256 verify sim (RFC 6979 §A.2.5) ==="

  let mut ok := true

  let pubX := natOfHex "60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6"
  let pubY := natOfHex "7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299"
  let q : Point := .affine pubX pubY
  let z := natOfHex "AF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF"
  let r := natOfHex "EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716"
  let s := natOfHex "F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8"

  -- Verify the valid signature.
  IO.println "  verifying valid signature (~minutes — 3 scalar mults)..."
  if verify q z r s then
    IO.println "  ✓ RFC 6979 §A.2.5 sig verified"
  else
    IO.println "  ✗ valid sig REJECTED (bug)"
    ok := false

  -- Negative test: bit-flip in r.
  IO.println "  testing tampered sig (~minutes)..."
  let badR := r ^^^ 1
  if verify q z badR s then
    IO.println "  ✗ tampered r accepted (bug)"
    ok := false
  else
    IO.println "  ✓ tampered r rejected"

  -- Negative test: wrong message digest.
  IO.println "  testing wrong digest (~minutes)..."
  let badZ := z ^^^ 1
  if verify q badZ r s then
    IO.println "  ✗ wrong digest accepted (bug)"
    ok := false
  else
    IO.println "  ✓ wrong digest rejected"

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.P256ECDSATest
