/-
  Sim test for IP.Crypto.Bip32.

  Cross-checks against the canonical BIP-32 reference vectors
  (BIP-32 spec, "Test Vectors" §1) from a known seed:

    seed = 000102030405060708090a0b0c0d0e0f

  Master key:
    privKey   = e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35
    chainCode = 873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508

  Chain m/0' (hardened child 0):
    privKey   = edb2e14f9ee77d26dd93b4ecede8d16ed408ce149b6cd80b0715a2d911a0afea
    chainCode = 47fdacbd0f1097043b78c63c20c34ef4ed9a111d980047ad16282c7ae6236141

  Chain m/0'/1 (non-hardened child 1 of above):
    privKey   = 3c6cb8d0f6a264c91ea8b5030fadaa8e538b020f0a387421a12de9319dc93368
    chainCode = 2a7857631386ba23dacac34180dd1983734e444fdbf774041578e9b6adb37c19

  This walks the spec's first 3 levels — enough to exercise
  both hardened and non-hardened CKDpriv branches in one
  pass, which would catch wiring bugs in either branch.
-/

import IP.Crypto.Bip32

open Sparkle.IP.Crypto.Bip32

namespace Sparkle.Tests.IP.Crypto.Bip32Test

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

private def natToHex32 (k : Nat) : String := Id.run do
  let mut bs : Array UInt8 := #[]
  let mut x := k
  for _ in [:32] do
    bs := bs.push (UInt8.ofNat (x &&& 0xFF))
    x := x >>> 8
  bytesToHex bs.reverse

/-- Parse a hex string ("00010203…") into a byte array. -/
private def hexToBytes (s : String) : Array UInt8 := Id.run do
  let chars := s.toList.toArray
  let mut out : Array UInt8 := #[]
  let mut i := 0
  while i + 1 < chars.size do
    let c1 := chars.getD i '0'
    let c2 := chars.getD (i + 1) '0'
    let hexDigit (c : Char) : Nat :=
      if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then 10 + c.toNat - 'a'.toNat
      else if 'A' ≤ c ∧ c ≤ 'F' then 10 + c.toNat - 'A'.toNat
      else 0
    out := out.push (UInt8.ofNat (hexDigit c1 * 16 + hexDigit c2))
    i := i + 2
  return out

def main : IO Unit := do
  IO.println "=== BIP-32 HD wallet sim ==="
  let mut allOk := true

  let seed := hexToBytes "000102030405060708090a0b0c0d0e0f"
  let master := masterKey seed
  let masterPrivHex := natToHex32 master.privKey
  let masterChainHex := bytesToHex master.chainCode
  let expectedPriv := "e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35"
  let expectedChain := "873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508"

  if masterPrivHex == expectedPriv ∧ masterChainHex == expectedChain then
    IO.println "  ✓ master key (m)"
  else
    IO.println "  ✗ master key (m)"
    IO.println s!"    expectedPriv : {expectedPriv}"
    IO.println s!"    gotPriv      : {masterPrivHex}"
    IO.println s!"    expectedChain: {expectedChain}"
    IO.println s!"    gotChain     : {masterChainHex}"
    allOk := false

  -- m/0' — hardened child 0.  Slow: this requires a secp256k1
  -- scalar mul for the public-key derivation (well — actually
  -- the hardened branch uses ser256(privKey) directly and
  -- does NOT need the public key, so this is fast).
  match ckdPriv master (0 + (1 <<< 31)) with
  | none =>
    IO.println "  ✗ m/0' returned none (I_L ≥ n, unlikely)"
    allOk := false
  | some child1 =>
    let privHex := natToHex32 child1.privKey
    let chainHex := bytesToHex child1.chainCode
    let expectedPriv1 := "edb2e14f9ee77d26dd93b4ecede8d16ed408ce149b6cd80b0715a2d911a0afea"
    let expectedChain1 := "47fdacbd0f1097043b78c63c20c34ef4ed9a111d980047ad16282c7ae6236141"
    if privHex == expectedPriv1 ∧ chainHex == expectedChain1 then
      IO.println "  ✓ m/0' (hardened child)"
    else
      IO.println "  ✗ m/0' (hardened child)"
      IO.println s!"    expectedPriv : {expectedPriv1}"
      IO.println s!"    gotPriv      : {privHex}"
      IO.println s!"    expectedChain: {expectedChain1}"
      IO.println s!"    gotChain     : {chainHex}"
      allOk := false

    -- m/0'/1 — non-hardened child 1.  Needs a secp256k1
    -- scalar mul on the parent's privKey to get its public
    -- key for serP(...).  This is the slow path; expect
    -- 30-90 s on pure-Lean secp256k1.
    IO.println "\n  Running m/0'/1 (needs secp256k1 scalar mul; may take ~minute)..."
    match ckdPriv child1 1 with
    | none =>
      IO.println "  ✗ m/0'/1 returned none"
      allOk := false
    | some child2 =>
      let privHex2 := natToHex32 child2.privKey
      let chainHex2 := bytesToHex child2.chainCode
      let expectedPriv2 := "3c6cb8d0f6a264c91ea8b5030fadaa8e538b020f0a387421a12de9319dc93368"
      let expectedChain2 := "2a7857631386ba23dacac34180dd1983734e444fdbf774041578e9b6adb37c19"
      if privHex2 == expectedPriv2 ∧ chainHex2 == expectedChain2 then
        IO.println "  ✓ m/0'/1 (non-hardened child)"
      else
        IO.println "  ✗ m/0'/1 (non-hardened child)"
        IO.println s!"    expectedPriv : {expectedPriv2}"
        IO.println s!"    gotPriv      : {privHex2}"
        IO.println s!"    expectedChain: {expectedChain2}"
        IO.println s!"    gotChain     : {chainHex2}"
        allOk := false

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Bip32Test
