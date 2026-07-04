/-
  Sim test for IP.Crypto.Ed25519Sign — validates against
  RFC 8032 §7.1 test vector 1 (the empty-message vector).

    secret key : 9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60
    public key : d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a
    message    : ""
    signature  : e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065
                 224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bdfa9
                 87599f9f5d2c87d8

  This validates the entire stack:
    SHA-512 padding & compression
      → scalar clamp & little-endian decode
        → curve point base · scalar  (252-iteration scalar mult)
          → point encoding (y || x-parity)
            → SHA-512 over (R || A || M)
              → S = (r + k·a) mod l
                → RFC 8032 byte sequence
-/

import IP.Crypto.Proof.Ed25519Sign

open Sparkle.IP.Crypto.Ed25519Sign

namespace Sparkle.Tests.IP.Crypto.Ed25519SignTest

/-- Parse a hex string into a byte array. -/
def hexToBytes (s : String) : Array UInt8 := Id.run do
  let mut bytes : Array UInt8 := #[]
  let cs := s.toList
  let mut i : Nat := 0
  while i + 1 < cs.length do
    let hi := (cs.getD i (Char.ofNat 0)).toNat
    let lo := (cs.getD (i + 1) (Char.ofNat 0)).toNat
    let toDigit (c : Nat) : Nat :=
      if c ≥ 0x30 ∧ c ≤ 0x39 then c - 0x30
      else if c ≥ 0x61 ∧ c ≤ 0x66 then c - 0x61 + 10
      else if c ≥ 0x41 ∧ c ≤ 0x46 then c - 0x41 + 10
      else 0
    let b := (toDigit hi <<< 4) ||| toDigit lo
    bytes := bytes.push (UInt8.ofNat b)
    i := i + 2
  return bytes

def bytesToHex (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

/-! ### RFC 8032 §7.1 Test 1. -/
private def secret1 : String :=
  "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
private def public1 : String :=
  "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
private def sig1 : String :=
  "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"

def main : IO Unit := do
  IO.println "=== Ed25519 sign sim (RFC 8032 §7.1 Test 1) ==="
  let mut allOk := true

  let priv := hexToBytes secret1
  let expectedPub := hexToBytes public1
  let expectedSig := hexToBytes sig1

  -- Public key derivation.
  IO.println "  computing public key (~30s for the 252-bit scalar mult)..."
  let pub := derivePublicKey priv
  let pubHex := bytesToHex pub
  let pubOk := pub == expectedPub
  IO.println s!"  expected pub: {public1}"
  IO.println s!"  got      pub: {pubHex}"
  if pubOk then
    IO.println "    ✓ public key matches RFC 8032 vector"
  else
    IO.println "    ✗ public key mismatch"
    allOk := false

  -- Sign empty message.
  IO.println "  signing empty message (~60s — two more scalar mults plus SHA-512)..."
  let signedRaw := sign priv #[]
  let signedHex := bytesToHex signedRaw
  let sigOk := signedRaw == expectedSig
  IO.println s!"  expected sig: {sig1}"
  IO.println s!"  got      sig: {signedHex}"
  if sigOk then
    IO.println "    ✓ signature matches RFC 8032 Test 1"
  else
    IO.println "    ✗ signature mismatch"
    allOk := false

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Ed25519SignTest
