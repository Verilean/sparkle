/-
  Test for the FIDO2/CTAP2 pure data layer (M1).

  Validates the byte layouts a minimal authenticator emits, BEFORE
  any hardware, so the HW milestones have a locked reference:

  1. `authenticatorData` structure — exact field offsets.
  2. DER signature round-trips through `P256ECDSA.parseDerSignature`.
  3. END-TO-END: sign `authData ‖ clientDataHash` with P-256 and
     verify with the derived public key — the golden oracle that
     ties the hash, the signature, and the encoded bytes together.
  4. CBOR canonical map-key ordering + COSE key shape.

  Pure-data only (no `#synthesizeVerilog`, no iverilog) — this is
  the byte-layout lock, like the RLP / SHA-256 pure layers.
-/
import IP.Crypto.CTAP2Data
import IP.Crypto.CBOR
import IP.Crypto.DerSig
import IP.Crypto.P256ECDSA
import IP.Crypto.P256Point

open Sparkle.IP.Crypto.CTAP2Data
open Sparkle.IP.Crypto

namespace Sparkle.Tests.IP.Crypto.CTAP2DataTest

private def hex (bs : Array UInt8) : String := Id.run do
  let d := fun n => "0123456789abcdef".toList.getD n '?'
  let mut s := ""
  for b in bs do s := s.push (d (b.toNat / 16)) |>.push (d (b.toNat % 16))
  return s

/-- Fixed test fixtures. -/
private def rpId : String := "example.com"
private def d : Nat := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
private def k : Nat := 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
private def clientDataHash : Array UInt8 := Array.replicate 32 0xAB
private def aaguid : Array UInt8 := Array.replicate 16 0x00
private def credId : Array UInt8 := Array.replicate 16 0x42
private def signCount : Nat := 1

def main : IO Unit := do
  IO.println "=== FIDO2/CTAP2 pure data layer — byte-layout + end-to-end check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- Public key coordinates from the private scalar.
  let (qx, qy) := match P256ECDSA.derivePublicKey d with
    | .affine x y => (x, y)
    | .infinity   => (0, 0)

  -- rpIdHash = SHA-256(rpId).
  let rpIdHash := sha256Bytes rpId.toUTF8.toList.toArray

  -- ---- 1. authenticatorData layout ----
  let attCred := attestedCredData aaguid credId qx qy
  let authDataMC := authenticatorData rpIdHash flagsMakeCred signCount (some attCred)
  let authDataGA := authenticatorData rpIdHash flagsGetAssertion signCount none
  -- getAssertion authData is exactly 37 bytes (32+1+4).
  if authDataGA.size == 37 then
    IO.println "  ✓ getAssertion authData is 37 bytes"
  else
    IO.println s!"  ✗ getAssertion authData size = {authDataGA.size} (expect 37)"; ok := false
  -- field offsets: [0:32]=rpIdHash, [32]=flags, [33:37]=signCount BE.
  let rpMatch := (authDataGA.extract 0 32) == rpIdHash
  let flagMatch := authDataGA[32]! == flagsGetAssertion
  let scMatch := (authDataGA.extract 33 37) == #[0,0,0,1]
  if rpMatch && flagMatch && scMatch then
    IO.println "  ✓ authData fields (rpIdHash‖flags‖signCount) at correct offsets"
  else
    IO.println s!"  ✗ authData field mismatch rp={rpMatch} flag={flagMatch} sc={scMatch}"; ok := false
  -- makeCredential authData starts with the same 37 bytes then attCred.
  if (authDataMC.extract 0 37) == (authenticatorData rpIdHash flagsMakeCred signCount none) then
    IO.println s!"  ✓ makeCredential authData = header ‖ attestedCredData ({authDataMC.size} B)"
  else
    IO.println "  ✗ makeCredential authData header mismatch"; ok := false

  -- ---- 2. DER round-trip ----
  -- Sign the makeCredential attestation message = authDataMC ‖ clientDataHash.
  let msgMC := authDataMC ++ clientDataHash
  let zMC := P256ECDSA.digestToNat (sha256Bytes msgMC)
  match P256ECDSA.sign d k zMC with
  | none => IO.println "  ✗ P256 sign returned none"; ok := false
  | some (r, s) =>
    let der := DerSig.encodeDerSig r s
    match P256ECDSA.parseDerSignature der with
    | some (r', s') =>
      if r' == r && s' == s then
        IO.println s!"  ✓ DER sig round-trips (len {der.size})"
      else
        IO.println s!"  ✗ DER round-trip mismatch"; ok := false
    | none => IO.println "  ✗ parseDerSignature failed"; ok := false

    -- ---- 3. END-TO-END verify ----
    let q := P256ECDSA.derivePublicKey d
    if P256ECDSA.verify q zMC r s then
      IO.println "  ✓ end-to-end: verify(Q, H(authData‖clientDataHash), r, s) = true"
    else
      IO.println "  ✗ end-to-end verify FAILED"; ok := false

    -- ---- responses assemble (smoke) ----
    let mcResp := makeCredentialResponse authDataMC der
    -- getAssertion over its own 37-byte authData.
    let zGA := P256ECDSA.digestToNat (sha256Bytes (authDataGA ++ clientDataHash))
    match P256ECDSA.sign d k zGA with
    | some (rg, sg) =>
      let gaResp := getAssertionResponse credId authDataGA (DerSig.encodeDerSig rg sg)
      IO.println s!"  ✓ responses built: makeCred {mcResp.size}B, getAssertion {gaResp.size}B"
      -- getAssertion end-to-end
      if P256ECDSA.verify q zGA rg sg then
        IO.println "  ✓ end-to-end getAssertion verify = true"
      else
        IO.println "  ✗ getAssertion verify FAILED"; ok := false
    | none => IO.println "  ✗ getAssertion sign none"; ok := false

  -- ---- 4. COSE key + CBOR canonical shape ----
  -- COSE map first byte = 0xA5 (map, 5 entries).
  let cose := coseKeyP256 qx qy
  if cose[0]! == 0xA5 then
    IO.println "  ✓ COSE_Key is a 5-entry CBOR map (0xA5)"
  else
    IO.println s!"  ✗ COSE_Key first byte = {hex #[cose[0]!]} (expect a5)"; ok := false
  -- canonical key order: uint keys (1,3) sort before negInt keys (-1,-2,-3);
  -- CBOR.mapPairs must have re-sorted them.  A tiny direct check:
  let m := CBOR.mapPairs [(CBOR.uint 3, CBOR.uint 0), (CBOR.uint 1, CBOR.uint 0)]
  -- expect: a2 (map2) 01 00 03 00  — key 1 before key 3.
  if m == #[0xA2, 0x01, 0x00, 0x03, 0x00] then
    IO.println "  ✓ CBOR map keys sorted canonically (1 before 3)"
  else
    IO.println s!"  ✗ CBOR key sort wrong: {hex m}"; ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.CTAP2DataTest
