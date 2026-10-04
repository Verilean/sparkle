/-
  Sim test for IP.TLS.X509Verify.validateChain.

  Uses an OpenSSL-generated 2-cert chain:
    * `ca-cert.der`   — self-signed Ed25519 CA
    * `leaf-cert.der` — Ed25519 leaf, signed by the CA

  We:
    1. Parse both certs and confirm `leaf.issuer = ca.subject`.
    2. Validate the chain with the CA's pubkey in the trust set.
    3. Try the inverse trust set (empty) and confirm rejection.
    4. Try a tampered leaf cert and confirm rejection.

  Verification time: each Ed25519 verify ≈ 90s on this
  Nat-backed implementation, so this test takes ~3 minutes
  (leaf-by-CA + CA-by-itself + a tamper retry).
-/

import IP.TLS.X509Verify

open Sparkle.IP.TLS.X509
open Sparkle.IP.TLS.X509Verify

namespace Sparkle.Tests.IP.TLS.X509VerifyTest

private def readDer (relPath : String) : IO (Array UInt8) := do
  let path : System.FilePath :=
    System.FilePath.mk ("Tests/IP/TLS/" ++ relPath)
  let bytes ← IO.FS.readBinFile path
  let mut out : Array UInt8 := Array.replicate bytes.size 0
  for i in [:bytes.size] do
    out := out.set! i bytes[i]!
  return out

def main : IO Unit := do
  IO.println "=== X.509 cert-chain validation sim ==="

  let mut ok := true

  -- Load both certs.
  let caRaw ← readDer "ca-cert.der"
  let leafRaw ← readDer "leaf-cert.der"

  -- Parse.
  let caLink? := mkLink caRaw
  let leafLink? := mkLink leafRaw
  match caLink?, leafLink? with
  | none, _ =>
    IO.println "  ✗ CA parse failed"; ok := false
  | _, none =>
    IO.println "  ✗ leaf parse failed"; ok := false
  | some ca, some leaf =>
    IO.println s!"  CA   subject DN size  = {ca.cert.subjectDer.size}"
    IO.println s!"  leaf issuer DN size   = {leaf.cert.issuerDer.size}"
    if ca.cert.subjectDer = leaf.cert.issuerDer then
      IO.println "  ✓ leaf.issuer = CA.subject"
    else
      IO.println "  ✗ DN mismatch"
      ok := false

    -- Trust set with the real CA pubkey: should succeed.
    IO.println s!"\n  validating chain (~3 min, three Ed25519 verifies)..."
    let trust : TrustSet := [ca.cert.spki.rawKey]
    if validateChain [leaf, ca] trust then
      IO.println "  ✓ chain validates with CA in trust set"
    else
      IO.println "  ✗ chain validation rejected a valid chain"
      ok := false

    -- Empty trust set: should fail (CA pubkey not trusted).
    IO.println s!"\n  testing empty trust set..."
    if validateChain [leaf, ca] [] then
      IO.println "  ✗ chain accepted with empty trust set (bug)"
      ok := false
    else
      IO.println "  ✓ empty trust set rejects chain"

    -- Tampered leaf cert: flip a byte inside the TBS section.
    IO.println s!"\n  testing tampered leaf (one byte flip)..."
    let tamperOff := leaf.cert.tbsBegin + 10
    let mut leafTampered := leafRaw
    leafTampered := leafTampered.set! tamperOff (leafRaw[tamperOff]! ^^^ 1)
    match mkLink leafTampered with
    | none =>
      -- Tampering broke DER structure — also acceptable, just
      -- note it.
      IO.println "  ✓ tampered leaf failed even to parse (acceptable)"
    | some leafBad =>
      if validateChain [leafBad, ca] trust then
        IO.println "  ✗ tampered leaf accepted (bug)"
        ok := false
      else
        IO.println "  ✓ tampered leaf rejected"

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.TLS.X509VerifyTest
