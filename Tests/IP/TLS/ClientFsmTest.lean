/-
  Sim test for IP.TLS.Client — verify the state machine
  transitions, message framing, and that the key schedule
  is driven correctly off the running transcript.

  The cryptographic ground truth lives in
  `Tests/IP/TLS/KeyScheduleTest.lean`, which feeds RFC 8448
  §3 hash values directly into the schedule.  This file
  drives the FSM with synthetic-but-consistent wire messages
  to confirm:
    * each transition lands in the expected `Phase`
    * the transcript accumulates correctly
    * the DHE secret is correctly computed via X25519
    * derived secrets match those produced by independently
      invoking the schedule on the same transcript hash
-/

import IP.TLS.Client
import IP.TLS.KeySchedule
import IP.TLS.Handshake
import IP.Crypto.HKDF
import IP.Crypto.X25519
import IP.Crypto.Ed25519Sign

open Sparkle.IP.TLS.Client
open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.TLS.Handshake
open Sparkle.IP.Crypto.HKDF (sha256)
open Sparkle.IP.Crypto.Ed25519Sign (sign derivePublicKey)

namespace Sparkle.Tests.IP.TLS.ClientFsmTest

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
  IO.println "=== TLS 1.3 client FSM transitions ==="

  let mut ok := true

  -- Use RFC 8448 §3 client + server X25519 keypairs (so DHE check
  -- can be against the published expected secret).
  let clientPriv := bytesOfHex "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"
  let clientPub  := bytesOfHex "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
  let serverPub  := bytesOfHex "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"
  let dheExp := "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"

  -- Build a syntactically valid ClientHello with our client pubkey.
  let randomZeros : Array UInt8 := Array.replicate 32 0
  let chMsg := buildClientHello randomZeros #[] clientPub

  -- Build a syntactically valid ServerHello with the server pubkey.
  let shBody : Array UInt8 :=
    #[0x03, 0x03]                              -- legacy_version
    ++ Array.replicate 32 0                   -- random
    ++ #[0]                                   -- empty session_id_echo
    ++ #[0x13, 0x01]                          -- cipher_suite = TLS_AES_128_GCM_SHA256
    ++ #[0x00]                                -- compression
    ++ (be16 6 ++ #[0x00, 0x33] ++ be16 2 ++ #[0x00, 0x1D])  -- broken; rebuild below
  -- Actually rebuild extensions cleanly: extension key_share (51) with x25519 entry.
  let kse : Array UInt8 := #[0x00, 0x1D] ++ be16 32 ++ serverPub
  let ksData : Array UInt8 := kse
  let extKS : Array UInt8 := be16 51 ++ be16 ksData.size ++ ksData
  let shBody2 : Array UInt8 :=
    #[0x03, 0x03]                              -- legacy_version
    ++ Array.replicate 32 0                   -- random
    ++ #[0]                                   -- empty session_id_echo
    ++ #[0x13, 0x01]                          -- cipher_suite
    ++ #[0x00]                                -- compression
    ++ be16 extKS.size                        -- extensions length
    ++ extKS                                  -- extensions
  let _ := shBody  -- discard the broken first attempt
  let shMsg := wrapHandshake HandshakeType.serverHello shBody2

  -- ──────────────────────────────────────────────────────────────────
  -- Phase 1: ClientHello sent
  -- ──────────────────────────────────────────────────────────────────
  let s0 := initState clientPriv clientPub
  let s1 := afterSendClientHello s0 chMsg
  IO.println s!"  CH wire size = {chMsg.size} bytes"
  if !(s1.phase == Phase.waitSh) then
    IO.println s!"  ✗ expected waitSh, got {repr s1.phase}"
    ok := false
  else
    IO.println s!"  ✓ phase: waitSh"

  -- ──────────────────────────────────────────────────────────────────
  -- Phase 2: ServerHello → expect waitEe + correct DHE
  -- ──────────────────────────────────────────────────────────────────
  let s2 := onServerHello s1 shMsg
  match s2.phase with
  | Phase.failed msg =>
    IO.println s!"  ✗ onServerHello failed: {msg}"
    ok := false
  | Phase.waitEe =>
    IO.println s!"  ✓ phase: waitEe"
    let gotDhe := hexOfBytes s2.dheSecret
    if gotDhe = dheExp then
      IO.println s!"  ✓ DHE shared secret = RFC 8448 §3 value"
    else
      IO.println s!"  ✗ DHE mismatch"
      IO.println s!"    expected: {dheExp}"
      IO.println s!"    got     : {gotDhe}"
      ok := false
    -- Cross-check: independently call the key schedule on the
    -- transcript and confirm the FSM derived the same secrets.
    let thChSh := sha256 s2.transcript
    let es := earlySecret #[]
    let hsExpected := deriveHandshakeStage es s2.dheSecret thChSh
    match s2.handshakeSecrets with
    | none =>
      IO.println "  ✗ handshakeSecrets missing"
      ok := false
    | some hs =>
      if hs.handshakeSecret = hsExpected.handshakeSecret ∧
         hs.cHsTrafficSecret = hsExpected.cHsTrafficSecret ∧
         hs.sHsTrafficSecret = hsExpected.sHsTrafficSecret then
        IO.println "  ✓ FSM-derived handshake secrets match independent schedule"
      else
        IO.println "  ✗ FSM-derived secrets diverge from independent schedule"
        ok := false
  | _ =>
    IO.println s!"  ✗ unexpected phase after onServerHello: {repr s2.phase}"
    ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Phase 3: EncryptedExtensions (minimal body)
  -- ──────────────────────────────────────────────────────────────────
  let eeMsg := wrapHandshake HandshakeType.encryptedExtensions (be16 0)
  let s3 := onEncryptedExtensions s2 eeMsg
  if s3.phase == Phase.waitCertOrCv then
    IO.println "  ✓ phase: waitCertOrCv"
  else
    IO.println s!"  ✗ EE: expected waitCertOrCv, got {repr s3.phase}"
    ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Phase 4: Certificate — use a real Ed25519 server keypair so the
  -- subsequent CertificateVerify can be signed for real.
  -- ──────────────────────────────────────────────────────────────────
  let serverEdPriv := bytesOfHex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let serverEdPub := derivePublicKey serverEdPriv
  let certMsg := wrapHandshake HandshakeType.certificate (Array.replicate 8 0)
  let s4 := onCertificate s3 certMsg serverEdPub
  if s4.phase == Phase.waitCv then
    IO.println "  ✓ phase: waitCv (server pubkey stamped)"
  else
    IO.println s!"  ✗ Cert: expected waitCv, got {repr s4.phase}"
    ok := false
  if s4.serverPubkey = serverEdPub then
    IO.println "  ✓ serverPubkey set from Cert payload"
  else
    ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Phase 5: CertificateVerify — server signs the transcript with
  -- Ed25519, client verifies.  Per RFC 8446 §4.4.3:
  --   signed = (0x20 × 64) || "TLS 1.3, server CertificateVerify"
  --          || 0x00 || Transcript-Hash(messages so far)
  -- ──────────────────────────────────────────────────────────────────
  IO.println "  (signing CV — ~60s)..."
  let thBeforeCv := sha256 s4.transcript
  let pad : Array UInt8 := Array.replicate 64 0x20
  let ctxLabel : Array UInt8 := "TLS 1.3, server CertificateVerify".toUTF8.toList.toArray
  let signedContent : Array UInt8 := pad ++ ctxLabel ++ #[0x00] ++ thBeforeCv
  let realSig := sign serverEdPriv signedContent
  let cvBody : Array UInt8 := #[0x08, 0x07] ++ be16 64 ++ realSig
  let cvMsg := wrapHandshake HandshakeType.certificateVerify cvBody
  IO.println "  (verifying CV — ~90s)..."
  let s5 := onCertificateVerify s4 cvMsg
  if s5.phase == Phase.waitFinished then
    IO.println "  ✓ phase: waitFinished (Ed25519 sig verified)"
  else
    IO.println s!"  ✗ CV: expected waitFinished, got {repr s5.phase}"
    ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Phase 6: Server Finished — build verify_data using the
  -- handshake secret + current transcript hash, then feed it
  -- back into the FSM so it accepts.
  -- ──────────────────────────────────────────────────────────────────
  match s5.handshakeSecrets with
  | none =>
    IO.println "  ✗ no handshake secrets"
    ok := false
  | some hs =>
    let thBeforeServerFin := sha256 s5.transcript
    let serverVerifyData := finishedVerifyData hs.sHsTrafficSecret thBeforeServerFin
    let finMsg := buildFinished serverVerifyData
    let s6 := onServerFinished s5 finMsg
    match s6.phase with
    | Phase.connected =>
      IO.println "  ✓ phase: connected (server Finished verified)"
      -- Confirm we computed the client Finished verify_data.
      if s6.clientFinishedVerifyData.size = hashLen then
        IO.println "  ✓ client Finished verify_data produced (32 bytes)"
      else
        IO.println s!"  ✗ client Finished verify_data size = {s6.clientFinishedVerifyData.size}"
        ok := false
      -- Confirm application secrets are filled in.
      match s6.applicationSecrets with
      | none =>
        IO.println "  ✗ application secrets missing"
        ok := false
      | some app =>
        if app.cApTrafficSecret.size = hashLen ∧
           app.sApTrafficSecret.size = hashLen then
          IO.println "  ✓ application traffic secrets derived"
        else
          ok := false
    | Phase.failed m =>
      IO.println s!"  ✗ ServerFinished failed: {m}"
      ok := false
    | p =>
      IO.println s!"  ✗ unexpected phase: {repr p}"
      ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.TLS.ClientFsmTest
