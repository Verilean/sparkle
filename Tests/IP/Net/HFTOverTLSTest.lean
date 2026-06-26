/-
  Sim test for IP.Net.HFTOverTLS — end-to-end HFT request
  over a TLS 1.3 1-RTT session.

  Flow:
    1. Run a full TLS 1.3 handshake through the client FSM
       against a stub server, sharing X25519 + Ed25519 sig.
    2. Both sides arrive at the same
       client_application_traffic_secret_0 +
       server_application_traffic_secret_0.
    3. Client encrypts an HFT request ("GET /tick ...") as a
       TLS application_data record on its sending channel.
    4. Server mirror decrypts using the matching secret +
       sequence number, gets the original bytes back.
    5. Server encrypts an HFT response, client decrypts.
    6. Tampering tests: flip a bit in the record, decrypt
       must fail.

  This shows the same end-to-end pipeline the HFT NIC's
  TCP path would carry on top of TLS, just at the
  pure-data level — the Sparkle HW wrapper is a future
  T.6.HW task.
-/

import IP.Net.HFTOverTLS
import IP.TLS.Client
import IP.TLS.Handshake
import IP.TLS.KeySchedule
import IP.Crypto.HKDF
import IP.Crypto.X25519
import IP.Crypto.Ed25519Sign

open Sparkle.IP.Net.HFTOverTLS
open Sparkle.IP.TLS.Client
open Sparkle.IP.TLS.Handshake
open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.Crypto.HKDF (sha256)
open Sparkle.IP.Crypto.Ed25519Sign (sign derivePublicKey)

namespace Sparkle.Tests.IP.Net.HFTOverTLSTest

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

/-- Drive the full client handshake against a stub server,
    returning the final state (with both application
    secrets). -/
private def runHandshake : Option State := Id.run do
  -- Both sides use known X25519 keypairs (from RFC 8448 §3
  -- for repro, but values are arbitrary for this test).
  let clientPriv := bytesOfHex "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"
  let clientPub  := bytesOfHex "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
  let serverPub  := bytesOfHex "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"
  -- 1. Client builds CH.
  let chMsg := buildClientHello (Array.replicate 32 0) #[] clientPub
  let s0 := initState clientPriv clientPub
  let s1 := afterSendClientHello s0 chMsg
  -- 2. Stub server emits SH carrying serverPub in key_share.
  let kse : Array UInt8 := #[0x00, 0x1D] ++ be16 32 ++ serverPub
  let extKS : Array UInt8 := be16 51 ++ be16 kse.size ++ kse
  let shBody : Array UInt8 :=
    #[0x03, 0x03]
    ++ Array.replicate 32 0
    ++ #[0]
    ++ #[0x13, 0x01]
    ++ #[0x00]
    ++ be16 extKS.size
    ++ extKS
  let shMsg := wrapHandshake HandshakeType.serverHello shBody
  let s2 := onServerHello s1 shMsg
  if !(s2.phase == Phase.waitEe) then return none
  -- 3. EE, Certificate, CV (real Ed25519 signature).
  let eeMsg := wrapHandshake HandshakeType.encryptedExtensions (be16 0)
  let s3 := onEncryptedExtensions s2 eeMsg
  let serverEdPriv := bytesOfHex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let serverEdPub := derivePublicKey serverEdPriv
  let certMsg := wrapHandshake HandshakeType.certificate (Array.replicate 8 0)
  let s4 := onCertificate s3 certMsg serverEdPub
  let thBeforeCv := sha256 s4.transcript
  let pad : Array UInt8 := Array.replicate 64 0x20
  let ctxLabel : Array UInt8 := "TLS 1.3, server CertificateVerify".toUTF8.toList.toArray
  let signedContent : Array UInt8 := pad ++ ctxLabel ++ #[0x00] ++ thBeforeCv
  let realSig := sign serverEdPriv signedContent
  let cvBody : Array UInt8 := #[0x08, 0x07] ++ be16 64 ++ realSig
  let cvMsg := wrapHandshake HandshakeType.certificateVerify cvBody
  let s5 := onCertificateVerify s4 cvMsg
  if !(s5.phase == Phase.waitFinished) then return none
  -- 4. Server Finished — server side computes the same value, sends it back.
  match s5.handshakeSecrets with
  | none => return none
  | some hs =>
    let thBeforeServerFin := sha256 s5.transcript
    let serverVerifyData := finishedVerifyData hs.sHsTrafficSecret thBeforeServerFin
    let finMsg := wrapHandshake HandshakeType.finished serverVerifyData
    let s6 := onServerFinished s5 finMsg
    return some s6

def main : IO Unit := do
  IO.println "=== HFT-over-TLS 1.3 end-to-end sim ==="

  let mut ok := true

  match runHandshake with
  | none =>
    IO.println "  ✗ TLS handshake failed"
    ok := false
  | some s =>
    if !(s.phase == Phase.connected) then
      IO.println s!"  ✗ TLS handshake didn't reach connected: {repr s.phase}"
      ok := false
    else
      IO.println "  ✓ TLS handshake reached connected"
      match s.applicationSecrets with
      | none =>
        IO.println "  ✗ no application secrets"
        ok := false
      | some app =>
        let cAp := app.cApTrafficSecret
        let sAp := app.sApTrafficSecret
        IO.println s!"  ✓ c_ap secret: {hexOfBytes cAp}"
        IO.println s!"  ✓ s_ap secret: {hexOfBytes sAp}"

        -- Round-trip: HFT request over TLS.
        let req := "GET /tick HTTP/1.0\r\nHost: hft.example.com\r\n\r\n".toUTF8.toList.toArray
        let record := encryptRequest cAp 0 req
        IO.println s!"  ✓ encrypted request: {record.size} bytes (plaintext {req.size} bytes)"

        match decryptRequest cAp 0 record with
        | none =>
          IO.println "  ✗ server-side decrypt failed"
          ok := false
        | some (ct, plaintext) =>
          if plaintext = req then
            IO.println "  ✓ server got back identical HFT request bytes"
          else
            IO.println "  ✗ decrypted plaintext mismatch"
            ok := false
          IO.println s!"    ContentType: {repr ct}"

        -- Round-trip: server responds.
        let resp := "HTTP/1.0 200 OK\r\nContent-Length: 3\r\n\r\n42\n".toUTF8.toList.toArray
        let record2 := encryptResponse sAp 0 resp
        match decryptResponse sAp 0 record2 with
        | none =>
          IO.println "  ✗ client-side decrypt failed"
          ok := false
        | some (_, p) =>
          if p = resp then
            IO.println "  ✓ client got back identical HFT response bytes"
          else
            IO.println "  ✗ response decrypted plaintext mismatch"
            ok := false

        -- Tamper test: flip a byte, decrypt must fail.
        let badRecord := record.set! 10 (record[10]! ^^^ 1)
        match decryptRequest cAp 0 badRecord with
        | none =>
          IO.println "  ✓ tampered record rejected"
        | some _ =>
          IO.println "  ✗ tampered record was accepted (bug)"
          ok := false

        -- Sequence-number test: same record with wrong seq must fail.
        match decryptRequest cAp 1 record with
        | none =>
          IO.println "  ✓ replay with wrong seq rejected"
        | some _ =>
          IO.println "  ✗ wrong-seq record was accepted (bug)"
          ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.HFTOverTLSTest
