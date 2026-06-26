/-
  End-to-end client ↔ server TLS 1.3 handshake test.

  Pipe the messages produced by IP.TLS.Server through
  IP.TLS.Client (and vice versa) on the same machine — both
  must arrive at `connected` with matching application
  traffic secrets.

  This exercises:
    * server: parse ClientHello → emit SH + flight (EE/Cert/CV/Fin)
    * client: receive each, verify CV with real Ed25519 sig
    * both derive identical Handshake/Application secrets
    * client emits its Finished
    * server verifies and reaches connected
-/

import IP.TLS.Client
import IP.TLS.Server
import IP.TLS.Handshake
import IP.TLS.KeySchedule
import IP.Crypto.Ed25519Sign
import IP.Crypto.HKDF
import IP.Crypto.X25519

open Sparkle.IP.TLS.Client
open Sparkle.IP.TLS.Server
open Sparkle.IP.TLS.Handshake
open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.Crypto.HKDF (sha256)
open Sparkle.IP.Crypto.Ed25519Sign (sign derivePublicKey)

namespace Sparkle.Tests.IP.TLS.ClientServerTest

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

/-- Split a concatenation of Handshake-framed messages into
    individual messages.  Each message starts with a tag byte
    followed by u24 length. -/
private partial def splitFlight (bytes : Array UInt8) : List (Array UInt8) := Id.run do
  let mut acc : List (Array UInt8) := []
  let mut rest := bytes
  while rest.size ≥ 4 do
    let len :=
      (rest[1]!.toNat <<< 16) |||
      (rest[2]!.toNat <<<  8) |||
       rest[3]!.toNat
    let msgLen := 4 + len
    if rest.size < msgLen then break
    let mut msg : Array UInt8 := Array.replicate msgLen 0
    for i in [:msgLen] do
      msg := msg.set! i rest[i]!
    let mut newRest : Array UInt8 := Array.replicate (rest.size - msgLen) 0
    for i in [:newRest.size] do
      newRest := newRest.set! i rest[msgLen + i]!
    acc := msg :: acc
    rest := newRest
  return acc.reverse

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
  IO.println "=== TLS 1.3 client ↔ server end-to-end ==="

  -- ──────────────────────────────────────────────────────────────────
  -- Keypair setup.
  -- ──────────────────────────────────────────────────────────────────
  let clientEcdhPriv := bytesOfHex "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"
  let clientEcdhPub  := bytesOfHex "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
  let serverEcdhPriv := bytesOfHex "b1580eeadf6dd589b8ef4f2d5652578cc810e9980191ec8d058308cea216a21e"
  let serverEcdhPub  := bytesOfHex "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"

  let serverSigPriv := bytesOfHex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let serverSigPub := derivePublicKey serverSigPriv

  -- ──────────────────────────────────────────────────────────────────
  -- Client side: build CH.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "  C: building ClientHello"
  let chMsg := buildClientHello (Array.replicate 32 0) #[] clientEcdhPub
  let cs0 := Sparkle.IP.TLS.Client.initState clientEcdhPriv clientEcdhPub
  let cs1 := afterSendClientHello cs0 chMsg
  IO.println s!"     CH size = {chMsg.size}"

  -- ──────────────────────────────────────────────────────────────────
  -- Server side: process CH, emit SH + flight.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "  S: processing ClientHello (~60s Ed25519 sign)"
  let ss0 := Sparkle.IP.TLS.Server.initState serverEcdhPriv serverEcdhPub
  let serverRandom : Array UInt8 := Array.replicate 32 0
  -- Minimal Certificate body: TLS 1.3 has format
  --   opaque certificate_request_context<0..255> = "" (1 byte 0x00)
  --   CertificateEntry list<0..2^24-1>           = empty (3 bytes 0x000000)
  -- For our FSM-only test we present an EMPTY cert list and have
  -- the client side pre-stamp the pubkey via onCertificate (manual).
  let certBody : Array UInt8 := #[0x00, 0x00, 0x00, 0x00]
  -- signCv callback: caller-provided Ed25519 sign + sigScheme wrap.
  let signCv : Array UInt8 → Array UInt8 := fun signedContent =>
    let sig := sign serverSigPriv signedContent
    -- CV body = sigScheme(2) || vec16 sig
    #[0x08, 0x07] ++ be16 64 ++ sig
  let (ss1, flight?) := processClientHello ss0 chMsg serverRandom certBody signCv

  match flight? with
  | none =>
    IO.println s!"  ✗ server failed: {repr ss1.phase}"
    IO.Process.exit 1
  | some f =>
    IO.println s!"     SH size = {f.serverHello.size}"
    IO.println s!"     flight size = {f.flight.size}"
    IO.println s!"     S phase = {repr ss1.phase}"

    -- ────────────────────────────────────────────────────────────────
    -- Client side: receive SH, EE, Cert, CV, server Fin.
    -- ────────────────────────────────────────────────────────────────
    IO.println "  C: receiving ServerHello"
    let cs2 := onServerHello cs1 f.serverHello
    if !(cs2.phase == Sparkle.IP.TLS.Client.Phase.waitEe) then
      IO.println s!"  ✗ client SH failed: {repr cs2.phase}"
      IO.Process.exit 1

    -- The handshake_secret on both sides must agree at this point.
    match cs2.handshakeSecrets, ss1.handshakeSecrets with
    | some chs, some shs =>
      if chs.handshakeSecret = shs.handshakeSecret then
        IO.println "  ✓ client & server handshake_secret agree"
      else
        IO.println s!"  ✗ handshake_secret mismatch"
        IO.println s!"    client = {hexOfBytes chs.handshakeSecret}"
        IO.println s!"    server = {hexOfBytes shs.handshakeSecret}"
        IO.Process.exit 1
    | _, _ =>
      IO.println "  ✗ handshake secrets missing on one side"
      IO.Process.exit 1

    -- Walk the server's flight as a sequence of handshake messages.
    let msgs := splitFlight f.flight
    IO.println s!"  C: flight contains {msgs.length} messages"
    if msgs.length ≠ 4 then
      IO.println "  ✗ expected EE + Cert + CV + Fin"
      IO.Process.exit 1

    let msgsArr := msgs.toArray
    let eeMsg := msgsArr[0]!
    let certMsg := msgsArr[1]!
    let cvMsg := msgsArr[2]!
    let finMsg := msgsArr[3]!

    let cs3 := onEncryptedExtensions cs2 eeMsg
    -- Use manual pubkey-stamping rather than X.509-parsing.
    let cs4 := onCertificate cs3 certMsg serverSigPub
    IO.println "  C: verifying CertificateVerify (~90s Ed25519 verify)"
    let cs5 := onCertificateVerify cs4 cvMsg
    if !(cs5.phase == Sparkle.IP.TLS.Client.Phase.waitFinished) then
      IO.println s!"  ✗ client CV failed: {repr cs5.phase}"
      IO.Process.exit 1
    IO.println "  ✓ client verified server CV"
    let cs6 := onServerFinished cs5 finMsg
    if !(cs6.phase == Sparkle.IP.TLS.Client.Phase.connected) then
      IO.println s!"  ✗ client SFin failed: {repr cs6.phase}"
      IO.Process.exit 1
    IO.println "  ✓ client reached connected"

    -- ────────────────────────────────────────────────────────────────
    -- Client emits its Finished.  Server consumes it.
    -- ────────────────────────────────────────────────────────────────
    let clientFin := buildClientFinished cs6
    IO.println s!"  C → S: Finished ({clientFin.size} bytes)"
    let ss2 := onClientFinished ss1 clientFin
    if !(ss2.phase == Sparkle.IP.TLS.Server.Phase.connected) then
      IO.println s!"  ✗ server CFin failed: {repr ss2.phase}"
      IO.Process.exit 1
    IO.println "  ✓ server reached connected"

    -- Cross-check application traffic secrets agree.
    match cs6.applicationSecrets, ss2.applicationSecrets with
    | some cApp, some sApp =>
      if cApp.cApTrafficSecret = sApp.cApTrafficSecret ∧
         cApp.sApTrafficSecret = sApp.sApTrafficSecret then
        IO.println "  ✓ client & server application traffic secrets agree"
      else
        IO.println "  ✗ application traffic secret mismatch"
        IO.Process.exit 1
    | _, _ =>
      IO.println "  ✗ application secrets missing"
      IO.Process.exit 1

    IO.println "\nALL PASS"

end Sparkle.Tests.IP.TLS.ClientServerTest
