/-
  End-to-end HTTPS over Sparkle TLS demo.

  Sequence:
    1. Client builds + sends ClientHello.
    2. Server processes CH, builds ServerHello + flight
       (EE/Cert/CV/Fin).
    3. Client receives SH, then walks the flight (EE, Cert, CV
       with real Ed25519 verify, server Fin).
    4. Client emits Finished.  Server consumes it.
    5. Both sides have matching application traffic secrets.
    6. Client encrypts an HTTP GET request as a TLS
       application_data record.  Server decrypts, processes,
       encrypts a 200 OK response.  Client decrypts.
    7. The decrypted plaintext on each side must be
       byte-exact equal to the original.

  This is the same crypto and FSM machinery that handles a
  real TLS 1.3 session — only the network transport (TCP
  segmentation, retry, etc.) is elided.  The HFT/TLS test
  exercises the same record-layer encrypt/decrypt; this
  test puts a full handshake in front of it.
-/
import IP.TLS.Client
import IP.TLS.Server
import IP.TLS.Handshake
import IP.TLS.KeySchedule
import IP.Net.HFTOverTLS
import IP.Crypto.Proof.Ed25519Sign
import IP.Crypto.Codec.HKDF
import IP.Crypto.Proof.X25519

open Sparkle.IP.TLS.Client
open Sparkle.IP.TLS.Server
open Sparkle.IP.TLS.Handshake
open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.Net.HFTOverTLS
open Sparkle.IP.Crypto.HKDF (sha256)
open Sparkle.IP.Crypto.Ed25519Sign (sign derivePublicKey)

namespace Sparkle.Tests.IP.Net.HTTPSDemoTest

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

/-- Split a concatenation of Handshake-framed messages. -/
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

def main : IO Unit := do
  IO.println "=== HTTPS over Sparkle TLS — end-to-end demo ==="

  -- Per-session keys (would be RNG in production).
  let clientEcdhPriv := bytesOfHex "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"
  let clientEcdhPub  := bytesOfHex "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
  let serverEcdhPriv := bytesOfHex "b1580eeadf6dd589b8ef4f2d5652578cc810e9980191ec8d058308cea216a21e"
  let serverEcdhPub  := bytesOfHex "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"
  let serverSigPriv := bytesOfHex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let serverSigPub := derivePublicKey serverSigPriv

  -- ──────────────────────────────────────────────────────────────────
  -- Phase A: TLS 1.3 1-RTT handshake.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n[A] TLS 1.3 handshake"
  let chMsg := buildClientHello (Array.replicate 32 0) #[] clientEcdhPub
  let cs0 := Sparkle.IP.TLS.Client.initState clientEcdhPriv clientEcdhPub
  let cs1 := afterSendClientHello cs0 chMsg

  let ss0 := Sparkle.IP.TLS.Server.initState serverEcdhPriv serverEcdhPub
  let serverRandom : Array UInt8 := Array.replicate 32 0
  let certBody : Array UInt8 := #[0x00, 0x00, 0x00, 0x00]
  let signCv := fun (signedContent : Array UInt8) =>
    let sig := sign serverSigPriv signedContent
    #[0x08, 0x07] ++ be16 64 ++ sig
  IO.println "  S: signing CertificateVerify (~60s)..."
  let (ss1, flight?) := processClientHello ss0 chMsg serverRandom certBody signCv

  let f := flight?.getD { serverHello := #[], flight := #[] }
  if f.serverHello.size = 0 then
    IO.println s!"  ✗ server processCH failed: {repr ss1.phase}"
    IO.Process.exit 1

  let cs2 := onServerHello cs1 f.serverHello
  let msgsArr := (splitFlight f.flight).toArray
  if msgsArr.size ≠ 4 then
    IO.println "  ✗ flight not 4 messages"
    IO.Process.exit 1
  let cs3 := onEncryptedExtensions cs2 msgsArr[0]!
  let cs4 := onCertificate cs3 msgsArr[1]! serverSigPub
  IO.println "  C: verifying CertificateVerify (~90s)..."
  let cs5 := onCertificateVerify cs4 msgsArr[2]!
  let cs6 := onServerFinished cs5 msgsArr[3]!
  if !(cs6.phase == Sparkle.IP.TLS.Client.Phase.connected) then
    IO.println s!"  ✗ client handshake failed: {repr cs6.phase}"
    IO.Process.exit 1

  let clientFin := buildClientFinished cs6
  let ss2 := onClientFinished ss1 clientFin
  if !(ss2.phase == Sparkle.IP.TLS.Server.Phase.connected) then
    IO.println s!"  ✗ server handshake failed: {repr ss2.phase}"
    IO.Process.exit 1
  IO.println "  ✓ handshake completed on both sides"

  let cApp := cs6.applicationSecrets.getD ⟨#[], #[], #[], #[]⟩
  let sApp := ss2.applicationSecrets.getD ⟨#[], #[], #[], #[]⟩
  if cApp.cApTrafficSecret ≠ sApp.cApTrafficSecret ∨
     cApp.sApTrafficSecret ≠ sApp.sApTrafficSecret then
    IO.println "  ✗ application traffic secrets do not match"
    IO.Process.exit 1
  IO.println "  ✓ application traffic secrets agree"

  -- ──────────────────────────────────────────────────────────────────
  -- Phase B: HTTPS request/response over the established session.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n[B] HTTPS application data"

  -- Client → Server: HTTP GET as one TLS record.
  let reqStr := "GET /index.html HTTP/1.0\r\nHost: sparkle.example.com\r\nUser-Agent: sparkle/0.1\r\n\r\n"
  let httpReq : Array UInt8 := reqStr.toUTF8.toList.toArray
  let reqRecord := encryptRequest cApp.cApTrafficSecret 0 httpReq
  IO.println s!"  C → S: encrypted request ({reqRecord.size} bytes, plaintext was {httpReq.size})"

  -- Server decrypts.
  match decryptRequest sApp.cApTrafficSecret 0 reqRecord with
  | none =>
    IO.println "  ✗ server decrypt failed"
    IO.Process.exit 1
  | some (ct, plaintext) =>
    if plaintext ≠ httpReq then
      IO.println "  ✗ server got different bytes"
      IO.Process.exit 1
    if !(ct == Sparkle.IP.TLS.Record.ContentType.applicationData) then
      IO.println "  ✗ wrong record content type"
      IO.Process.exit 1
    IO.println s!"  ✓ server decrypted to: {String.mk (plaintext.toList.map (Char.ofNat ·.toNat)) |>.trim}"

  -- Server → Client: HTTP/1.0 200 OK response.
  let respStr :=
    "HTTP/1.0 200 OK\r\n" ++
    "Content-Type: text/html; charset=utf-8\r\n" ++
    "Content-Length: 47\r\n\r\n" ++
    "<html><body><h1>Hello from Sparkle TLS</h1></body></html>"
  let httpResp : Array UInt8 := respStr.toUTF8.toList.toArray
  let respRecord := encryptResponse sApp.sApTrafficSecret 0 httpResp
  IO.println s!"  S → C: encrypted response ({respRecord.size} bytes, plaintext was {httpResp.size})"

  -- Client decrypts.
  match decryptResponse cApp.sApTrafficSecret 0 respRecord with
  | none =>
    IO.println "  ✗ client decrypt failed"
    IO.Process.exit 1
  | some (_, plaintext) =>
    if plaintext ≠ httpResp then
      IO.println "  ✗ client got different bytes"
      IO.Process.exit 1
    let respStr := String.mk (plaintext.toList.map (Char.ofNat ·.toNat))
    IO.println "  ✓ client decrypted response:"
    -- Indent each line.
    for line in respStr.splitOn "\r\n" do
      IO.println s!"    | {line}"

  -- Tamper test on application_data path.
  IO.println "\n[C] Tamper test (post-handshake AEAD integrity)"
  let badReq := reqRecord.set! 10 (reqRecord[10]! ^^^ 1)
  match decryptRequest sApp.cApTrafficSecret 0 badReq with
  | none => IO.println "  ✓ bit-flipped record rejected"
  | some _ =>
    IO.println "  ✗ tampered record accepted (bug)"
    IO.Process.exit 1

  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Net.HTTPSDemoTest
