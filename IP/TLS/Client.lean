/-
  IP.TLS.Client — TLS 1.3 client-side state machine
  (RFC 8446 §A.1).

  The client states for a basic 1-RTT handshake:

      START
        |  client sends ClientHello, computes x25519 keypair
        v
      WAIT_SH
        |  on ServerHello: compute (handshake keys, transcript hash after CH||SH)
        v
      WAIT_EE
        |  on EncryptedExtensions: append to transcript
        v
      WAIT_CERT_OR_CV
        |  on Certificate: append, expect CertificateVerify next
        |  (or on PreSharedKey path: skip to WAIT_FINISHED)
        v
      WAIT_CV
        |  on CertificateVerify: verify server signature
        v
      WAIT_FINISHED
        |  on Finished: verify server verify_data,
        |  compute application keys from transcript-after-server-Finished,
        |  build & send client Finished.
        v
      CONNECTED

  This file ships the pure state-transition functions; the
  Sparkle Signal HW wrapper is a future T.6.HW task.
-/

import IP.TLS.KeySchedule
import IP.TLS.Handshake
import IP.Crypto.HKDF
import IP.Crypto.X25519
import IP.Crypto.Ed25519Sign
import IP.Crypto.P256ECDSA
import IP.Crypto.RSAPSS
import IP.TLS.X509

namespace Sparkle.IP.TLS.Client

open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.TLS.Handshake (HandshakeType ServerHello parseServerHelloBody buildFinished wrapHandshake)
open Sparkle.IP.Crypto.HKDF (sha256 hmacSha256 hkdfExpandLabel)

/-! ### Client state. -/

inductive Phase where
  | start          : Phase
  | waitSh         : Phase
  | waitEe         : Phase
  | waitCertOrCv   : Phase
  | waitCv         : Phase
  | waitFinished   : Phase
  | connected      : Phase
  | failed (reason : String) : Phase
  deriving Repr, BEq, Inhabited

/-- Per-connection client state.

    Carries the live secrets, the running transcript bytes
    (so we can hash at any cut point), the client's X25519
    private key for KEX, and the server's verifying key once
    learned. -/
structure State where
  phase            : Phase
  /-- 32-byte X25519 client secret (clamped). -/
  ourEcdhSecret    : Array UInt8
  /-- 32-byte X25519 client public key (sent in ClientHello). -/
  ourEcdhPublic    : Array UInt8
  /-- Concatenation of handshake message bytes seen so far
      (used to compute the running transcript hash on demand). -/
  transcript       : Array UInt8
  /-- DHE shared secret (filled once we see ServerHello). -/
  dheSecret        : Array UInt8
  /-- Handshake-stage secrets (filled after ServerHello). -/
  handshakeSecrets : Option HandshakeSecrets
  /-- Application-stage secrets (filled after server Finished). -/
  applicationSecrets : Option ApplicationSecrets
  /-- Server's verifying key, learned from server's Certificate. -/
  serverPubkey     : Array UInt8
  /-- The client_finished verify_data we end up sending, kept for
      tests / downstream record encryption. -/
  clientFinishedVerifyData : Array UInt8
  deriving Repr

/-- Initial state: nothing computed yet. -/
def initState (ourEcdhSecret ourEcdhPublic : Array UInt8) : State :=
  { phase := .start
  , ourEcdhSecret := ourEcdhSecret
  , ourEcdhPublic := ourEcdhPublic
  , transcript := #[]
  , dheSecret := #[]
  , handshakeSecrets := none
  , applicationSecrets := none
  , serverPubkey := #[]
  , clientFinishedVerifyData := #[] }

/-! ### Transition functions.  Each takes the current state +
    the next message's bytes (the handshake-framed wire form,
    i.e. type || u24 length || body) and returns the new state.
    Failures land the state in `Phase.failed`. -/

/-- Run after we've built & sent ClientHello.  We pre-append
    the ClientHello bytes to the transcript here so subsequent
    transcript-hash calls include them. -/
def afterSendClientHello (s : State) (clientHelloMsg : Array UInt8) : State :=
  { s with transcript := s.transcript ++ clientHelloMsg
         , phase := .waitSh }

/-- Receive ServerHello.  `serverHelloMsg` is the full
    Handshake frame (type byte + u24 length + body).  Strips
    the frame, parses the body, computes the DHE shared
    secret and the handshake-stage secrets, transitions to
    `waitEe`. -/
def onServerHello (s : State) (serverHelloMsg : Array UInt8) : State := Id.run do
  if serverHelloMsg.size < 4 then
    return { s with phase := .failed "ServerHello: truncated frame" }
  if serverHelloMsg[0]! ≠ HandshakeType.serverHello.toByte then
    return { s with phase := .failed "ServerHello: wrong msg_type" }
  -- u24 length at bytes 1..3
  let bodyLen :=
    (serverHelloMsg[1]!.toNat <<< 16) |||
    (serverHelloMsg[2]!.toNat <<<  8) |||
     serverHelloMsg[3]!.toNat
  if serverHelloMsg.size ≠ 4 + bodyLen then
    return { s with phase := .failed "ServerHello: length mismatch" }
  let mut body : Array UInt8 := Array.replicate bodyLen 0
  for i in [:bodyLen] do
    body := body.set! i serverHelloMsg[4 + i]!
  match parseServerHelloBody body with
  | none => return { s with phase := .failed "ServerHello: parse failed" }
  | some sh =>
    -- Compute DHE shared secret.
    let dhe := Sparkle.IP.Crypto.X25519.x25519 s.ourEcdhSecret sh.serverPubkey
    -- Append SH to transcript, compute transcript hash, derive HS-stage.
    let transcript' := s.transcript ++ serverHelloMsg
    let chShHash := sha256 transcript'
    let es := earlySecret #[]
    let hs := deriveHandshakeStage es dhe chShHash
    return { s with phase := .waitEe
                  , transcript := transcript'
                  , dheSecret := dhe
                  , handshakeSecrets := some hs }

/-- Receive EncryptedExtensions.  No semantic processing for
    a minimal client beyond appending to the transcript. -/
def onEncryptedExtensions (s : State) (eeMsg : Array UInt8) : State :=
  if eeMsg.size < 4 ∨ eeMsg[0]! ≠ HandshakeType.encryptedExtensions.toByte then
    { s with phase := .failed "EE: bad framing" }
  else
    { s with transcript := s.transcript ++ eeMsg
           , phase := .waitCertOrCv }

/-- Receive Certificate (manual override variant).  The
    caller provides the already-extracted server pubkey
    bytes — useful for tests that bypass X.509 parsing
    or that present a non-cert form. -/
def onCertificate (s : State) (certMsg : Array UInt8)
    (extractedServerPubkey : Array UInt8) : State :=
  if certMsg.size < 4 ∨ certMsg[0]! ≠ HandshakeType.certificate.toByte then
    { s with phase := .failed "Cert: bad framing" }
  else
    { s with transcript := s.transcript ++ certMsg
           , serverPubkey := extractedServerPubkey
           , phase := .waitCv }

/-- Receive Certificate, parsing the DER blob with the
    full X.509 parser to extract the server pubkey.

    `certMsg` is the full Handshake-wrapped Certificate
    frame; `certDer` is the DER blob of the end-entity
    certificate from inside that message (the caller still
    has to peel the TLS Certificate list framing).

    On success the FSM stamps the appropriate server pubkey
    bytes:
      * ed25519   → 32 raw bytes
      * ecdsaP256 → 65 bytes (SEC1 uncompressed, 0x04||X||Y)
      * rsa       → DER-encoded RSAPublicKey (n + e). -/
def onCertificateDer (s : State) (certMsg certDer : Array UInt8) : State := Id.run do
  if certMsg.size < 4 ∨ certMsg[0]! ≠ HandshakeType.certificate.toByte then
    return { s with phase := .failed "Cert: bad framing" }
  match Sparkle.IP.TLS.X509.parseCertificate certDer with
  | none =>
    return { s with phase := .failed "Cert: X.509 parse failed" }
  | some cert =>
    -- Reject anything other than the three TLS sig schemes
    -- we support (matches CertificateVerify dispatch).
    match cert.spki.algorithm with
    | Sparkle.IP.TLS.X509.PublicKeyAlg.ed25519
    | Sparkle.IP.TLS.X509.PublicKeyAlg.ecdsaP256
    | Sparkle.IP.TLS.X509.PublicKeyAlg.rsa =>
      return { s with transcript := s.transcript ++ certMsg
                    , serverPubkey := cert.spki.rawKey
                    , phase := .waitCv }
    | Sparkle.IP.TLS.X509.PublicKeyAlg.other oid =>
      return { s with phase := .failed s!"Cert: unsupported pubkey OID {repr oid}" }

/-- Receive CertificateVerify.  RFC 8446 §4.4.3:
      signed content =
        ASCII " " × 64 ||
        "TLS 1.3, server CertificateVerify" ||
        0x00 ||
        Transcript-Hash(ClientHello..Certificate)

    Verify with the previously-extracted server pubkey
    (currently Ed25519 only). -/
def onCertificateVerify (s : State) (cvMsg : Array UInt8) : State := Id.run do
  if cvMsg.size < 4 ∨ cvMsg[0]! ≠ HandshakeType.certificateVerify.toByte then
    return { s with phase := .failed "CV: bad framing" }
  -- Parse body: SignatureScheme (2 bytes) + signature (vec16).
  let bodyLen :=
    (cvMsg[1]!.toNat <<< 16) |||
    (cvMsg[2]!.toNat <<<  8) |||
     cvMsg[3]!.toNat
  if cvMsg.size ≠ 4 + bodyLen ∨ bodyLen < 4 then
    return { s with phase := .failed "CV: length mismatch" }
  let sigScheme :=
    (cvMsg[4]!.toNat <<< 8) ||| cvMsg[5]!.toNat
  let sigLen :=
    (cvMsg[6]!.toNat <<< 8) ||| cvMsg[7]!.toNat
  if cvMsg.size ≠ 8 + sigLen then
    return { s with phase := .failed "CV: signature length mismatch" }
  let mut signature : Array UInt8 := Array.replicate sigLen 0
  for i in [:sigLen] do
    signature := signature.set! i cvMsg[8 + i]!
  -- Compute Transcript-Hash(...Certificate) — i.e. transcript BEFORE this CV.
  let thBeforeCv := sha256 s.transcript
  -- Build signed content per §4.4.3.
  let pad : Array UInt8 := Array.replicate 64 0x20  -- 64 spaces
  let context : Array UInt8 := "TLS 1.3, server CertificateVerify".toUTF8.toList.toArray
  let signedContent : Array UInt8 := pad ++ context ++ #[0x00] ++ thBeforeCv
  -- Dispatch on signature scheme (RFC 8446 §4.2.3).
  match sigScheme with
  | 0x0807 =>
    -- ed25519: 32-byte pubkey, 64-byte raw sig.
    if sigLen ≠ 64 ∨ s.serverPubkey.size ≠ 32 then
      return { s with phase := .failed "CV: ed25519 key/sig size wrong" }
    if Sparkle.IP.Crypto.Ed25519Sign.verify s.serverPubkey signedContent signature then
      return { s with transcript := s.transcript ++ cvMsg
                    , phase := .waitFinished }
    else
      return { s with phase := .failed "CV: ed25519 sig verification failed" }
  | 0x0403 =>
    -- ecdsa_secp256r1_sha256: 65-byte SEC1-uncompressed pubkey,
    -- DER-encoded SEQUENCE { INTEGER r, INTEGER s } signature.
    match Sparkle.IP.Crypto.P256ECDSA.parsePubkeyRaw s.serverPubkey with
    | none =>
      return { s with phase := .failed "CV: bad ECDSA P-256 pubkey encoding" }
    | some q =>
      match Sparkle.IP.Crypto.P256ECDSA.parseDerSignature signature with
      | none =>
        return { s with phase := .failed "CV: bad ECDSA DER signature" }
      | some (r, sigS) =>
        let digest := Sparkle.IP.Crypto.HKDF.sha256 signedContent
        let z := Sparkle.IP.Crypto.P256ECDSA.digestToNat digest
        if Sparkle.IP.Crypto.P256ECDSA.verify q z r sigS then
          return { s with transcript := s.transcript ++ cvMsg
                        , phase := .waitFinished }
        else
          return { s with phase := .failed "CV: ECDSA P-256 sig verification failed" }
  | 0x0804 =>
    -- rsa_pss_rsae_sha256: DER-encoded RSAPublicKey in serverPubkey.
    match Sparkle.IP.Crypto.RSAPSS.parsePubkeyDer s.serverPubkey with
    | none =>
      return { s with phase := .failed "CV: bad RSA pubkey DER" }
    | some (n, e) =>
      if Sparkle.IP.Crypto.RSAPSS.verify n e signedContent signature then
        return { s with transcript := s.transcript ++ cvMsg
                      , phase := .waitFinished }
      else
        return { s with phase := .failed "CV: RSA-PSS sig verification failed" }
  | _ =>
    return { s with phase := .failed s!"CV: unsupported sig scheme {sigScheme}" }

/-- Receive server Finished.  Verify the server's
    verify_data, then derive application secrets from the
    transcript-hash AFTER server Finished, then build the
    client Finished verify_data and stamp it into the state. -/
def onServerFinished (s : State) (finMsg : Array UInt8) : State := Id.run do
  if finMsg.size < 4 ∨ finMsg[0]! ≠ HandshakeType.finished.toByte then
    return { s with phase := .failed "Fin: bad framing" }
  let bodyLen :=
    (finMsg[1]!.toNat <<< 16) |||
    (finMsg[2]!.toNat <<<  8) |||
     finMsg[3]!.toNat
  if finMsg.size ≠ 4 + bodyLen then
    return { s with phase := .failed "Fin: length mismatch" }
  let mut serverVerifyData : Array UInt8 := Array.replicate bodyLen 0
  for i in [:bodyLen] do
    serverVerifyData := serverVerifyData.set! i finMsg[4 + i]!
  match s.handshakeSecrets with
  | none => return { s with phase := .failed "Fin: missing handshake secrets" }
  | some hs =>
    -- Transcript hash through Certificate Verify (before Finished).
    let thBeforeServerFin := sha256 s.transcript
    let expectedVerifyData :=
      finishedVerifyData hs.sHsTrafficSecret thBeforeServerFin
    if expectedVerifyData ≠ serverVerifyData then
      return { s with phase := .failed "Fin: server verify_data mismatch" }
    -- Append server Finished, derive application secrets.
    let transcript' := s.transcript ++ finMsg
    let thAfterServerFin := sha256 transcript'
    let app := deriveApplicationStage hs.handshakeSecret thAfterServerFin
    -- Compute the client Finished verify_data (transcript NOW
    -- = ClientHello..server Finished, same as above).
    let clientFvd :=
      finishedVerifyData hs.cHsTrafficSecret thAfterServerFin
    return { s with transcript := transcript'
                  , applicationSecrets := some app
                  , clientFinishedVerifyData := clientFvd
                  , phase := .connected }

/-- Build the client Finished wire message (HandshakeType +
    u24 length + verify_data). -/
def buildClientFinished (s : State) : Array UInt8 :=
  buildFinished s.clientFinishedVerifyData

end Sparkle.IP.TLS.Client
