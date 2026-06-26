/-
  IP.TLS.Server — TLS 1.3 server-side state machine
  (RFC 8446 §A.2).

  Mirror of `IP.TLS.Client`:

      START
        |  receive ClientHello, compute DHE shared, derive
        |  handshake secrets, build ServerHello.
        v
      SEND_SH
        |  emit ServerHello, then handshake-protected flight
        |  (EE + Cert + CV + server Finished).
        v
      WAIT_CFIN
        |  on client Finished: verify verify_data, derive
        |  application secrets.
        v
      CONNECTED

  The handshake messages here are NOT encrypted by the
  record layer — the caller wraps them via IP.TLS.Record
  with the appropriate handshake / application traffic keys.
  This module just implements the FSM and the
  produce/consume of plaintext handshake bytes.

  For signature production (CertificateVerify) we accept the
  three TLS 1.3 sig schemes via callbacks: the caller passes
  a `signCv` function appropriate for their cert chain.
-/

import IP.TLS.KeySchedule
import IP.TLS.Handshake
import IP.Crypto.HKDF
import IP.Crypto.X25519

namespace Sparkle.IP.TLS.Server

open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.TLS.Handshake
open Sparkle.IP.Crypto.HKDF (sha256)

inductive Phase where
  | start            : Phase
  | sentSh           : Phase
  | sentFlight       : Phase
  | waitClientFin    : Phase
  | connected        : Phase
  | failed (reason : String) : Phase
  deriving Repr, BEq, Inhabited

/-- Per-connection server state. -/
structure State where
  phase            : Phase
  /-- Server's static long-term X25519 secret (used for KEM).
      In TLS 1.3 the X25519 key is per-handshake (ephemeral),
      so this is more accurately the per-connection ephemeral. -/
  ourEcdhSecret    : Array UInt8
  /-- Server's X25519 public key (sent in ServerHello). -/
  ourEcdhPublic    : Array UInt8
  /-- Concatenation of handshake message bytes seen/sent. -/
  transcript       : Array UInt8
  /-- DHE shared secret (after ClientHello processed). -/
  dheSecret        : Array UInt8
  handshakeSecrets : Option HandshakeSecrets
  applicationSecrets : Option ApplicationSecrets
  /-- Client random captured from ClientHello. -/
  clientRandom     : Array UInt8
  /-- Session ID echo. -/
  sessionIdEcho    : Array UInt8
  deriving Repr

def initState (ourEcdhSecret ourEcdhPublic : Array UInt8) : State :=
  { phase := .start
  , ourEcdhSecret := ourEcdhSecret
  , ourEcdhPublic := ourEcdhPublic
  , transcript := #[]
  , dheSecret := #[]
  , handshakeSecrets := none
  , applicationSecrets := none
  , clientRandom := #[]
  , sessionIdEcho := #[] }

/-! ### Server flight output.

    `processClientHello` returns the bytes the server needs
    to emit, in the order they go on the wire.  The caller
    pipes them through the record layer. -/

structure FirstFlight where
  /-- ServerHello (sent as a Handshake record, not encrypted). -/
  serverHello : Array UInt8
  /-- EncryptedExtensions + Certificate + CertificateVerify +
      server Finished, concatenated.  Encrypt under the
      server handshake traffic key. -/
  flight      : Array UInt8
  deriving Repr, Inhabited

/-- Receive ClientHello, build the first-flight messages,
    update state.

    `serverRandom` is the 32-byte ServerHello.random the
    caller provides (RNG-side concern).
    `certificateBytes` is the server's Certificate body
    (already serialized into the TLS 1.3 Certificate
    message body form — see RFC 8446 §4.4.2).
    `cvBody` is the CertificateVerify body
    (SignatureScheme || vec16 signature).
    `signCv` is a callback: caller computes the signature
    over the signed-content given the current transcript
    hash. -/
def processClientHello
    (s : State) (chMsg : Array UInt8)
    (serverRandom certificateBody : Array UInt8)
    (signCv : Array UInt8 → Array UInt8) :
    State × Option FirstFlight := Id.run do
  -- Frame check.
  if chMsg.size < 4 ∨ chMsg[0]! ≠ HandshakeType.clientHello.toByte then
    return ({ s with phase := .failed "CH: bad framing" }, none)
  let bodyLen :=
    (chMsg[1]!.toNat <<< 16) |||
    (chMsg[2]!.toNat <<<  8) |||
     chMsg[3]!.toNat
  if chMsg.size ≠ 4 + bodyLen then
    return ({ s with phase := .failed "CH: length mismatch" }, none)
  let mut body : Array UInt8 := Array.replicate bodyLen 0
  for i in [:bodyLen] do
    body := body.set! i chMsg[4 + i]!
  match parseClientHelloBody body with
  | none =>
    return ({ s with phase := .failed "CH: parse failed" }, none)
  | some ch =>
    -- DHE = X25519(server_priv, client_pub).
    let dhe := Sparkle.IP.Crypto.X25519.x25519 s.ourEcdhSecret ch.clientPubkey
    -- Build ServerHello.
    let shMsg := buildServerHello serverRandom ch.legacySession s.ourEcdhPublic
    -- Transcript: CH || SH (both as Handshake-framed bytes).
    let transcript1 := s.transcript ++ chMsg ++ shMsg
    let chShHash := sha256 transcript1
    let es := earlySecret #[]
    let hs := deriveHandshakeStage es dhe chShHash
    -- EncryptedExtensions: empty body for minimal flight.
    let eeMsg := wrapHandshake HandshakeType.encryptedExtensions (be16 0)
    -- Certificate: wrap caller-provided body.
    let certMsg := wrapHandshake HandshakeType.certificate certificateBody
    -- Run signCv over Transcript-Hash(CH..Cert), then frame
    -- as CertificateVerify body.
    let transcriptForCv := transcript1 ++ eeMsg ++ certMsg
    let thBeforeCv := sha256 transcriptForCv
    let pad : Array UInt8 := Array.replicate 64 0x20
    let ctxLabel : Array UInt8 :=
      "TLS 1.3, server CertificateVerify".toUTF8.toList.toArray
    let signedContent : Array UInt8 :=
      pad ++ ctxLabel ++ #[0x00] ++ thBeforeCv
    let cvSig := signCv signedContent
    -- For the FSM we just take whatever sigScheme bytes the
    -- caller embedded: cvSig is the FULL CV body (with the
    -- SignatureScheme + vec16 wrapper).
    let cvMsg := wrapHandshake HandshakeType.certificateVerify cvSig
    -- Compute server Finished verify_data over transcript
    -- through CV.
    let transcriptThroughCv := transcriptForCv ++ cvMsg
    let thBeforeServerFin := sha256 transcriptThroughCv
    let serverVerifyData :=
      finishedVerifyData hs.sHsTrafficSecret thBeforeServerFin
    let finMsg := wrapHandshake HandshakeType.finished serverVerifyData
    -- Final transcript through server Finished.
    let transcript2 := transcriptThroughCv ++ finMsg
    -- Application secrets are derived from the transcript
    -- through server Finished (RFC 8446 §7.1 — the client
    -- uses the same transcript point), so we precompute them
    -- here so they're available before client Finished
    -- arrives.
    let thAfterServerFin := sha256 transcript2
    let app := deriveApplicationStage hs.handshakeSecret thAfterServerFin
    -- Compose flight (EE..serverFin).
    let flight := eeMsg ++ certMsg ++ cvMsg ++ finMsg
    let s' : State :=
      { s with phase := .sentFlight
             , transcript := transcript2
             , dheSecret := dhe
             , handshakeSecrets := some hs
             , applicationSecrets := some app
             , clientRandom := ch.random
             , sessionIdEcho := ch.legacySession }
    return (s', some { serverHello := shMsg, flight := flight })

/-- Receive the client's Finished message.  Verifies its
    verify_data under the c_handshake_traffic secret and
    derives the application traffic secrets. -/
def onClientFinished (s : State) (finMsg : Array UInt8) : State := Id.run do
  if finMsg.size < 4 ∨ finMsg[0]! ≠ HandshakeType.finished.toByte then
    return { s with phase := .failed "CFIN: bad framing" }
  let bodyLen :=
    (finMsg[1]!.toNat <<< 16) |||
    (finMsg[2]!.toNat <<<  8) |||
     finMsg[3]!.toNat
  if finMsg.size ≠ 4 + bodyLen then
    return { s with phase := .failed "CFIN: length mismatch" }
  let mut clientVerifyData : Array UInt8 := Array.replicate bodyLen 0
  for i in [:bodyLen] do
    clientVerifyData := clientVerifyData.set! i finMsg[4 + i]!
  match s.handshakeSecrets with
  | none => return { s with phase := .failed "CFIN: missing handshake secrets" }
  | some hs =>
    -- Transcript hash at the point the client computed its
    -- verify_data = through server Finished (the current
    -- transcript before appending client Finished).
    let thAtClientFin := sha256 s.transcript
    let expected :=
      finishedVerifyData hs.cHsTrafficSecret thAtClientFin
    if expected ≠ clientVerifyData then
      return { s with phase := .failed "CFIN: client verify_data mismatch" }
    -- Append client Finished.  Application secrets were
    -- already derived in processClientHello (using the
    -- transcript through server Finished), matching the
    -- client's derivation point.
    let transcript' := s.transcript ++ finMsg
    return { s with transcript := transcript'
                  , phase := .connected }

end Sparkle.IP.TLS.Server
