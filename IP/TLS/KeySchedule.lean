/-
  IP.TLS.KeySchedule — TLS 1.3 key schedule (RFC 8446 §7.1).

  The schedule chains HKDF-Extract / Derive-Secret calls to
  produce a tree of secrets:

      Early Secret      ← HKDF-Extract(0, PSK)
      Handshake Secret  ← HKDF-Extract(derived(ES), (EC)DHE)
      Master Secret     ← HKDF-Extract(derived(HS), 0)

  Each "[X] Secret" further derives traffic secrets via
  Derive-Secret with labels like "c hs traffic", "s hs
  traffic", "c ap traffic", "s ap traffic", "finished".

  Per-record write_key / write_iv are derived from a traffic
  secret via HKDF-Expand-Label("key", …, 16) and
  HKDF-Expand-Label("iv", …, 12).
-/

import IP.Crypto.Codec.HKDF

namespace Sparkle.IP.TLS.KeySchedule

open Sparkle.IP.Crypto.HKDF
  (sha256 hmacSha256 hkdfExtract hkdfExpand hkdfExpandLabel deriveSecret)

/-! ### Hash output size (SHA-256 → 32 bytes). -/

def hashLen : Nat := 32

/-- The all-zero secret of `hashLen` bytes. -/
def zeroSecret : Array UInt8 := Array.replicate hashLen 0

/-- SHA-256 of the empty string — used as the
    "transcript_hash of no messages" stand-in in the
    schedule's "derived" labels. -/
def emptyHash : Array UInt8 := sha256 #[]

/-! ### Schedule stage outputs. -/

structure HandshakeSecrets where
  /-- Handshake Secret (after Extract with DHE shared secret). -/
  handshakeSecret  : Array UInt8
  /-- client_handshake_traffic_secret. -/
  cHsTrafficSecret : Array UInt8
  /-- server_handshake_traffic_secret. -/
  sHsTrafficSecret : Array UInt8
  deriving Repr

structure ApplicationSecrets where
  /-- Master Secret. -/
  masterSecret     : Array UInt8
  /-- client_application_traffic_secret_0. -/
  cApTrafficSecret : Array UInt8
  /-- server_application_traffic_secret_0. -/
  sApTrafficSecret : Array UInt8
  /-- exporter_master_secret. -/
  exporterSecret   : Array UInt8
  deriving Repr

/-! ### Derive functions. -/

/-- Compute Early Secret = HKDF-Extract(0_salt, PSK).
    No-PSK handshakes use PSK = 0^hashLen. -/
def earlySecret (psk : Array UInt8) : Array UInt8 :=
  let p := if psk.size = 0 then zeroSecret else psk
  hkdfExtract zeroSecret p

/-- Compute the Handshake Secret stage + both handshake
    traffic secrets.  `transcriptCH_SH` = Transcript-Hash
    of (ClientHello || ServerHello). -/
def deriveHandshakeStage
    (earlySec dheSecret transcriptCH_SH : Array UInt8) :
    HandshakeSecrets :=
  -- Derive-Secret(ES, "derived", "")
  let derived := deriveSecret earlySec "derived" emptyHash
  -- HKDF-Extract(derived, dheSecret) = Handshake Secret
  let hs := hkdfExtract derived dheSecret
  let cHs := deriveSecret hs "c hs traffic" transcriptCH_SH
  let sHs := deriveSecret hs "s hs traffic" transcriptCH_SH
  { handshakeSecret := hs, cHsTrafficSecret := cHs, sHsTrafficSecret := sHs }

/-- Compute the Application Secret stage.
    `transcriptCH_SF` = Transcript-Hash(ClientHello..server Finished). -/
def deriveApplicationStage
    (handshakeSec transcriptCH_SF : Array UInt8) :
    ApplicationSecrets :=
  let derived := deriveSecret handshakeSec "derived" emptyHash
  let ms := hkdfExtract derived zeroSecret
  let cAp := deriveSecret ms "c ap traffic" transcriptCH_SF
  let sAp := deriveSecret ms "s ap traffic" transcriptCH_SF
  let exp := deriveSecret ms "exp master" transcriptCH_SF
  { masterSecret := ms
  , cApTrafficSecret := cAp
  , sApTrafficSecret := sAp
  , exporterSecret := exp }

/-! ### Per-record key / iv derivation (§7.3). -/

structure RecordKeys where
  key : Array UInt8     -- 16 bytes for AES-128-GCM
  iv  : Array UInt8     -- 12 bytes static_iv
  deriving Repr

/-- Derive (key, iv) from a traffic secret per RFC 8446 §7.3:
      key = HKDF-Expand-Label(secret, "key", "", key_length)
      iv  = HKDF-Expand-Label(secret, "iv",  "", iv_length)

    For AES-128-GCM: key_length = 16, iv_length = 12. -/
def deriveRecordKeys (trafficSecret : Array UInt8) : RecordKeys :=
  { key := hkdfExpandLabel trafficSecret "key" #[] 16
  , iv  := hkdfExpandLabel trafficSecret "iv"  #[] 12 }

/-! ### Finished verify_data (§4.4.4).

    finished_key = HKDF-Expand-Label(base_key, "finished", "", Hash.length)
    verify_data  = HMAC(finished_key, Transcript-Hash(messages)) -/

/-- Derive the Finished verify_data.

    `baseKey` is the corresponding "handshake traffic secret"
    (server's for Server-Finished, client's for
    Client-Finished).  `transcriptHash` is the SHA-256 of
    the transcript through the message immediately preceding
    Finished. -/
def finishedVerifyData
    (baseKey transcriptHash : Array UInt8) : Array UInt8 :=
  let fk := hkdfExpandLabel baseKey "finished" #[] hashLen
  hmacSha256 fk transcriptHash

end Sparkle.IP.TLS.KeySchedule
