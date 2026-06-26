/-
  IP.Net.HFTOverTLS — pure-data integration of the HFT
  strategy with TLS 1.3 record protection.

  After the TLS handshake completes (see IP.TLS.Client), the
  client and server share two application traffic secrets:
    - c_ap_traffic_secret_0 (for client→server records)
    - s_ap_traffic_secret_0 (for server→client records)

  Each is run through `deriveRecordKeys` to produce a
  (write_key : 16B, write_iv : 12B) pair.  Records are
  encrypted with AES-128-GCM keyed by write_key, IV =
  write_iv XOR be64(seq_num), additional_data = the
  TLSCiphertext header.

  This module gives a one-shot demo:
    1. Encrypt an HFT order/quote payload as a TLS
       application_data record.
    2. Server (mirrored on the same secret pair) decrypts.
    3. Plaintext bytes can then drive the existing
       `Sparkle.IP.Net.HFTStrategy.hftStrategy` byte-stream HW.

  The HW-side coupling (Signal-typed Sparkle modules
  consuming/producing TLS records) is a future T.6.HW task —
  this is the software reference / system-test scaffolding.
-/

import IP.TLS.KeySchedule
import IP.TLS.Record

namespace Sparkle.IP.Net.HFTOverTLS

open Sparkle.IP.TLS.KeySchedule (deriveRecordKeys RecordKeys)
open Sparkle.IP.TLS.Record (ContentType encryptRecord decryptRecord)

/-- Convenience wrapper: encrypt an HFT request payload (eg
    "GET /tick HTTP/1.0\r\n…") as one TLS application_data
    record on the client→server channel.

    The caller passes the per-connection client_application
    traffic secret + the running sequence number for this
    direction. -/
def encryptRequest
    (cApSecret : Array UInt8) (seqNum : Nat) (payload : Array UInt8) :
    Array UInt8 :=
  let keys : RecordKeys := deriveRecordKeys cApSecret
  encryptRecord keys.key keys.iv seqNum .applicationData payload

/-- Decrypt a TLS application_data record on the server→client
    channel.  Returns the (real_type, plaintext) pair, or
    `none` on AEAD verification failure. -/
def decryptResponse
    (sApSecret : Array UInt8) (seqNum : Nat) (record : Array UInt8) :
    Option (ContentType × Array UInt8) :=
  let keys : RecordKeys := deriveRecordKeys sApSecret
  decryptRecord keys.key keys.iv seqNum record

/-- Symmetric helper for the server-side mirror image:
    decrypt a client-encrypted record using the same
    cApSecret + seqNum (i.e. validates we got there). -/
def decryptRequest
    (cApSecret : Array UInt8) (seqNum : Nat) (record : Array UInt8) :
    Option (ContentType × Array UInt8) :=
  let keys : RecordKeys := deriveRecordKeys cApSecret
  decryptRecord keys.key keys.iv seqNum record

/-- Server-side: encrypt a response payload as one TLS
    record on the server→client channel. -/
def encryptResponse
    (sApSecret : Array UInt8) (seqNum : Nat) (payload : Array UInt8) :
    Array UInt8 :=
  let keys : RecordKeys := deriveRecordKeys sApSecret
  encryptRecord keys.key keys.iv seqNum .applicationData payload

end Sparkle.IP.Net.HFTOverTLS
