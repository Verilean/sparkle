/-
  IP.TLS.Record — TLS 1.3 record layer (RFC 8446 §5).

  A TLS record:
    struct {
      ContentType opaque_type = application_data;  /* 23 */
      ProtocolVersion legacy_record_version = 0x0303;
      uint16 length;
      opaque encrypted_record[TLSCiphertext.length];
    } TLSCiphertext;

  The encrypted_record is:
    AEAD-Encrypted(write_key,
                   nonce,
                   additional_data = TLSCiphertext header (5 bytes),
                   plaintext = TLSInnerPlaintext)

  TLSInnerPlaintext is the actual content + ContentType byte
  appended after the data:
    struct {
      opaque content[TLSPlaintext.length];
      ContentType type;                  /* real type */
      uint8 zeros[length_of_padding];   /* trailing zero pad */
    } TLSInnerPlaintext;

  Per-record nonce derivation (§5.3):
    nonce = static_iv XOR be64(seqnum)  -- iv is 12 bytes,
                                           seqnum becomes
                                           low 8 bytes
-/

import IP.Crypto.AESGCM

namespace Sparkle.IP.TLS.Record

open Sparkle.IP.Crypto.AESGCM (encryptAead decryptAead GcmCiphertext)

/-- TLS 1.3 ContentType (RFC 8446 §B.1). -/
inductive ContentType where
  | invalid           : ContentType  -- 0
  | changeCipherSpec  : ContentType  -- 20 (legacy, ignored on RX)
  | alert             : ContentType  -- 21
  | handshake         : ContentType  -- 22
  | applicationData   : ContentType  -- 23
  deriving Repr, BEq, DecidableEq

def ContentType.toByte : ContentType → UInt8
  | .invalid          => 0
  | .changeCipherSpec => 20
  | .alert            => 21
  | .handshake        => 22
  | .applicationData  => 23

def ContentType.ofByte? : UInt8 → Option ContentType
  | 0  => some .invalid
  | 20 => some .changeCipherSpec
  | 21 => some .alert
  | 22 => some .handshake
  | 23 => some .applicationData
  | _  => none

/-! ### Nonce derivation (RFC 8446 §5.3). -/

/-- Build the per-record nonce: pad seqnum to 12 bytes
    (big-endian, left-zeros), XOR with static IV. -/
def buildNonce (staticIV : Array UInt8) (seqNum : Nat) : Array UInt8 := Id.run do
  let mut nonce : Array UInt8 := Array.replicate 12 0
  for i in [:8] do
    let shift := (7 - i) * 8
    nonce := nonce.set! (4 + i) (UInt8.ofNat ((seqNum >>> shift) &&& 0xFF))
  -- XOR with staticIV.
  let n := min 12 staticIV.size
  for i in [:n] do
    nonce := nonce.set! i (nonce[i]! ^^^ staticIV[i]!)
  return nonce

/-! ### Record build / parse. -/

/-- TLSCiphertext header: opaque_type(1) || legacy_version(2)
    || length(2) = 5 bytes.  This is the AEAD additional_data. -/
def buildRecordHeader (cipherLen : Nat) : Array UInt8 :=
  #[ ContentType.applicationData.toByte
   , 0x03, 0x03                              -- TLS 1.2 legacy version
   , UInt8.ofNat ((cipherLen >>> 8) &&& 0xFF)
   , UInt8.ofNat (cipherLen &&& 0xFF) ]

/-- Encrypt one TLS record per RFC 8446 §5.2.

    `inner` is the TLSInnerPlaintext content (handshake bytes,
    application data, alert payload, ...).  `realType` is the
    ContentType to embed after the data per the inner
    plaintext format. -/
def encryptRecord
    (writeKey staticIV : Array UInt8) (seqNum : Nat)
    (realType : ContentType) (inner : Array UInt8) :
    Array UInt8 := Id.run do
  let nonce := buildNonce staticIV seqNum
  -- Build TLSInnerPlaintext: content || type byte (no padding for now).
  let tlsInner := inner ++ #[realType.toByte]
  -- The TLSCiphertext "length" field is the size of the
  -- encrypted_record = ciphertext_len + tag(16).
  let cipherLen := tlsInner.size + 16
  let header := buildRecordHeader cipherLen
  let res : GcmCiphertext := encryptAead writeKey nonce tlsInner header
  -- Final record = header || ciphertext || tag
  return header ++ res.ciphertext ++ res.tag

/-- Parse + decrypt one TLS record.  Returns
    `some (realType, plaintext)` on success, `none` on AEAD
    failure or malformed header. -/
def decryptRecord
    (writeKey staticIV : Array UInt8) (seqNum : Nat)
    (record : Array UInt8) :
    Option (ContentType × Array UInt8) := Id.run do
  if record.size < 5 + 16 then return none
  -- Verify outer header.
  if record[0]! ≠ ContentType.applicationData.toByte then return none
  let cipherLen :=
    (record[3]!.toNat <<< 8) ||| record[4]!.toNat
  if record.size ≠ 5 + cipherLen then return none
  -- Split: header (5 bytes additional_data) || ciphertext || tag (16 bytes)
  let header : Array UInt8 :=
    #[record[0]!, record[1]!, record[2]!, record[3]!, record[4]!]
  let payloadLen := cipherLen - 16
  let mut ct : Array UInt8 := Array.replicate payloadLen 0
  for i in [:payloadLen] do
    ct := ct.set! i record[5 + i]!
  let mut tag : Array UInt8 := Array.replicate 16 0
  for i in [:16] do
    tag := tag.set! i record[5 + payloadLen + i]!
  let nonce := buildNonce staticIV seqNum
  match decryptAead writeKey nonce ct header tag with
  | none => return none
  | some innerPad =>
    -- Strip trailing zero padding, find the real type byte
    -- (the last non-zero byte).
    let mut k : Int := (innerPad.size : Int) - 1
    while k ≥ 0 ∧ innerPad[k.toNat]! = 0 do
      k := k - 1
    if k < 0 then return none
    let realByte := innerPad[k.toNat]!
    match ContentType.ofByte? realByte with
    | none => return none
    | some realType =>
      let mut content : Array UInt8 := Array.replicate k.toNat 0
      for i in [:k.toNat] do
        content := content.set! i innerPad[i]!
      return some (realType, content)

end Sparkle.IP.TLS.Record
