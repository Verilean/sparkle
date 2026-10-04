/-
  IP.Crypto.CTAP2Data — FIDO2/CTAP2 data-structure builders (pure).

  Builds the exact byte layouts a minimal (no-PIN, no-resident-key)
  authenticator emits, per the WebAuthn / CTAP2 specs:

    * COSE_Key for an ES256 / P-256 public key,
    * attestedCredentialData,
    * authenticatorData,
    * the makeCredential and getAssertion CBOR response maps.

  All pure `Nat` / `Array UInt8`; this milestone (M1) locks the
  byte layouts before any hardware.  The hardware milestones feed
  the same bytes through the on-chip SHA-256 + P-256 signer.
-/
import IP.Crypto.Codec.CBOR
import IP.Crypto.Codec.DerSig
import IP.Crypto.SHA256
import IP.Crypto.Proof.P256ECDSA

namespace Sparkle.IP.Crypto.CTAP2Data

-- `CBOR.*` / `DerSig.*` resolve because the sibling namespaces
-- `Sparkle.IP.Crypto.CBOR` / `.DerSig` are in scope from inside
-- `Sparkle.IP.Crypto.CTAP2Data`.

/-- SHA-256 of a byte array as 32 big-endian bytes (the pure
    `sha256OfBytes` returns 8 × `BitVec 32`). -/
def sha256Bytes (input : Array UInt8) : Array UInt8 := Id.run do
  let words := Sparkle.IP.Crypto.SHA256.sha256OfBytes input
  let mut out : Array UInt8 := #[]
  for w in words do
    for i in [:4] do
      out := out.push (UInt8.ofNat ((w.toNat >>> ((3 - i) * 8)) &&& 0xFF))
  return out

/-- `n` as `width` big-endian bytes (zero-padded / truncated). -/
def beN (n : Nat) (width : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for i in [:width] do
    out := out.push (UInt8.ofNat ((n >>> ((width - 1 - i) * 8)) &&& 0xFF))
  return out

/-! ### authenticatorData flags -/

/-- makeCredential: User Present (0x01) + Attested-credential-data
    present (0x40) = 0x45. -/
def flagsMakeCred : UInt8 := 0x45
/-- getAssertion: User Present only = 0x05.  (0x01 UP + 0x04 UV;
    spec's minimal example uses 0x05 = UP+UV; UP-only is 0x01.
    We use 0x05 to mirror the common minimal authenticator.) -/
def flagsGetAssertion : UInt8 := 0x05

/-! ### COSE_Key for ES256 / P-256 -/

/-- COSE_Key CBOR map for an EC2 / ES256 / P-256 public key:
      { 1: 2 (kty EC2), 3: -7 (alg ES256), -1: 1 (crv P-256),
        -2: bstr x(32), -3: bstr y(32) }
    Keys are emitted in canonical order by `CBOR.mapPairs`. -/
def coseKeyP256 (x y : Nat) : Array UInt8 :=
  CBOR.mapPairs [
    (CBOR.uint 1,          CBOR.uint 2),          -- kty: EC2
    (CBOR.uint 3,          CBOR.negIntOfMag 7),   -- alg: ES256 (-7)
    (CBOR.negIntOfMag 1,   CBOR.uint 1),          -- crv: P-256 (label -1 → 1)
    (CBOR.negIntOfMag 2,   CBOR.bstr (beN x 32)), -- x (label -2)
    (CBOR.negIntOfMag 3,   CBOR.bstr (beN y 32))  -- y (label -3)
  ]

/-! ### attestedCredentialData -/

/-- `aaguid(16) ‖ credIdLen(2 BE) ‖ credId ‖ COSE_Key`. -/
def attestedCredData (aaguid credId : Array UInt8) (x y : Nat) : Array UInt8 :=
  aaguid ++ beN credId.size 2 ++ credId ++ coseKeyP256 x y

/-! ### authenticatorData -/

/-- `rpIdHash(32) ‖ flags(1) ‖ signCount(4 BE) ‖ [attestedCredData]`. -/
def authenticatorData (rpIdHash : Array UInt8) (flags : UInt8)
    (signCount : Nat) (attCred : Option (Array UInt8)) : Array UInt8 :=
  rpIdHash ++ #[flags] ++ beN signCount 4 ++ (attCred.getD #[])

/-! ### Response CBOR maps -/

/-- makeCredential response: `{ 1: "packed", 2: bstr authData,
    3: { alg: -7, sig: bstr DER } }`.  (Keys 1/2/3 = fmt / authData
    / attStmt; attStmt keys are text strings "alg"/"sig".) -/
def makeCredentialResponse (authData sigDer : Array UInt8) : Array UInt8 :=
  let attStmt := CBOR.mapPairs [
    (CBOR.tstr "alg", CBOR.negIntOfMag 7),
    (CBOR.tstr "sig", CBOR.bstr sigDer)
  ]
  CBOR.mapPairs [
    (CBOR.uint 1, CBOR.tstr "packed"),
    (CBOR.uint 2, CBOR.bstr authData),
    (CBOR.uint 3, attStmt)
  ]

/-- getAssertion response: `{ 1: { id: bstr credId, type:
    "public-key" }, 2: bstr authData, 3: bstr DER }`. -/
def getAssertionResponse (credId authData sigDer : Array UInt8) : Array UInt8 :=
  let credential := CBOR.mapPairs [
    (CBOR.tstr "id",   CBOR.bstr credId),
    (CBOR.tstr "type", CBOR.tstr "public-key")
  ]
  CBOR.mapPairs [
    (CBOR.uint 1, credential),
    (CBOR.uint 2, CBOR.bstr authData),
    (CBOR.uint 3, CBOR.bstr sigDer)
  ]

end Sparkle.IP.Crypto.CTAP2Data
