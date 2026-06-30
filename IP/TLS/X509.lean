/-
  IP.TLS.X509 — X.509 v3 certificate parser.

  Builds on `IP.TLS.ASN1` to extract from a DER-encoded
  X.509 certificate:
    * version
    * serial number
    * signature algorithm (the outer one matching the cert sig)
    * issuer / subject DistinguishedName-as-bytes
      (we keep the DER blob; parsing of RDN sequences is
      not needed for TLS sig verify)
    * validity period (notBefore / notAfter, ASCII times)
    * SubjectPublicKeyInfo: algorithm OID + raw public key
      payload (suitable for feeding into Ed25519 / ECDSA P-256
      / RSA-PSS verify)
    * the TBSCertificate byte slice (= the data the signature
      is over)
    * the cert-level signature bit string

  Reference: RFC 5280 §4.1.

      Certificate ::= SEQUENCE {
        tbsCertificate       TBSCertificate,
        signatureAlgorithm   AlgorithmIdentifier,
        signatureValue       BIT STRING
      }

      TBSCertificate ::= SEQUENCE {
        version          [0] EXPLICIT Version DEFAULT v1,
        serialNumber     INTEGER,
        signature        AlgorithmIdentifier,
        issuer           Name,
        validity         Validity,
        subject          Name,
        subjectPublicKeyInfo  SubjectPublicKeyInfo,
        ...
      }
-/

import IP.TLS.ASN1

namespace Sparkle.IP.TLS.X509

open Sparkle.IP.TLS.ASN1

/-! ### High-level cert records. -/

/-- Algorithm identifier in a TLS-relevant subset.  TLS 1.3
    cert chains use one of these three pubkey algorithms;
    other AlgorithmIdentifiers we surface generically with
    the OID and skipped parameters. -/
inductive PublicKeyAlg where
  | ed25519                          -- 1.3.101.112
  | ecdsaP256                        -- ecPublicKey + P-256 curve
  | rsa                              -- 1.2.840.113549.1.1.1
  | other (oid : Array Nat)          -- anything else (TLS will reject)
  deriving Repr, BEq, Inhabited

/-- A parsed SubjectPublicKeyInfo. -/
structure SubjectPublicKeyInfo where
  algorithm : PublicKeyAlg
  /-- The raw pubkey bytes appropriate for the algorithm:
        * ed25519   → 32 bytes (the raw key)
        * ecdsaP256 → 65 bytes (0x04 || X || Y, SEC1 uncompressed)
        * rsa       → DER-encoded RSAPublicKey
                      (SEQUENCE { n INTEGER, e INTEGER })
        * other     → the BIT STRING payload as-is. -/
  rawKey    : Array UInt8
  deriving Repr, Inhabited

/-- Validity period (notBefore, notAfter) as ASCII strings.
    UTCTime: "YYMMDDhhmmssZ" (13 bytes).
    GeneralizedTime: "YYYYMMDDhhmmssZ" (15 bytes). -/
structure Validity where
  notBefore : String
  notAfter  : String
  deriving Repr, Inhabited

/-- Parsed view of a single X.509 v3 certificate. -/
structure Certificate where
  /-- Version per RFC 5280 §4.1.2.1.  Value 0/1/2 corresponds
      to v1/v2/v3.  Most TLS certs are v3 (= 2). -/
  version       : Nat
  serialNumber  : Nat
  /-- The signature algorithm OID inside TBSCertificate.
      Must match the outer signatureAlgorithm. -/
  signatureAlgOid : Array Nat
  /-- Issuer DN bytes (DER). -/
  issuerDer     : Array UInt8
  /-- Subject DN bytes (DER). -/
  subjectDer    : Array UInt8
  validity      : Validity
  spki          : SubjectPublicKeyInfo
  /-- Byte range of TBSCertificate inside the original
      cert blob — the data covered by the outer signature.  -/
  tbsBegin      : Nat
  tbsEnd        : Nat
  /-- The outer signature value (BIT STRING payload). -/
  signature     : Array UInt8
  deriving Repr, Inhabited

/-! ### Implementation. -/

/-- Read a Validity SEQUENCE: { notBefore Time, notAfter Time }. -/
private def parseValidity (bytes : Array UInt8) (h : Header) : Option Validity := Id.run do
  match children bytes h with
  | none => return none
  | some kids =>
    if kids.size ≠ 2 then return none
    let parseTime (th : Header) : String := Id.run do
      let mut s := ""
      for i in [:th.valueLength] do
        s := s.push (Char.ofNat bytes[th.valueOffset + i]!.toNat)
      return s
    return some { notBefore := parseTime kids[0]!, notAfter := parseTime kids[1]! }

/-- Parse a SubjectPublicKeyInfo SEQUENCE:
      SEQUENCE {
        algorithm  AlgorithmIdentifier,
        subjectPublicKey  BIT STRING
      } -/
private def parseSpki (bytes : Array UInt8) (h : Header) :
    Option SubjectPublicKeyInfo := Id.run do
  match children bytes h with
  | none => return none
  | some kids =>
    if kids.size ≠ 2 then return none
    let algSeq := kids[0]!
    let bitStr := kids[1]!
    if algSeq.tag ≠ tagSequence then return none
    if bitStr.tag ≠ tagBitString then return none
    -- algorithm OID = first child of algSeq.
    match children bytes algSeq with
    | none => return none
    | some algKids =>
      if algKids.size < 1 then return none
      let oidH := algKids[0]!
      if oidH.tag ≠ tagObjectId then return none
      let oid := readObjectId bytes oidH
      -- Extract the raw key (BIT STRING payload after the
      -- unused-bits byte).
      match readBitString bytes bitStr with
      | none => return none
      | some raw =>
        -- Dispatch on algorithm OID.
        let alg : PublicKeyAlg :=
          if oidEquals oid oidEd25519 then .ed25519
          else if oidEquals oid oidEcPublicKey then
            -- ecPublicKey: check the curve parameter (second OID).
            if algKids.size ≥ 2 ∧ algKids[1]!.tag = tagObjectId then
              let curve := readObjectId bytes algKids[1]!
              if oidEquals curve oidP256 then .ecdsaP256 else .other oid
            else .other oid
          else if oidEquals oid oidRsaEncryption then .rsa
          else .other oid
        return some { algorithm := alg, rawKey := raw }

/-- Parse a full X.509 v3 certificate from DER bytes. -/
def parseCertificate (bytes : Array UInt8) : Option Certificate := Id.run do
  -- Outer SEQUENCE.
  match parseHeader bytes 0 with
  | none => return none
  | some outer =>
    if outer.tag ≠ tagSequence then return none
    match children bytes outer with
    | none => return none
    | some certKids =>
      if certKids.size ≠ 3 then return none
      let tbs := certKids[0]!
      let outerSigAlg := certKids[1]!
      let sigBitStr := certKids[2]!
      if tbs.tag ≠ tagSequence then return none
      if outerSigAlg.tag ≠ tagSequence then return none
      if sigBitStr.tag ≠ tagBitString then return none
      let _ := outerSigAlg  -- we don't currently consume this
      match children bytes tbs with
      | none => return none
      | some tbsKids =>
        -- TBSCertificate fields (with optional version):
        --   [0] EXPLICIT version INTEGER DEFAULT v1
        --   serialNumber INTEGER
        --   signature AlgorithmIdentifier
        --   issuer Name
        --   validity Validity
        --   subject Name
        --   subjectPublicKeyInfo SubjectPublicKeyInfo
        --   extensions [3] EXPLICIT (optional)
        let mut idx := 0
        let mut version := 0  -- v1 default
        if h : idx < tbsKids.size then
          let head := tbsKids[idx]
          if head.cls = .contextSpecific ∧ head.tag = 0 then
            -- EXPLICIT [0] wrapper around INTEGER version.
            match children bytes head with
            | none => return none
            | some vKids =>
              if vKids.size = 1 ∧ vKids[0]!.tag = tagInteger then
                version := readInteger bytes vKids[0]!
                idx := idx + 1
              else return none
        if idx + 5 >= tbsKids.size then return none
        let serial := tbsKids[idx]!
        let sigAlgInner := tbsKids[idx + 1]!
        let issuer := tbsKids[idx + 2]!
        let validity := tbsKids[idx + 3]!
        let subject := tbsKids[idx + 4]!
        let spkiH := tbsKids[idx + 5]!
        if serial.tag ≠ tagInteger then return none
        if sigAlgInner.tag ≠ tagSequence then return none
        if issuer.tag ≠ tagSequence then return none
        if validity.tag ≠ tagSequence then return none
        if subject.tag ≠ tagSequence then return none
        if spkiH.tag ≠ tagSequence then return none
        -- Inner signature algorithm OID.
        let inAlgKids := (children bytes sigAlgInner).getD #[]
        let sigOid := if inAlgKids.size ≥ 1 then readObjectId bytes inAlgKids[0]! else #[]
        -- Validity.
        match parseValidity bytes validity with
        | none => return none
        | some vd =>
          match parseSpki bytes spkiH with
          | none => return none
          | some spki =>
            match readBitString bytes sigBitStr with
            | none => return none
            | some sigBits =>
              -- TBSCertificate bytes (for sig coverage) = the
              -- entire TBSCert element INCLUDING its outer SEQUENCE
              -- tag + length.  `tbs` is the first child of `outer`,
              -- so its tag byte sits at `outer.valueOffset`.
              return some
                { version := version
                , serialNumber := readInteger bytes serial
                , signatureAlgOid := sigOid
                , issuerDer := Header.value bytes issuer
                , subjectDer := Header.value bytes subject
                , validity := vd
                , spki := spki
                , tbsBegin := outer.valueOffset
                , tbsEnd := tbs.endOffset
                , signature := sigBits }

/-! ### Direct Ed25519 SPKI extraction

    Lightweight scanner that finds an Ed25519 SubjectPublicKey
    inside a DER blob (full cert or bare SPKI) by locating
    the RFC 8410 §3 algorithm-OID marker

      06 03 2b 65 70

    (OBJECT IDENTIFIER, 3 bytes, value 1.3.101.112) and reading
    the BIT STRING that follows.  RFC 8410 §4 fixes the SPKI
    shape so the public key sits at a constant offset from the
    OID:

      ... 06 03 2b 65 70 03 21 00 <32-byte pubkey>

    where `03 21 00` is "BIT STRING, length 33 bytes, 0 unused
    bits".  We verify those three trailing bytes literally
    before slicing the 32-byte key — that's what distinguishes a
    real Ed25519 SPKI from accidental byte-sequence collisions
    in unrelated parts of the cert (issuer OIDs, etc.).

    Returns `none` if the OID sequence is absent or the
    BIT-STRING shape after it doesn't match. -/
def extractEd25519Pubkey (bytes : Array UInt8) : Option (Array UInt8) := Id.run do
  -- Walk the byte string looking for the 5-byte OID marker.
  let marker : Array UInt8 := #[0x06, 0x03, 0x2b, 0x65, 0x70]
  let mut i := 0
  while i + marker.size <= bytes.size do
    let mut isMatch := true
    for j in [:marker.size] do
      if bytes.getD (i + j) 0 ≠ marker.getD j 0 then
        isMatch := false
    if isMatch then
      -- After the OID expect `03 21 00` then 32 bytes of key.
      let p := i + marker.size
      if bytes.getD p       0 == 0x03 ∧
         bytes.getD (p + 1) 0 == 0x21 ∧
         bytes.getD (p + 2) 0 == 0x00 ∧
         p + 3 + 32 <= bytes.size then
        let key := (bytes.toList.drop (p + 3)).take 32 |>.toArray
        return some key
    i := i + 1
  return none

end Sparkle.IP.TLS.X509
