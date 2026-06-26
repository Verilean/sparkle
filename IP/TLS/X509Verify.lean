/-
  IP.TLS.X509Verify — certificate chain validation.

  Given a leaf cert and a chain of issuer certs (ending in
  a self-signed root), check:
    1. For each link `(cert, issuer)`:
       * cert.issuerDer = issuer.subjectDer
       * cert.signature verifies under issuer.spki using
         tbsCert.signatureAlgOid
    2. The root's pubkey is in the caller-supplied trust set.

  Scope: covers the three TLS 1.3 sig algorithms
  (Ed25519, ECDSA-P256-SHA256, RSA-PSS-SHA256).

  Out of scope for this iteration: validity-period checks
  (notBefore/notAfter), critical-extension processing, name
  constraints, CRL/OCSP revocation.  Those land later if
  needed — for a TLS sig-verify happy path they're not
  required.
-/

import IP.TLS.X509
import IP.Crypto.Ed25519Sign
import IP.Crypto.P256ECDSA
import IP.Crypto.RSAPSS

namespace Sparkle.IP.TLS.X509Verify

open Sparkle.IP.TLS.X509
open Sparkle.IP.TLS.ASN1 (oidEd25519 oidEcdsaWithSha256 oidEquals)

/-! ### Per-link signature verification.

    Given a child cert's bytes (with its TBS range and
    signature) and the issuer's parsed SPKI, verify that the
    issuer signed the child's TBS bytes. -/

/-- Compute SHA-256 over the TBSCertificate slice.  Used for
    ECDSA-P256-SHA256 and RSA-PSS-SHA256 sig schemes. -/
private def tbsBytes (cert : Certificate) (raw : Array UInt8) : Array UInt8 := Id.run do
  let n := cert.tbsEnd - cert.tbsBegin
  let mut out : Array UInt8 := Array.replicate n 0
  for i in [:n] do
    if cert.tbsBegin + i < raw.size then
      out := out.set! i raw[cert.tbsBegin + i]!
  return out

/-- Well-known TLS 1.3 sig-algorithm OIDs for cert
    signatures (RFC 5280 §A.2 + RFC 8410 §3 + RFC 8017 §C). -/
private def oidSha256WithRSAEncryption : List Nat :=
  [1, 2, 840, 113549, 1, 1, 11]

private def oidRsassaPss : List Nat :=
  [1, 2, 840, 113549, 1, 1, 10]

/-- Verify `cert.signature` against `issuerSpki` using the
    algorithm in `cert.signatureAlgOid`.  Returns true on
    valid signature.

    Supported schemes:
      * 1.3.101.112              Ed25519
      * 1.2.840.10045.4.3.2      ecdsa-with-SHA256 (P-256)
      * 1.2.840.113549.1.1.11    sha256WithRSAEncryption
      * 1.2.840.113549.1.1.10    rsassa-pss (PSS-SHA256)

    Unsupported OIDs fail closed. -/
def verifySignature (cert : Certificate) (raw : Array UInt8)
    (issuerSpki : SubjectPublicKeyInfo) : Bool := Id.run do
  let tbs := tbsBytes cert raw
  let oid := cert.signatureAlgOid.toList
  if oidEquals cert.signatureAlgOid oidEd25519 then
    -- Ed25519: issuer must be Ed25519 too.
    match issuerSpki.algorithm with
    | PublicKeyAlg.ed25519 =>
      return Sparkle.IP.Crypto.Ed25519Sign.verify
        issuerSpki.rawKey tbs cert.signature
    | _ => return false
  else if oidEquals cert.signatureAlgOid oidEcdsaWithSha256 then
    -- ECDSA-P256-SHA256.
    match issuerSpki.algorithm with
    | PublicKeyAlg.ecdsaP256 =>
      match Sparkle.IP.Crypto.P256ECDSA.parsePubkeyRaw issuerSpki.rawKey with
      | none => return false
      | some q =>
        match Sparkle.IP.Crypto.P256ECDSA.parseDerSignature cert.signature with
        | none => return false
        | some (r, s) =>
          let digest := Sparkle.IP.Crypto.HKDF.sha256 tbs
          let z := Sparkle.IP.Crypto.P256ECDSA.digestToNat digest
          return Sparkle.IP.Crypto.P256ECDSA.verify q z r s
    | _ => return false
  else if oid = oidSha256WithRSAEncryption ∨ oid = oidRsassaPss then
    match issuerSpki.algorithm with
    | PublicKeyAlg.rsa =>
      match Sparkle.IP.Crypto.RSAPSS.parsePubkeyDer issuerSpki.rawKey with
      | none => return false
      | some (n, e) =>
        if oid = oidSha256WithRSAEncryption then
          -- PKCS#1 v1.5 path: NOT implemented yet — this is
          -- the legacy "rsaEncryption with SHA-256" common in
          -- v1 chains.  Falls through to false until we add
          -- PKCS1v15 verify.
          return false
        else
          -- RSA-PSS-SHA256.
          return Sparkle.IP.Crypto.RSAPSS.verify n e tbs cert.signature
    | _ => return false
  else
    return false

/-! ### Chain walk.

    The input chain is a list of (certDerBytes × Certificate)
    pairs in order leaf → intermediate → ... → root.  The root
    is self-signed (its issuer equals its subject) AND must
    appear in the trust set (matched by SPKI bytes). -/

structure CertLink where
  raw  : Array UInt8
  cert : Certificate
  deriving Inhabited

/-- Build a CertLink from raw DER bytes; returns `none` on
    malformed input. -/
def mkLink (raw : Array UInt8) : Option CertLink :=
  match parseCertificate raw with
  | none => none
  | some c => some { raw := raw, cert := c }

/-- Trust set: caller provides the list of acceptable root
    SPKI raw key payloads.  We compare by `rawKey` bytes only —
    sufficient for self-signed roots since the algorithm OID
    must also match issuer→child link semantically. -/
abbrev TrustSet := List (Array UInt8)

/-- Validate the entire chain.

    Steps for each adjacent pair (child, issuer):
      * child.issuerDer = issuer.subjectDer
      * issuer signed child

    For the root (last link):
      * root.issuerDer = root.subjectDer  (self-signed)
      * root signed itself
      * root.spki.rawKey ∈ trustSet -/
def validateChain (chain : List CertLink) (trust : TrustSet) : Bool := Id.run do
  match chain with
  | [] => return false
  | leaf :: rest =>
    -- Walk pairs (child, issuer).
    let mut cur := leaf
    let mut remaining := rest
    while !remaining.isEmpty do
      let issuer := remaining.head!
      -- DN match.
      if cur.cert.issuerDer ≠ issuer.cert.subjectDer then
        return false
      -- Signature.
      if !verifySignature cur.cert cur.raw issuer.cert.spki then
        return false
      cur := issuer
      remaining := remaining.tail!
    -- `cur` is now the root.  Check self-signed + trusted.
    if cur.cert.issuerDer ≠ cur.cert.subjectDer then
      return false
    if !verifySignature cur.cert cur.raw cur.cert.spki then
      return false
    -- Trust set membership via byte-equality on rawKey.
    let trusted := trust.any (· = cur.cert.spki.rawKey)
    return trusted

end Sparkle.IP.TLS.X509Verify
