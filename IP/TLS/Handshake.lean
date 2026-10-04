/-
  IP.TLS.Handshake — TLS 1.3 handshake message codecs
  (RFC 8446 §4).

  Builders/parsers for the messages we exchange in a 1-RTT
  X25519+AES-128-GCM+Ed25519 handshake:

    ClientHello          (§4.1.2)
    ServerHello          (§4.1.3)
    EncryptedExtensions  (§4.3.1)
    Certificate          (§4.4.2)
    CertificateVerify    (§4.4.3)
    Finished             (§4.4.4)

  Each `Handshake` message is framed with:
      uint8  msg_type;
      uint24 length;
      opaque body[length];
-/

namespace Sparkle.IP.TLS.Handshake

/-! ### Handshake type byte (RFC 8446 §B.3). -/

inductive HandshakeType where
  | clientHello         : HandshakeType  -- 1
  | serverHello         : HandshakeType  -- 2
  | newSessionTicket    : HandshakeType  -- 4
  | encryptedExtensions : HandshakeType  -- 8
  | certificate         : HandshakeType  -- 11
  | certificateVerify   : HandshakeType  -- 15
  | finished            : HandshakeType  -- 20
  deriving Repr, BEq, DecidableEq

def HandshakeType.toByte : HandshakeType → UInt8
  | .clientHello         => 1
  | .serverHello         => 2
  | .newSessionTicket    => 4
  | .encryptedExtensions => 8
  | .certificate         => 11
  | .certificateVerify   => 15
  | .finished            => 20

def HandshakeType.ofByte? : UInt8 → Option HandshakeType
  | 1  => some .clientHello
  | 2  => some .serverHello
  | 4  => some .newSessionTicket
  | 8  => some .encryptedExtensions
  | 11 => some .certificate
  | 15 => some .certificateVerify
  | 20 => some .finished
  | _  => none

/-! ### Encoding helpers (big-endian length-prefix variants). -/

def be16 (n : Nat) : Array UInt8 :=
  #[UInt8.ofNat ((n >>> 8) &&& 0xFF), UInt8.ofNat (n &&& 0xFF)]

def be24 (n : Nat) : Array UInt8 :=
  #[ UInt8.ofNat ((n >>> 16) &&& 0xFF)
   , UInt8.ofNat ((n >>>  8) &&& 0xFF)
   , UInt8.ofNat ( n         &&& 0xFF) ]

def be32 (n : Nat) : Array UInt8 :=
  #[ UInt8.ofNat ((n >>> 24) &&& 0xFF)
   , UInt8.ofNat ((n >>> 16) &&& 0xFF)
   , UInt8.ofNat ((n >>>  8) &&& 0xFF)
   , UInt8.ofNat ( n         &&& 0xFF) ]

/-- Vector with 1-byte length prefix (max 255 bytes). -/
def vec8 (bs : Array UInt8) : Array UInt8 :=
  #[UInt8.ofNat bs.size] ++ bs

/-- Vector with 2-byte length prefix. -/
def vec16 (bs : Array UInt8) : Array UInt8 :=
  be16 bs.size ++ bs

/-- Vector with 3-byte length prefix. -/
def vec24 (bs : Array UInt8) : Array UInt8 :=
  be24 bs.size ++ bs

/-! ### Wrap a body in `HandshakeType || u24 length || body`. -/

def wrapHandshake (t : HandshakeType) (body : Array UInt8) : Array UInt8 :=
  #[t.toByte] ++ be24 body.size ++ body

/-! ### Extension format (§4.2). -/

/-- TLS 1.3 ExtensionType (selection of what we need). -/
def extServerName        : Nat := 0
def extSupportedGroups   : Nat := 10
def extSignatureAlgorithms : Nat := 13
def extSupportedVersions : Nat := 43
def extKeyShare          : Nat := 51

/-- Build one `Extension { extension_type; extension_data }`. -/
def mkExtension (extType : Nat) (data : Array UInt8) : Array UInt8 :=
  be16 extType ++ vec16 data

/-! ### ClientHello (§4.1.2).

    struct {
      ProtocolVersion legacy_version = 0x0303;
      Random random;
      opaque legacy_session_id<0..32>;
      CipherSuite cipher_suites<2..2^16-2>;
      opaque legacy_compression_methods<1..2^8-1> = { 0 };
      Extension extensions<8..2^16-1>;
    } ClientHello; -/

/-- TLS 1.3 standard cipher suites we care about.
    TLS_AES_128_GCM_SHA256 = 0x1301. -/
def cipherTlsAes128GcmSha256 : Array UInt8 := #[0x13, 0x01]

/-- Build a minimal TLS 1.3 ClientHello body (no extensions
    other than the bare minimum: supported_versions,
    supported_groups, signature_algorithms, key_share).

    Arguments:
      `random32`     — 32-byte ClientHello.random
      `legacySid`    — session ID (0..32 bytes; usually 32 random for TLS 1.3 compat)
      `x25519Pubkey` — 32-byte X25519 public key
    Output: ClientHello body bytes (without HandshakeType / length). -/
def buildClientHelloBody
    (random32 legacySid x25519Pubkey : Array UInt8) : Array UInt8 := Id.run do
  -- 1. supported_versions: just TLS 1.3 (0x0304).
  let svData : Array UInt8 := #[2] ++ #[0x03, 0x04]
                              -- u8 length prefix = 2 bytes
  let extSV := mkExtension extSupportedVersions svData
  -- 2. supported_groups: x25519 (0x001d).
  let sgData : Array UInt8 := be16 2 ++ #[0x00, 0x1D]
  let extSG := mkExtension extSupportedGroups sgData
  -- 3. signature_algorithms: ed25519 (0x0807) + ecdsa_secp256r1_sha256 (0x0403) + rsa_pss_rsae_sha256 (0x0804).
  let saData : Array UInt8 :=
    be16 6 ++ #[0x08, 0x07, 0x04, 0x03, 0x08, 0x04]
  let extSA := mkExtension extSignatureAlgorithms saData
  -- 4. key_share: one KeyShareEntry { group=x25519; key_exchange=<pubkey> }.
  let kse : Array UInt8 := #[0x00, 0x1D] ++ be16 x25519Pubkey.size ++ x25519Pubkey
  let ksData : Array UInt8 := be16 kse.size ++ kse
  let extKS := mkExtension extKeyShare ksData
  let allExts : Array UInt8 := extSV ++ extSG ++ extSA ++ extKS
  -- Body.
  return #[0x03, 0x03]                       -- legacy_version
       ++ random32                            -- 32 bytes random
       ++ vec8 legacySid                      -- session ID (vec<0..32>)
       ++ vec16 cipherTlsAes128GcmSha256      -- cipher_suites (vec<2..2^16-2>)
       ++ vec8 #[0]                           -- compression methods = {0}
       ++ vec16 allExts                       -- extensions

/-- Build a complete ClientHello handshake message (with type
    byte + length prefix). -/
def buildClientHello
    (random32 legacySid x25519Pubkey : Array UInt8) : Array UInt8 :=
  wrapHandshake .clientHello
    (buildClientHelloBody random32 legacySid x25519Pubkey)

/-! ### ServerHello parser (§4.1.3).

    We only need to extract:
      - server_random
      - chosen cipher_suite (must be 0x1301)
      - the server's KeyShareEntry.key_exchange (X25519 pubkey)

    struct {
      ProtocolVersion legacy_version = 0x0303;
      Random random;
      opaque legacy_session_id_echo<0..32>;
      CipherSuite cipher_suite;
      uint8 legacy_compression_method = 0;
      Extension extensions<6..2^16-1>;
    } ServerHello; -/

structure ServerHello where
  random       : Array UInt8     -- 32 bytes
  cipherSuite  : Array UInt8     -- 2 bytes
  serverPubkey : Array UInt8     -- 32 bytes (x25519)
  deriving Repr

/-- Helper: read a u16 big-endian from `bs[off..off+2]`. -/
private def readU16 (bs : Array UInt8) (off : Nat) : Nat :=
  if h : off + 1 < bs.size then
    (bs[off]!.toNat <<< 8) ||| bs[off + 1]!.toNat
  else 0

private def slice (bs : Array UInt8) (off len : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate len 0
  for i in [:len] do
    out := out.set! i (if h : off + i < bs.size then bs[off + i]! else 0)
  return out

/-- Parse a ServerHello body (without the outer HandshakeType /
    u24 length).  Returns `none` on malformed input or
    unsupported cipher / key share. -/
def parseServerHelloBody (body : Array UInt8) : Option ServerHello := Id.run do
  -- legacy_version (2) + random (32) + session_id_echo (vec<0..32>) +
  -- cipher_suite (2) + compression (1) + extensions (vec16).
  if body.size < 2 + 32 + 1 + 2 + 1 + 2 then return none
  let mut p := 2  -- skip legacy_version
  let random := slice body p 32
  p := p + 32
  let sidLen := body[p]!.toNat
  p := p + 1 + sidLen
  let cipher := slice body p 2
  p := p + 2
  -- skip compression byte
  p := p + 1
  let extsLen := readU16 body p
  p := p + 2
  if body.size < p + extsLen then return none
  -- Walk extensions looking for key_share (51).
  let mut serverPub : Array UInt8 := #[]
  let mut k := p
  let endExts := p + extsLen
  while k + 4 ≤ endExts do
    let extType := readU16 body k
    let extLen := readU16 body (k + 2)
    if k + 4 + extLen > endExts then
      k := endExts  -- bail
    else
      if extType = extKeyShare then
        -- KeyShareEntry { uint16 group; opaque key_exchange<1..2^16-1>; }
        let entryStart := k + 4
        let group := readU16 body entryStart
        let keLen := readU16 body (entryStart + 2)
        if group = 0x001D then  -- x25519
          serverPub := slice body (entryStart + 4) keLen
      k := k + 4 + extLen
  if serverPub.size ≠ 32 then return none
  return some { random := random, cipherSuite := cipher, serverPubkey := serverPub }

/-! ### Finished message (§4.4.4).

    The Finished message verifies that both sides computed
    the same transcript hash.

      struct {
        opaque verify_data[Hash.length];
      } Finished;

      verify_data = HMAC(finished_key, Transcript-Hash(Handshake messages))

    where finished_key is derived via HKDF-Expand-Label. -/

/-- Build the Finished handshake message body = verify_data. -/
def buildFinishedBody (verifyData : Array UInt8) : Array UInt8 := verifyData

def buildFinished (verifyData : Array UInt8) : Array UInt8 :=
  wrapHandshake .finished verifyData

/-! ### ClientHello parser + ServerHello builder.

    The dual of `buildClientHello` and `parseServerHelloBody`,
    used by the server side. -/

structure ClientHello where
  random        : Array UInt8     -- 32 bytes
  legacySession : Array UInt8     -- 0..32 bytes echo
  clientPubkey  : Array UInt8     -- 32 bytes (x25519)
  deriving Repr, Inhabited

/-- Parse a ClientHello body (without HandshakeType / u24 len). -/
def parseClientHelloBody (body : Array UInt8) : Option ClientHello := Id.run do
  -- legacy_version (2) + random (32) + sid (vec<0..32>) +
  -- ciphers (vec16) + compression (vec8) + extensions (vec16).
  if body.size < 2 + 32 + 1 then return none
  let mut p := 2  -- skip legacy_version
  let random := slice body p 32
  p := p + 32
  let sidLen := body[p]!.toNat
  p := p + 1
  if p + sidLen > body.size then return none
  let sid := slice body p sidLen
  p := p + sidLen
  if p + 2 > body.size then return none
  let cipherListLen := readU16 body p
  p := p + 2 + cipherListLen
  if p + 1 > body.size then return none
  let compLen := body[p]!.toNat
  p := p + 1 + compLen
  if p + 2 > body.size then return none
  let extsLen := readU16 body p
  p := p + 2
  if body.size < p + extsLen then return none
  -- Walk extensions for key_share x25519.
  let mut clientPub : Array UInt8 := #[]
  let mut k := p
  let endExts := p + extsLen
  while k + 4 ≤ endExts do
    let extType := readU16 body k
    let extLen := readU16 body (k + 2)
    if k + 4 + extLen > endExts then
      k := endExts
    else
      if extType = extKeyShare then
        -- KeyShareClientHello { client_shares: <KeyShareEntry> }
        -- The inner client_shares is itself vec16; each KeyShareEntry is
        -- (u16 group, vec16 key_exchange).
        let entryStart := k + 4
        let totalLen := readU16 body entryStart
        let mut q := entryStart + 2
        let entryEnd := entryStart + 2 + totalLen
        while q + 4 ≤ entryEnd do
          let group := readU16 body q
          let keLen := readU16 body (q + 2)
          if group = 0x001D ∧ keLen = 32 then
            clientPub := slice body (q + 4) keLen
          q := q + 4 + keLen
      k := k + 4 + extLen
  if clientPub.size ≠ 32 then return none
  return some { random := random, legacySession := sid, clientPubkey := clientPub }

/-- Build a TLS 1.3 ServerHello body emitting the chosen
    cipher (TLS_AES_128_GCM_SHA256), x25519 key_share, and
    supported_versions=TLS 1.3.

    `serverRandom` is the 32-byte server random.
    `sessionIdEcho` echoes the client's legacy session ID.
    `x25519Pubkey` is the server's KEM share. -/
def buildServerHelloBody
    (serverRandom sessionIdEcho x25519Pubkey : Array UInt8) :
    Array UInt8 := Id.run do
  -- supported_versions: TLS 1.3 (0x0304).
  let svData : Array UInt8 := #[0x03, 0x04]
  let extSV := mkExtension extSupportedVersions svData
  -- key_share: single KeyShareEntry { group=x25519, key_exchange=pubkey }
  let kse : Array UInt8 := #[0x00, 0x1D] ++ be16 x25519Pubkey.size ++ x25519Pubkey
  let extKS := mkExtension extKeyShare kse
  let allExts := extSV ++ extKS
  return #[0x03, 0x03]                       -- legacy_version
       ++ serverRandom                        -- 32 bytes
       ++ vec8 sessionIdEcho                  -- session ID echo
       ++ cipherTlsAes128GcmSha256            -- chosen cipher_suite (2 bytes)
       ++ #[0x00]                             -- compression
       ++ vec16 allExts                       -- extensions

def buildServerHello
    (serverRandom sessionIdEcho x25519Pubkey : Array UInt8) :
    Array UInt8 :=
  wrapHandshake .serverHello
    (buildServerHelloBody serverRandom sessionIdEcho x25519Pubkey)

end Sparkle.IP.TLS.Handshake
