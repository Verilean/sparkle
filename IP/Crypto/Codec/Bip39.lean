/-
  IP.Crypto.Bip39 — BIP-39 mnemonic → seed derivation.

  BIP-39 specifies how a human-memorable English mnemonic
  phrase is converted into the 64-byte binary seed that BIP-32
  (HD wallets) consumes.  The hardware wallet's bring-up
  flow runs this once per session:

      mnemonic + passphrase  →  PBKDF2-HMAC-SHA512(...)
                              →  64-byte seed
                              →  BIP-32 master key derivation
                              →  secp256k1 private key
                              →  EIP-1559 transaction signer

  This file implements the deterministic
  `mnemonicToSeed : String → String → Array UInt8` half.  The
  mnemonic-VALIDATION half (English wordlist lookup + entropy
  + checksum bit) is intentionally out of scope; callers
  expected to validate before feeding the phrase here, or to
  accept any whitespace-normalised input.

  Spec (BIP-39 §"From mnemonic to seed"):
    SEED = PBKDF2(
             password   = NFKD(mnemonic),
             salt       = "mnemonic" || NFKD(passphrase),
             iterations = 2048,
             keyLen     = 64,
             prf        = HMAC-SHA-512
           )

  NFKD normalisation is the caller's responsibility (the same
  way ECDSA `sign` takes the hash as an already-truncated
  `Nat`).  ASCII mnemonics — which is every reference test
  vector and every wallet's English-default flow — round-trip
  untouched.
-/

import IP.Crypto.Proof.SHA512

namespace Sparkle.IP.Crypto.Bip39

open Sparkle.IP.Crypto.SHA512 (sha512Bytes)

/-! ### HMAC-SHA-512 (RFC 2104). -/

/-- HMAC block size for SHA-512 = 128 bytes (twice SHA-256's
    block size — SHA-512 operates on 1024-bit blocks). -/
def blockSize : Nat := 128

/-- HMAC output size for SHA-512 = 64 bytes. -/
def outSize : Nat := 64

/-- Prepare the HMAC key: if longer than blockSize, hash;
    then pad with zeros to exactly blockSize bytes. -/
def hmacKeyPad (key : Array UInt8) : Array UInt8 := Id.run do
  let k0 :=
    if key.size > blockSize then sha512Bytes key
    else key
  let mut out : Array UInt8 := Array.replicate blockSize 0
  for i in [:k0.size] do
    out := out.set! i (k0.getD i 0)
  return out

/-- HMAC-SHA-512(K, m). -/
def hmacSha512 (key msg : Array UInt8) : Array UInt8 := Id.run do
  let k := hmacKeyPad key
  let mut ipad : Array UInt8 := Array.replicate blockSize 0
  let mut opad : Array UInt8 := Array.replicate blockSize 0
  for i in [:blockSize] do
    ipad := ipad.set! i ((k.getD i 0) ^^^ 0x36)
    opad := opad.set! i ((k.getD i 0) ^^^ 0x5C)
  let inner := sha512Bytes (ipad ++ msg)
  let outer := sha512Bytes (opad ++ inner)
  return outer

/-! ### PBKDF2 (RFC 8018 §5.2) instantiated with HMAC-SHA-512.

    BIP-39 fixes the PRF, iteration count, and output length;
    we still expose the general `pbkdf2HmacSha512` shape
    because future BIP-32 work may reuse it. -/

/-- Inner loop: produce the i-th 64-byte block T(i) by
    repeatedly applying HMAC-SHA-512 with the previous
    output and XOR-accumulating across `iterations`. -/
private def pbkdf2Block
    (password salt : Array UInt8) (iterations blockIdx : Nat) :
    Array UInt8 := Id.run do
  -- U(1) = HMAC(password, salt || INT(i)) where INT(i) is the
  -- 4-byte big-endian encoding of the block index.
  let intBe : Array UInt8 :=
    #[ UInt8.ofNat ((blockIdx >>> 24) &&& 0xFF)
     , UInt8.ofNat ((blockIdx >>> 16) &&& 0xFF)
     , UInt8.ofNat ((blockIdx >>> 8)  &&& 0xFF)
     , UInt8.ofNat (blockIdx          &&& 0xFF) ]
  let mut u := hmacSha512 password (salt ++ intBe)
  let mut t := u
  for _ in [1:iterations] do
    u := hmacSha512 password u
    -- XOR u into t in place.
    let mut t' := t
    for j in [:outSize] do
      t' := t'.set! j ((t.getD j 0) ^^^ (u.getD j 0))
    t := t'
  return t

/-- PBKDF2-HMAC-SHA-512.  `keyLen` ≤ (2^32 - 1) * 64. -/
def pbkdf2HmacSha512
    (password salt : Array UInt8) (iterations keyLen : Nat) :
    Array UInt8 := Id.run do
  let nBlocks := (keyLen + outSize - 1) / outSize
  let mut out : Array UInt8 := #[]
  for i in [1:nBlocks + 1] do
    out := out ++ pbkdf2Block password salt iterations i
  -- Truncate to keyLen bytes.
  return out.toList.take keyLen |>.toArray

/-! ### BIP-39 top-level

    The standard fixes: 2048 iterations, 64-byte output,
    salt prefix "mnemonic". -/

/-- BIP-39 PBKDF2 iteration count. -/
def bip39Iterations : Nat := 2048

/-- BIP-39 seed length in bytes. -/
def seedLen : Nat := 64

/-- Convert a string to its UTF-8 byte representation.  ASCII
    strings — i.e. every BIP-39 English mnemonic — round-trip
    unchanged. -/
private def utf8 (s : String) : Array UInt8 := s.toUTF8.toList.toArray

/-- BIP-39 mnemonic → seed.  `passphrase` is the optional
    "25th word" — pass `""` for the standard flow that just
    uses the mnemonic phrase.

    Caller is responsible for NFKD-normalising non-ASCII
    inputs; for English BIP-39 mnemonics (the universal
    default) the input is already canonical. -/
def mnemonicToSeed (mnemonic passphrase : String) : Array UInt8 :=
  let password := utf8 mnemonic
  let salt := utf8 ("mnemonic" ++ passphrase)
  pbkdf2HmacSha512 password salt bip39Iterations seedLen

end Sparkle.IP.Crypto.Bip39
