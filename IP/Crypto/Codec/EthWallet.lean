/-
  IP.Crypto.EthWallet — pure-data end-to-end signer.

  Composes every eth-wallet primitive built up in #422–#426
  into a single function:

      mnemonic  →  BIP-39 seed (PBKDF2-HMAC-SHA-512, 2048)
                →  BIP-32 master key
                →  BIP-32 derive(m/44'/60'/0'/0/0)
                →  EIP-1559 signing payload + Keccak-256 hash
                →  ECDSA sign(priv, k, hash)
                →  encode signed envelope

  Caller still picks the per-signature nonce `k` (passed in
  rather than RFC 6979-derived — see comment in #426 commit
  about why that follow-up lives in the FSM scope).  The
  ergonomic, "all I need is the mnemonic and the tx fields"
  API is what the wallet's UI consumes.

  This file is the **Tier-A oracle** for the Signal-domain
  signer FSM that follows in a subsequent commit.
-/

import IP.Crypto.Codec.Bip39
import IP.Crypto.Codec.Bip32
import IP.Crypto.Codec.Eip1559Tx

namespace Sparkle.IP.Crypto.EthWallet

open Sparkle.IP.Crypto.Bip39 (mnemonicToSeed)
open Sparkle.IP.Crypto.Bip32 (deriveEthereumDefaultKey ExtendedPrivKey)
open Sparkle.IP.Crypto.Eip1559Tx
  (Tx Signed signTx encodeSigned addressOfPrivateKey)

/-! ### End-to-end signer.

    A success returns `(address, envelope)` — the address is
    surfaced so the wallet UI can confirm "you're about to
    sign from 0xabc..." independently of the user supplying
    it.  The envelope is the broadcast-ready byte string. -/

structure SignedTx where
  address  : Array UInt8     -- 20-byte EVM address (`0x…`)
  envelope : Array UInt8     -- the byte string sent to eth_sendRawTransaction

/-- Sign `tx` starting from a BIP-39 mnemonic (English,
    NFKD-normalised by the caller; ASCII mnemonics — the
    universal default — pass unchanged) and an optional
    BIP-39 passphrase.

    `nonce` is the per-signature ECDSA nonce; production
    callers MUST derive it deterministically (RFC 6979 over
    HMAC-SHA-256 of (privKey, hash)), tracked separately.

    Returns `none` if any cryptographic step fails:
      * BIP-32 derivation hits an `I_L ≥ n` boundary
        (cryptographically negligible)
      * ECDSA produces a degenerate signature with the chosen
        `nonce` (callers retry with a fresh nonce). -/
def signFromMnemonic
    (mnemonic passphrase : String) (tx : Tx) (nonce : Nat) :
    Option SignedTx :=
  let seed := mnemonicToSeed mnemonic passphrase
  match deriveEthereumDefaultKey seed with
  | none => none
  | some k =>
    match signTx tx k.privKey nonce with
    | none => none
    | some signed =>
      match addressOfPrivateKey k.privKey with
      | none => none
      | some addr => some { address := addr, envelope := encodeSigned signed }

end Sparkle.IP.Crypto.EthWallet
