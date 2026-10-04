/-
  IP.Crypto.Bip32 — BIP-32 hierarchical deterministic (HD)
  wallet key derivation.

  BIP-32 takes the 64-byte seed from BIP-39 and builds a tree
  of (privKey, chainCode) pairs, addressable by a derivation
  path like `m/44'/60'/0'/0/0` (which is the Ethereum default
  path: BIP-44 / coin-type 60 / account 0 / external chain /
  index 0).

  The two derivation primitives:

    * Non-hardened CKDpriv(parent, i) for 0 ≤ i < 2^31:
        I = HMAC-SHA-512(parent.chainCode,
                         serP(parent.publicKey) || ser32(i))
        childPriv  = (parent.priv + I_L) mod n
        childChain = I_R

    * Hardened CKDpriv(parent, i) for i ≥ 2^31:
        I = HMAC-SHA-512(parent.chainCode,
                         0x00 || ser256(parent.priv) || ser32(i))
        childPriv  = (parent.priv + I_L) mod n
        childChain = I_R

  Hardened derivation breaks the parent.pubkey → child.priv
  chain (you need parent.priv to derive a hardened child), so
  it's the standard for account-level boundaries.  The
  conventional "path apostrophe" (e.g. `60'`) means
  index + 2^31.

  Master key derivation uses HMAC-SHA-512 with the literal
  ASCII key "Bitcoin seed" — yes, even for Ethereum wallets
  (Ethereum uses BIP-32 unchanged and only differs in the
  coin-type purpose number 60 vs Bitcoin's 0).
-/

import IP.Crypto.Codec.Bip39
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.Proof.Secp256k1Point

namespace Sparkle.IP.Crypto.Bip32

open Sparkle.IP.Crypto.Bip39 (hmacSha512)
open Sparkle.IP.Crypto.Secp256k1ECDSA (n derivePublicKey)
open Sparkle.IP.Crypto.Secp256k1Point (Point)

/-! ### Extended key shape.  The "extended" part is the chain
    code that lets the holder derive further children. -/

structure ExtendedPrivKey where
  privKey   : Nat
  chainCode : Array UInt8   -- 32 bytes
  deriving Inhabited

/-! ### Serialisations the BIP-32 HMAC input requires. -/

/-- 32-bit big-endian serialise. -/
private def ser32 (i : Nat) : Array UInt8 :=
  #[ UInt8.ofNat ((i >>> 24) &&& 0xFF)
   , UInt8.ofNat ((i >>> 16) &&& 0xFF)
   , UInt8.ofNat ((i >>> 8)  &&& 0xFF)
   , UInt8.ofNat (i          &&& 0xFF) ]

/-- 256-bit big-endian serialise, zero-padded on the left to
    exactly 32 bytes. -/
private def ser256 (k : Nat) : Array UInt8 := Id.run do
  let mut bs : Array UInt8 := #[]
  let mut x := k
  for _ in [:32] do
    bs := bs.push (UInt8.ofNat (x &&& 0xFF))
    x := x >>> 8
  return bs.reverse

/-- SEC1 compressed-form serialise of a secp256k1 point: 33
    bytes total — a 0x02 / 0x03 prefix byte indicating
    y-parity (even / odd) followed by the 32-byte x
    coordinate.  Used as the BIP-32 non-hardened HMAC input. -/
def serP (q : Point) : Array UInt8 :=
  match q with
  | .infinity => Array.replicate 33 0  -- shouldn't happen for valid privkeys
  | .affine x y =>
    let tag : UInt8 := if y % 2 == 0 then 0x02 else 0x03
    #[tag] ++ ser256 x

/-! ### Master key derivation. -/

/-- "Bitcoin seed" — the literal ASCII HMAC key BIP-32 uses to
    derive every wallet's master key, regardless of coin
    family (Ethereum, Cosmos, etc. all reuse this constant). -/
private def bitcoinSeedKey : Array UInt8 :=
  "Bitcoin seed".toUTF8.toList.toArray

/-- Read a 32-byte big-endian slice as a Nat. -/
private def beBytesToNat (bs : Array UInt8) : Nat := Id.run do
  let mut acc : Nat := 0
  for b in bs do
    acc := (acc <<< 8) ||| b.toNat
  return acc

/-- Master key from a 64-byte BIP-39 seed. -/
def masterKey (seed : Array UInt8) : ExtendedPrivKey :=
  let i := hmacSha512 bitcoinSeedKey seed
  let il := i.toList.take 32 |>.toArray
  let ir := i.toList.drop 32 |>.toArray
  { privKey := beBytesToNat il, chainCode := ir }

/-! ### Child key derivation. -/

/-- BIP-32 §"Private parent key → private child key".
    `index` ≥ 2^31 selects the hardened branch.  Returns
    `none` if I_L ≥ curve order n (cryptographically negligible
    probability; BIP-32 prescribes "try the next index"). -/
def ckdPriv (parent : ExtendedPrivKey) (index : Nat) : Option ExtendedPrivKey :=
  let isHardened := index >= (1 <<< 31)
  let msg :=
    if isHardened then
      #[(0 : UInt8)] ++ ser256 parent.privKey ++ ser32 index
    else
      serP (derivePublicKey parent.privKey) ++ ser32 index
  let i := hmacSha512 parent.chainCode msg
  let il := i.toList.take 32 |>.toArray
  let ir := i.toList.drop 32 |>.toArray
  let ilNat := beBytesToNat il
  if ilNat >= n then none
  else
    let child := (parent.privKey + ilNat) % n
    if child == 0 then none
    else some { privKey := child, chainCode := ir }

/-! ### Path derivation. -/

/-- A BIP-32 derivation step.  `.hardened i` corresponds to
    the path notation `i'` (= raw index i + 2^31). -/
inductive Step where
  | normal   (index : Nat) : Step
  | hardened (index : Nat) : Step
  deriving Inhabited

/-- Apply one path step.  Returns `none` if the underlying
    CKDpriv fails. -/
@[inline] def applyStep (parent : ExtendedPrivKey) : Step → Option ExtendedPrivKey
  | .normal i   => ckdPriv parent i
  | .hardened i => ckdPriv parent (i + (1 <<< 31))

/-- Derive an extended private key by following a path of
    steps from the master key.  Returns `none` if any step
    on the path produces an invalid (probability-negligible)
    derivation. -/
def derivePath (master : ExtendedPrivKey) (path : List Step) :
    Option ExtendedPrivKey :=
  path.foldlM applyStep master

/-! ### Ethereum convenience helpers.

    The canonical Ethereum derivation path is
    `m/44'/60'/<account>'/0/<address-index>` per BIP-44
    coin-type 60.  Most wallets pin `account=0, address=0`
    for the first account; this helper packages that path. -/

/-- Standard Ethereum first-account address derivation path
    `m/44'/60'/0'/0/0`. -/
def ethereumPath0 : List Step :=
  [.hardened 44, .hardened 60, .hardened 0, .normal 0, .normal 0]

/-- Derive the first standard Ethereum account's private key
    from a BIP-39 seed: master ← seed; child ← path
    `m/44'/60'/0'/0/0`. -/
def deriveEthereumDefaultKey (seed : Array UInt8) :
    Option ExtendedPrivKey :=
  derivePath (masterKey seed) ethereumPath0

end Sparkle.IP.Crypto.Bip32
