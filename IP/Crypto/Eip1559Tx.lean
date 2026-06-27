/-
  IP.Crypto.Eip1559Tx — EIP-1559 (Type 2) transaction signer.

  Composes the existing pure-data primitives (RLP, Keccak-256,
  secp256k1 ECDSA) into a complete EIP-1559 transaction
  signing pipeline:

    1. Pack the user-provided fields into the canonical
       9-tuple shape defined by EIP-1559.
    2. RLP-encode the 9-tuple, prepend `0x02` (TransactionType),
       Keccak-256 to obtain the signing hash `z`.
    3. ECDSA-sign `z` with the user's private key; derive the
       y-parity bit by comparing the recovered R point's
       y-coordinate parity.
    4. RLP-encode the 12-tuple (9 tx fields + yParity + r + s),
       prepend `0x02` — that's the broadcast envelope.

  The unsigned 9-tuple (steps 1+2) is also exposed for
  EIP-712 / off-chain message signing flows that need just
  the signing hash.

  Spec:
    EIP-1559: https://eips.ethereum.org/EIPS/eip-1559
    EIP-2930: https://eips.ethereum.org/EIPS/eip-2930 (accessList)
-/

import IP.Crypto.Keccak256
import IP.Crypto.RLP
import IP.Crypto.Secp256k1ECDSA
import IP.Crypto.Secp256k1Point

namespace Sparkle.IP.Crypto.Eip1559Tx

open Sparkle.IP.Crypto.RLP
open Sparkle.IP.Crypto.Keccak256
open Sparkle.IP.Crypto.Secp256k1ECDSA
open Sparkle.IP.Crypto.Secp256k1Point (Point base mulScalar)

/-- All fields needed to assemble an EIP-1559 transaction.
    Integer fields are kept as `Nat` and converted to
    canonical RLP big-endian bytes on demand.  `to` is a
    20-byte address (empty array means contract creation).
    `accessList` is left as raw RLP-encoded bytes; for the
    common "no access list" case pass `#[]`. -/
structure Tx where
  chainId          : Nat
  nonce            : Nat
  maxPriorityFee   : Nat
  maxFee           : Nat
  gasLimit         : Nat
  to               : Array UInt8     -- 20 bytes, or empty for contract create
  value            : Nat
  data             : Array UInt8
  accessList       : Array UInt8     -- pre-encoded RLP list; #[0xc0] for empty
  deriving Inhabited

/-- The "empty access list" sentinel: a single RLP byte 0xc0
    (= empty list).  Most wallet flows pass this. -/
def emptyAccessList : Array UInt8 := #[0xc0]

/-! ### Signing payload

    The hash that ECDSA actually signs is

      keccak256(0x02 || rlp([chainId, nonce, maxPriorityFee,
                              maxFee, gasLimit, to, value,
                              data, accessList]))

    per EIP-1559.  The leading `0x02` byte is the transaction-
    type discriminator (`TransactionType` in the EIP); it is
    NOT inside the RLP list. -/

def signingPayload (tx : Tx) : Array UInt8 :=
  let inner : List Item :=
    [ .bytes (beBytes tx.chainId)
    , .bytes (beBytes tx.nonce)
    , .bytes (beBytes tx.maxPriorityFee)
    , .bytes (beBytes tx.maxFee)
    , .bytes (beBytes tx.gasLimit)
    , .bytes tx.to
    , .bytes (beBytes tx.value)
    , .bytes tx.data
    ]
  let body := encode (.list inner) ++ tx.accessList.toList.toArray
  -- Re-RLP-encode the body: accessList is already an RLP item
  -- itself, so we splice it as raw bytes inside the outer list.
  -- For correctness we rebuild the outer list with accessList
  -- as a sibling Item; do it explicitly to keep RLP-roundtrip
  -- the gold standard.
  let _ := body  -- discard the intermediate; we use the cleaner form below
  let outer : Item :=
    .list (inner ++ [Item.bytes tx.accessList])
  -- Note: when accessList is "empty" (= #[0xc0]) the encoder
  -- will treat it as the 1-byte string 0xc0, which has the
  -- WRONG RLP shape for an embedded list.  Use the structured
  -- form when accessList is "no entries":
  let outerStruct : Item :=
    if tx.accessList = emptyAccessList then
      .list (inner ++ [Item.list []])
    else
      outer
  #[0x02] ++ encode outerStruct

/-- The Keccak-256 of the signing payload — the digest that
    ECDSA actually signs. -/
def signingHash (tx : Tx) : Array UInt8 :=
  keccak256OfBytes (signingPayload tx)

/-- Read the signing hash as the `Nat` that the ECDSA `sign`
    function expects (big-endian truncated to 256 bits — which
    is exactly the 32 bytes Keccak-256 emits). -/
def signingHashNat (tx : Tx) : Nat := Id.run do
  let bs := signingHash tx
  let mut acc : Nat := 0
  for b in bs do
    acc := (acc <<< 8) ||| b.toNat
  return acc

/-! ### Signing -/

/-- One signed-transaction tuple suitable for broadcast. -/
structure Signed where
  tx       : Tx
  yParity  : Nat   -- 0 or 1
  r        : Nat
  s        : Nat

/-- Sign `tx` with private key `d` and the caller-supplied
    nonce `k`.  Returns `none` if ECDSA produces a degenerate
    signature (r = 0 or s = 0); in production the caller
    re-derives `k` per RFC 6979 and retries until non-
    degenerate, but that loop is deferred to the BIP32 layer
    (#426) where RFC 6979 will land alongside HMAC-SHA512.

    The y-parity bit is recovered from the y-coordinate of
    `k · G` (the point whose x-coordinate became `r`): even
    y → 0, odd y → 1.  Per EIP-1559 §"Signature" this is the
    canonical recovery-id encoding (no `+ 27` legacy offset). -/
def signTx (tx : Tx) (d k : Nat) : Option Signed :=
  let z := signingHashNat tx
  match sign d k z with
  | none => none
  | some (r, s) =>
    -- Recover y-parity from k·G.
    let kg := mulScalar k base
    match kg with
    | .infinity => none
    | .affine _ y1 =>
      let yParity := y1 % 2
      some { tx, yParity, r, s }

/-! ### Broadcast envelope -/

/-- Encode the broadcast-ready signed transaction:

      0x02 || rlp([chainId, nonce, maxPriorityFee, maxFee,
                    gasLimit, to, value, data, accessList,
                    yParity, r, s])

    This is exactly the byte string an Ethereum node accepts
    on `eth_sendRawTransaction`. -/
def encodeSigned (sig : Signed) : Array UInt8 :=
  let tx := sig.tx
  let body : List Item :=
    [ .bytes (beBytes tx.chainId)
    , .bytes (beBytes tx.nonce)
    , .bytes (beBytes tx.maxPriorityFee)
    , .bytes (beBytes tx.maxFee)
    , .bytes (beBytes tx.gasLimit)
    , .bytes tx.to
    , .bytes (beBytes tx.value)
    , .bytes tx.data
    , (if tx.accessList = emptyAccessList then .list [] else .bytes tx.accessList)
    , .bytes (beBytes sig.yParity)
    , .bytes (beBytes sig.r)
    , .bytes (beBytes sig.s)
    ]
  #[0x02] ++ encode (.list body)

/-! ### Address derivation

    An Ethereum address is the low 20 bytes of
    `keccak256(publicKey)` where the public key is the 64-byte
    uncompressed (x ‖ y) form WITHOUT the leading 0x04 SEC1
    prefix.  This is the spec used to derive contract-creation
    addresses and to verify "this signature came from address
    X". -/

/-- Serialize a Nat as exactly `n` big-endian bytes (left-
    padded with zeros if needed).  Used to render public-key
    coordinates as fixed-width 32-byte halves. -/
def beBytesPadded (n : Nat) (width : Nat) : Array UInt8 := Id.run do
  let raw := beBytes n
  if raw.size >= width then return raw
  let mut out : Array UInt8 := Array.replicate (width - raw.size) 0
  out := out ++ raw
  return out

/-- Public-key bytes in the 64-byte "uncompressed without 0x04
    prefix" shape Keccak-256 hashes for the address. -/
def pubkeyBytes (q : Point) : Option (Array UInt8) :=
  match q with
  | .infinity => none
  | .affine x y => some (beBytesPadded x 32 ++ beBytesPadded y 32)

/-- Derive the 20-byte Ethereum address from a private key.
    `none` if the resulting public key is the point at
    infinity (impossible in practice for any 1 ≤ d < n). -/
def addressOfPrivateKey (d : Nat) : Option (Array UInt8) :=
  match pubkeyBytes (derivePublicKey d) with
  | none => none
  | some pk =>
    let hash := keccak256OfBytes pk
    some (hash.toList.drop 12 |>.toArray)

end Sparkle.IP.Crypto.Eip1559Tx
