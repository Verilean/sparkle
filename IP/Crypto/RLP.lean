/-
  IP.Crypto.RLP — Recursive Length Prefix encoding.

  RLP is Ethereum's canonical serialization format.  It is the
  on-wire shape of every transaction, every block header, every
  trie node, and the input to every keccak-of-tx hash.  Wallets
  that sign and broadcast EIP-1559 transactions must encode the
  signing payload (and the broadcast envelope) via RLP — so
  Sparkle's eth-wallet IP starts here.

  Spec (Yellow Paper appendix B):

    * A byte string s is encoded as:
        - if |s| = 1 and s[0] < 0x80:  s              (single low byte unchanged)
        - if |s| ≤ 55:                 [0x80 + |s|] ++ s
        - else:                        [0xb7 + |lenBytes|] ++ lenBytes ++ s
                                       (lenBytes = big-endian length)
    * A list of already-RLP-encoded items i is encoded as:
        - if payload length ≤ 55:      [0xc0 + len] ++ concat(items)
        - else:                        [0xf7 + |lenBytes|] ++ lenBytes ++ concat(items)

  This file implements only the encoder.  A decoder follows
  when (and if) we need to verify EIP-712 round-trip; the
  signer path only needs the encoder.
-/

namespace Sparkle.IP.Crypto.RLP

/-- RLP source items.  `bytes` is a raw byte string; `list` is
    a heterogeneous list of items (lists nest arbitrarily). -/
inductive Item where
  | bytes (b : Array UInt8)
  | list  (items : List Item)
  deriving Inhabited

/-- Big-endian byte encoding of a Nat, no leading zeros. -/
def beBytes (n : Nat) : Array UInt8 := Id.run do
  if n == 0 then return #[]
  let mut out : Array UInt8 := #[]
  let mut x := n
  while x > 0 do
    out := out.push (UInt8.ofNat (x &&& 0xFF))
    x := x >>> 8
  return out.reverse

/-- Encode a length-prefix triplet used by both the byte-string
    and list encoders.  `offsetShort` = 0x80 for bytes, 0xc0
    for lists; `offsetLong` is offset + 55. -/
@[inline] def encodeLength (len : Nat) (offsetShort : UInt8) : Array UInt8 :=
  if len < 56 then
    #[UInt8.ofNat (offsetShort.toNat + len)]
  else
    let lenBytes := beBytes len
    #[UInt8.ofNat (offsetShort.toNat + 55 + lenBytes.size)] ++ lenBytes

/-- RLP-encode a single Item.  Recursive — `Item.list` recurses
    into each child and concatenates.  Lean termination accepts
    this because `Item` is structurally recursive. -/
partial def encode : Item → Array UInt8
  | .bytes b =>
    if b.size == 1 && (b.getD 0 0).toNat < 0x80 then
      b
    else
      encodeLength b.size 0x80 ++ b
  | .list items =>
    let encoded := items.foldl (fun acc i => acc ++ encode i) (#[] : Array UInt8)
    encodeLength encoded.size 0xc0 ++ encoded

/-- Convenience: RLP-encode a single byte string. -/
@[inline] def encodeBytes (b : Array UInt8) : Array UInt8 := encode (.bytes b)

/-- Convenience: RLP-encode a list of byte strings (the common
    transaction-field shape: each tx field is either an integer
    or an address, both expressed as canonical big-endian
    bytes without leading zeros for integers). -/
@[inline] def encodeList (items : List (Array UInt8)) : Array UInt8 :=
  encode (.list (items.map .bytes))

/-- Encode a Nat as the canonical big-endian byte string with
    no leading zeros, then RLP-encode.  This is the shape every
    integer transaction field uses (nonce, gas, value, chainId,
    etc.) per Yellow Paper §4.3. -/
@[inline] def encodeNat (n : Nat) : Array UInt8 :=
  encodeBytes (beBytes n)

end Sparkle.IP.Crypto.RLP
