/-
  IP.Crypto.Merkle — binary Merkle tree commitment over an
  array of Goldilocks field elements.

  Hash function: SHA-256 (from `IP.Crypto.SHA256`).  Each
  leaf is the 32-byte SHA-256 of the 8-byte little-endian
  encoding of its Goldilocks value.  Each internal node is
  SHA-256(left ++ right).

  The tree height is fixed at the commit time; if the input
  length isn't a power of 2, we pad with zero-field
  elements.

  Provides:
    * `commit` — Array Nat → 32-byte root
    * `openAt` — Array Nat → index → list of sibling
                  hashes (the authentication path)
    * `verifyOpen` — root × leaf-value × index ×
                     auth-path → Bool

  This is the primitive every STARK / Plonk polynomial
  commitment scheme uses.  Pure-data only; HW engine
  follows in Z.2.b once the SHA-256 HW path lands
  (currently blocked by the L.1.b compiler-side TODOs).
-/

import IP.Crypto.SHA256
import IP.Crypto.Goldilocks

namespace Sparkle.IP.Crypto.Merkle

open Sparkle.IP.Crypto.SHA256 (sha256OfBytes)
open Sparkle.IP.Crypto.Goldilocks (p)

/-- 32-byte hash digest as an Array UInt8. -/
abbrev Digest := Array UInt8

/-- 8-byte little-endian encoding of a Goldilocks element. -/
def encodeLeaf (x : Nat) : Array UInt8 := Id.run do
  let mut bs : Array UInt8 := #[]
  for i in [:8] do
    let b := (x >>> (i * 8)) &&& 0xFF
    bs := bs.push (UInt8.ofNat b)
  return bs

/-- 32 raw bytes from a SHA-256 8×32-bit-word digest. -/
def digestOfWords (words : Array (BitVec 32)) : Digest := Id.run do
  let mut bs : Digest := #[]
  for w in words do
    for i in [:4] do
      let shift := (3 - i) * 8
      bs := bs.push (UInt8.ofNat ((w.toNat >>> shift) &&& 0xFF))
  return bs

/-- Leaf hash = SHA-256(leBytes(x)). -/
def hashLeaf (x : Nat) : Digest :=
  digestOfWords (sha256OfBytes (encodeLeaf x))

/-- Internal node hash = SHA-256(left ++ right). -/
def hashInternal (l r : Digest) : Digest :=
  digestOfWords (sha256OfBytes (l ++ r))

/-- Round a Nat up to the next power of two.  E.g.
    nextPow2 5 = 8, nextPow2 8 = 8, nextPow2 0 = 1. -/
def nextPow2 (n : Nat) : Nat := Id.run do
  if n ≤ 1 then return 1
  let mut k := 1
  while k < n do
    k := k * 2
  return k

/-- Hash one level of the tree: pair up adjacent digests
    and produce the next-level digests. -/
def hashLevel (xs : Array Digest) : Array Digest := Id.run do
  let mut out : Array Digest := #[]
  let mut i := 0
  while i + 1 < xs.size do
    out := out.push (hashInternal (xs.getD i #[]) (xs.getD (i + 1) #[]))
    i := i + 2
  return out

/-- Commit an array of Goldilocks values to a 32-byte
    Merkle root.  Pads to the next power of two with the
    zero field element. -/
def commit (xs : Array Nat) : Digest := Id.run do
  let n := nextPow2 xs.size
  -- Initial leaf digests, padded.
  let mut leaves : Array Digest := #[]
  for i in [:n] do
    leaves := leaves.push (hashLeaf (xs.getD i 0))
  -- Fold up: hash each level until one digest remains.
  let mut level := leaves
  while level.size > 1 do
    level := hashLevel level
  return level.getD 0 #[]

/-- Open an index: return the list of sibling digests at
    each level (root-to-leaf order would be cleaner, but
    leaf-to-root is the standard).

    The verifier processes these in order, combining with
    its running digest. -/
def openAt (xs : Array Nat) (idx : Nat) : Array Digest := Id.run do
  let n := nextPow2 xs.size
  -- Build initial leaf digests.
  let mut level : Array Digest := #[]
  for i in [:n] do
    level := level.push (hashLeaf (xs.getD i 0))
  -- Walk up, recording the sibling at the current index.
  let mut idxCur := idx
  let mut path : Array Digest := #[]
  while level.size > 1 do
    let siblingIdx := idxCur ^^^ 1   -- xor with 1: pair partner
    path := path.push (level.getD siblingIdx #[])
    idxCur := idxCur / 2
    level := hashLevel level
  return path

/-- Verify a Merkle opening.  Returns `true` iff applying
    the auth-path to `leafHash = hashLeaf leafVal` reproduces
    the claimed root. -/
def verifyOpen
    (root : Digest) (leafVal : Nat) (idx : Nat)
    (path : Array Digest) : Bool := Id.run do
  let mut cur := hashLeaf leafVal
  let mut idxCur := idx
  for sib in path do
    if idxCur % 2 = 0 then
      cur := hashInternal cur sib
    else
      cur := hashInternal sib cur
    idxCur := idxCur / 2
  return cur == root

end Sparkle.IP.Crypto.Merkle
