/-
  IP.Crypto.SHA256 — FIPS 180-4 SHA-256.

  This file lands the **pure-data SHA-256 algorithm** in
  Lean, validated against NIST test vectors at sim time.
  The Signal-side hardware engine (iterative 64-cycle
  compressor with a 64×32-bit message-schedule register
  file) follows in Phase L.1.b — but having the pure-data
  reference here gives Ed25519 / secp256k1 / HMAC-SHA256 a
  callable hash to wire into their own sim tests in the
  meantime, and provides the spec the HW engine will be
  cross-checked against.

  Layout (per FIPS 180-4 §6.2):
    * 8 working-state words a..h (each 32 bits)
    * 64 round constants K[t]
    * 64 message-schedule words W[t]: first 16 come from
      the input block (512-bit message block = 16 ×
      32-bit), rest computed via the schedule recurrence.

  Per-round update (t = 0..63):
    T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]
    T2 = Σ₀(a) + Maj(a,b,c)
    (a, b, c, d, e, f, g, h) :=
      (T1 + T2, a, b, c, d + T1, e, f, g)

  Helpers:
    Ch(x,y,z)  = (x ∧ y) ⊕ (¬x ∧ z)
    Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)
    Σ₀(x) = ROTR(x, 2) ⊕ ROTR(x, 13) ⊕ ROTR(x, 22)
    Σ₁(x) = ROTR(x, 6) ⊕ ROTR(x, 11) ⊕ ROTR(x, 25)
    σ₀(x) = ROTR(x, 7) ⊕ ROTR(x, 18) ⊕ SHR(x, 3)
    σ₁(x) = ROTR(x, 17) ⊕ ROTR(x, 19) ⊕ SHR(x, 10)
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Crypto.SHA256

/-! ### Pure-data helpers. -/

/-- 32-bit rotate-right: ROTR(x, n) = (x >>> n) | (x <<< (32-n)). -/
@[inline] def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> (BitVec.ofNat 32 n)) ||| (x <<< (BitVec.ofNat 32 (32 - n)))

@[inline] def shr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  x >>> (BitVec.ofNat 32 n)

@[inline] def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 2) ^^^ (rotr32 x 13) ^^^ (rotr32 x 22)

@[inline] def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 6) ^^^ (rotr32 x 11) ^^^ (rotr32 x 25)

@[inline] def smallSigma0 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 7) ^^^ (rotr32 x 18) ^^^ (shr32 x 3)

@[inline] def smallSigma1 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 17) ^^^ (rotr32 x 19) ^^^ (shr32 x 10)

@[inline] def chFn (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

@[inline] def majFn (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-! ### K table — 64 round constants. -/

def kTable : Array (BitVec 32) := #[
  0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
  0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
  0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
  0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
  0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
  0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
  0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
  0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
  0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
  0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
  0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
  0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
  0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
  0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
  0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
  0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32
]

/-- Initial hash values H0..H7 (FIPS 180-4 §5.3.3). -/
def initH : Array (BitVec 32) := #[
  0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
  0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32
]

/-! ### Pure-data single-block compression. -/

/-- Compute W[t] (t = 0..63) given an array of 16 input
    32-bit words. -/
def expandW (block : Array (BitVec 32)) : Array (BitVec 32) := Id.run do
  let mut w : Array (BitVec 32) := Array.replicate 64 (0#32)
  for i in [:16] do
    w := w.set! i (block.getD i 0#32)
  for i in [16:64] do
    let s0 := smallSigma0 (w.getD (i - 15) 0#32)
    let s1 := smallSigma1 (w.getD (i - 2) 0#32)
    let v := s1 + w.getD (i - 7) 0#32 + s0 + w.getD (i - 16) 0#32
    w := w.set! i v
  return w

/-- Pure-data SHA-256 single-block compression.  Takes
    initial state H (8 words) and a 16-word message block,
    returns the post-compression state. -/
def compressBlock (h : Array (BitVec 32)) (block : Array (BitVec 32)) :
    Array (BitVec 32) := Id.run do
  let w := expandW block
  let mut a := h.getD 0 0#32
  let mut b := h.getD 1 0#32
  let mut c := h.getD 2 0#32
  let mut d := h.getD 3 0#32
  let mut e := h.getD 4 0#32
  let mut f := h.getD 5 0#32
  let mut g := h.getD 6 0#32
  let mut hh := h.getD 7 0#32
  for t in [:64] do
    let t1 := hh + bigSigma1 e + chFn e f g + kTable.getD t 0#32 + w.getD t 0#32
    let t2 := bigSigma0 a + majFn a b c
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0#32 + a, h.getD 1 0#32 + b, h.getD 2 0#32 + c, h.getD 3 0#32 + d,
           h.getD 4 0#32 + e, h.getD 5 0#32 + f, h.getD 6 0#32 + g, h.getD 7 0#32 + hh]

/-- Pure-data SHA-256 of a list of pre-padded message
    blocks.  Each block is a 16-word array.  Padding is
    the caller's responsibility for now (FIPS 180-4 §5.1.1
    — append 1 bit + zeros + 64-bit length). -/
def hashBlocks (blocks : List (Array (BitVec 32))) : Array (BitVec 32) :=
  blocks.foldl compressBlock initH

/-- Pure-data SHA-256 of a byte array.  Performs the
    FIPS 180-4 padding internally. -/
def sha256OfBytes (input : Array UInt8) : Array (BitVec 32) := Id.run do
  -- Append 0x80, then zeros, then 64-bit length (in bits).
  let bitLen : Nat := input.size * 8
  let mut lenBytes : Array UInt8 := #[]
  for i in [:8] do
    let shift := (7 - i) * 8
    let byte := (bitLen >>> shift) &&& 0xFF
    lenBytes := lenBytes.push (UInt8.ofNat byte)
  -- Append 0x80 + as many zero bytes as needed so total
  -- (input + 0x80 + zeros + 8 length-bytes) is a multiple
  -- of 64.
  let mut padded : Array UInt8 := input
  padded := padded.push 0x80
  while padded.size % 64 ≠ 56 do
    padded := padded.push 0x00
  for b in lenBytes do
    padded := padded.push b
  -- Convert padded to 16-word blocks.
  let nBlocks := padded.size / 64
  let mut blocks : List (Array (BitVec 32)) := []
  for blk in [:nBlocks] do
    let mut words : Array (BitVec 32) := #[]
    for i in [:16] do
      let off := blk * 64 + i * 4
      let w0 := (padded.getD off 0).toNat
      let w1 := (padded.getD (off + 1) 0).toNat
      let w2 := (padded.getD (off + 2) 0).toNat
      let w3 := (padded.getD (off + 3) 0).toNat
      let word : Nat := (w0 <<< 24) ||| (w1 <<< 16) ||| (w2 <<< 8) ||| w3
      words := words.push (BitVec.ofNat 32 word)
    blocks := blocks ++ [words]
  return hashBlocks blocks

end Sparkle.IP.Crypto.SHA256
