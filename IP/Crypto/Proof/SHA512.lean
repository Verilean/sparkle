/-
  IP.Crypto.SHA512 — pure-data SHA-512 (FIPS 180-4).

  Same structure as SHA-256 but with 64-bit words, 80
  rounds, and different rotation amounts:
    Σ₀(x) = ROTR(x, 28) ⊕ ROTR(x, 34) ⊕ ROTR(x, 39)
    Σ₁(x) = ROTR(x, 14) ⊕ ROTR(x, 18) ⊕ ROTR(x, 41)
    σ₀(x) = ROTR(x,  1) ⊕ ROTR(x,  8) ⊕ SHR(x, 7)
    σ₁(x) = ROTR(x, 19) ⊕ ROTR(x, 61) ⊕ SHR(x, 6)

  Block size: 1024 bits (= 128 bytes = 16 × 64-bit words).
  Padding: bit-length field is 128-bit (we use the low 64
  for messages up to 2^64 bits).
-/

import Sparkle

namespace Sparkle.IP.Crypto.SHA512

@[inline] def rotr64 (x : BitVec 64) (n : Nat) : BitVec 64 :=
  (x >>> (BitVec.ofNat 64 n)) ||| (x <<< (BitVec.ofNat 64 (64 - n)))

@[inline] def shr64 (x : BitVec 64) (n : Nat) : BitVec 64 :=
  x >>> (BitVec.ofNat 64 n)

@[inline] def bigSigma0 (x : BitVec 64) : BitVec 64 :=
  (rotr64 x 28) ^^^ (rotr64 x 34) ^^^ (rotr64 x 39)

@[inline] def bigSigma1 (x : BitVec 64) : BitVec 64 :=
  (rotr64 x 14) ^^^ (rotr64 x 18) ^^^ (rotr64 x 41)

@[inline] def smallSigma0 (x : BitVec 64) : BitVec 64 :=
  (rotr64 x 1) ^^^ (rotr64 x 8) ^^^ (shr64 x 7)

@[inline] def smallSigma1 (x : BitVec 64) : BitVec 64 :=
  (rotr64 x 19) ^^^ (rotr64 x 61) ^^^ (shr64 x 6)

@[inline] def chFn (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

@[inline] def majFn (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- 80 round constants for SHA-512 (FIPS 180-4 §4.2.3). -/
def kTable : Array (BitVec 64) := #[
  0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
  0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
  0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
  0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
  0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
  0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
  0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
  0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
  0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
  0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
  0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
  0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
  0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
  0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
  0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
  0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
  0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
  0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
  0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
  0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64
]

/-- SHA-512 initial hash values (FIPS 180-4 §5.3.5). -/
def initH : Array (BitVec 64) := #[
  0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
  0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64
]

def expandW (block : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut w : Array (BitVec 64) := Array.replicate 80 (0#64)
  for i in [:16] do
    w := w.set! i (block.getD i 0#64)
  for i in [16:80] do
    let s0 := smallSigma0 (w.getD (i - 15) 0#64)
    let s1 := smallSigma1 (w.getD (i - 2) 0#64)
    let v := s1 + w.getD (i - 7) 0#64 + s0 + w.getD (i - 16) 0#64
    w := w.set! i v
  return w

def compressBlock (h : Array (BitVec 64)) (block : Array (BitVec 64)) :
    Array (BitVec 64) := Id.run do
  let w := expandW block
  let mut a := h.getD 0 0#64
  let mut b := h.getD 1 0#64
  let mut c := h.getD 2 0#64
  let mut d := h.getD 3 0#64
  let mut e := h.getD 4 0#64
  let mut f := h.getD 5 0#64
  let mut g := h.getD 6 0#64
  let mut hh := h.getD 7 0#64
  for t in [:80] do
    let t1 := hh + bigSigma1 e + chFn e f g + kTable.getD t 0#64 + w.getD t 0#64
    let t2 := bigSigma0 a + majFn a b c
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0#64 + a, h.getD 1 0#64 + b, h.getD 2 0#64 + c, h.getD 3 0#64 + d,
           h.getD 4 0#64 + e, h.getD 5 0#64 + f, h.getD 6 0#64 + g, h.getD 7 0#64 + hh]

def hashBlocks (blocks : List (Array (BitVec 64))) : Array (BitVec 64) :=
  blocks.foldl compressBlock initH

/-- Pure-data SHA-512 of a byte array with FIPS padding.
    Pad with 0x80, zeros, and a 128-bit big-endian
    bit-length (we use 64 bits for length and prepend 64
    zero bits — fine for messages < 2^64 bits). -/
def sha512OfBytes (input : Array UInt8) : Array (BitVec 64) := Id.run do
  let bitLen : Nat := input.size * 8
  -- 16-byte big-endian length field: 8 zero bytes + 8 bit-len bytes.
  let mut lenBytes : Array UInt8 := Array.replicate 8 0
  for i in [:8] do
    let shift := (7 - i) * 8
    let byte := (bitLen >>> shift) &&& 0xFF
    lenBytes := lenBytes.push (UInt8.ofNat byte)
  let mut padded : Array UInt8 := input
  padded := padded.push 0x80
  -- Pad with zeros until total size ≡ 112 (mod 128).
  while padded.size % 128 ≠ 112 do
    padded := padded.push 0x00
  for b in lenBytes do
    padded := padded.push b
  let nBlocks := padded.size / 128
  let mut blocks : List (Array (BitVec 64)) := []
  for blk in [:nBlocks] do
    let mut words : Array (BitVec 64) := #[]
    for i in [:16] do
      let off := blk * 128 + i * 8
      let mut w : Nat := 0
      for j in [:8] do
        w := (w <<< 8) ||| (padded.getD (off + j) 0).toNat
      words := words.push (BitVec.ofNat 64 w)
    blocks := blocks ++ [words]
  return hashBlocks blocks

/-- 64-byte (512-bit) digest as a raw byte array. -/
def sha512Bytes (input : Array UInt8) : Array UInt8 := Id.run do
  let words := sha512OfBytes input
  let mut bytes : Array UInt8 := #[]
  for w in words do
    for i in [:8] do
      let shift := (7 - i) * 8
      bytes := bytes.push (UInt8.ofNat ((w.toNat >>> shift) &&& 0xFF))
  return bytes

end Sparkle.IP.Crypto.SHA512
