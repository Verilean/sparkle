/-
  IP.Crypto.GHASH — pure-data GHASH for AES-GCM
  (NIST SP 800-38D §6.4).

  GHASH operates on 128-bit blocks in GF(2^128) with the
  reduction polynomial p(x) = x^128 + x^7 + x^2 + x + 1.

  NIST bit convention (§6.3): the most-significant bit of
  byte 0 is "bit 0" of the polynomial — i.e. the constant
  representing x^127 has bit 0 of byte 0 set, which as a
  conventional little-endian Nat is 0x80...00 (high bit of
  byte 0 in our `BitVec 128` MSB-first representation).

  The reduction polynomial in this convention is
  R = 0xE1 << 120 = 0xE1000000_00000000_00000000_00000000
  (top byte 0xE1 = bits for x^0 + x^1 + x^2 + x^7 reversed).

  Pure-data reference + NIST GCM KAT vectors in this file.
  HW engine (multi-cycle 128-bit serial mult) follows in T.3.b.
-/

import Sparkle

namespace Sparkle.IP.Crypto.GHASH

/-- The NIST-convention reduction constant: top byte 0xE1,
    rest zero — representing the polynomial reduction term
    x^127 (when shifted left by 1 to model the field's
    leading 1). -/
def R : BitVec 128 := (0xE1#8).zeroExtend 128 <<< 120

/-! ### Right-shift method (NIST §6.3 algorithm 1).

    To multiply X · Y in GF(2^128):
      Z := 0
      V := Y
      for i in 0..127 (bit i = MSB-first):
        if X has bit i set: Z := Z XOR V
        if V's bit 127 (LSB) is 1: V := (V >>> 1) XOR R
        else:                       V := V >>> 1
      return Z

    Note "bit i" here is NIST-bit-i = MSB of byte (i / 8),
    shifted by (i % 8) toward LSB.  In our `BitVec 128` the
    most-significant Nat bit corresponds to NIST-bit-0.
-/

/-- Test NIST-bit `i` (0 ≤ i < 128) of a BitVec.  NIST bit 0
    is the high bit of byte 0 = bit 127 in standard
    little-endian BitVec.toNat indexing. -/
@[inline] def testBitN (x : BitVec 128) (i : Nat) : Bool :=
  -- NIST bit i = standard bit (127 - i)
  ((x.toNat >>> (127 - i)) &&& 1) = 1

/-- GHASH 128-bit multiplication via right-shift.  Pure-Nat
    loop. -/
def gmul (x y : BitVec 128) : BitVec 128 := Id.run do
  let mut z : BitVec 128 := 0
  let mut v : BitVec 128 := y
  for i in [:128] do
    -- If NIST-bit i of x is set, Z ^= V
    if testBitN x i then
      z := z ^^^ v
    -- V := V >>> 1, with conditional R XOR if low bit was 1
    let lsbWasOne := (v.toNat &&& 1) = 1
    v := v >>> 1
    if lsbWasOne then
      v := v ^^^ R
  return z

/-! ### GHASH (NIST §6.4).

    GHASH_H(X) for X = X_1 || X_2 || ... || X_m (each
    128-bit), with hash subkey H:
      Y_0 = 0
      Y_i = (Y_{i-1} XOR X_i) ·_H H
    Return Y_m.

    The full GCM authentication tag is computed from
      GHASH_H(AAD || pad(AAD) || C || pad(C) ||
              len(AAD)_{64} || len(C)_{64})
    — i.e. concatenate associated data, ciphertext, and a
    final length block, padding each variable-length piece
    to a 128-bit boundary with zeros.
-/

/-- Multi-block GHASH: fold a list of 16-byte blocks. -/
def ghashBlocks (h : BitVec 128) (blocks : List (BitVec 128)) : BitVec 128 :=
  blocks.foldl (fun y x => gmul (y ^^^ x) h) 0

/-! ### Byte-array ↔ BitVec helpers. -/

/-- Pack 16 bytes into a `BitVec 128` (NIST convention:
    byte 0 = high byte, byte 15 = low byte). -/
def bytesToBlock (bs : Array UInt8) (start : Nat := 0) : BitVec 128 := Id.run do
  let mut acc : Nat := 0
  for i in [:16] do
    let b := if h : start + i < bs.size then bs[start + i].toNat else 0
    acc := (acc <<< 8) ||| b
  return BitVec.ofNat 128 acc

/-- Unpack a `BitVec 128` into 16 bytes (NIST convention). -/
def blockToBytes (x : BitVec 128) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate 16 0
  let n := x.toNat
  for i in [:16] do
    let shift := (15 - i) * 8
    out := out.set! i (UInt8.ofNat ((n >>> shift) &&& 0xFF))
  return out

/-- Pad a byte array to a multiple of 16 bytes with trailing
    zeros, then split into 128-bit blocks. -/
def bytesToPaddedBlocks (bs : Array UInt8) : List (BitVec 128) := Id.run do
  let n := bs.size
  let nBlocks := (n + 15) / 16
  let mut out : List (BitVec 128) := []
  for i in [:nBlocks] do
    out := out ++ [bytesToBlock bs (i * 16)]
  return out

/-- The GCM length block: 64-bit len(AAD) in bits || 64-bit
    len(C) in bits, MSB-first. -/
def lenBlock (aadBits cBits : Nat) : BitVec 128 :=
  BitVec.ofNat 128 ((aadBits <<< 64) ||| (cBits &&& ((1 <<< 64) - 1)))

/-- Full GHASH per NIST §6.4 over (AAD, ciphertext): pad
    each to a 16-byte boundary with zeros, append the length
    block, fold. -/
def ghashFull (h : BitVec 128) (aad ciphertext : Array UInt8) : BitVec 128 :=
  let aBlocks := bytesToPaddedBlocks aad
  let cBlocks := bytesToPaddedBlocks ciphertext
  let lb := lenBlock (aad.size * 8) (ciphertext.size * 8)
  ghashBlocks h (aBlocks ++ cBlocks ++ [lb])

end Sparkle.IP.Crypto.GHASH
