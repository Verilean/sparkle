/-
  H.264 CAVLC Decoder — Pure Lean Implementation

  Decodes a CAVLC-encoded bitstream back to 16 quantized coefficients.
  This is the inverse of the CAVLC encoder in CAVLC.lean.

  Parsing stages:
  1. coeff_token → (totalCoeff, trailingOnes)
  2. trailing_ones sign flags
  3. Level values
  4. total_zeros
  5. run_before values
  6. Coefficient reconstruction in zig-zag order

  Reference: ITU-T H.264 Section 9.2.1
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.CAVLC

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Sparkle.IP.Video.H264.CAVLCDecode

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Video.H264.CAVLC

-- ============================================================================
-- Bitstream reader utility
-- ============================================================================

/-- Bitstream state: buffer and current bit position -/
structure BitstreamReader where
  buffer : BitVec 32
  pos    : Nat
  deriving Repr

/-- Read n bits from the bitstream (MSB-first), advance position -/
def BitstreamReader.readBits (r : BitstreamReader) (n : Nat) : BitVec 32 × BitstreamReader :=
  if n == 0 then (0#32, r)
  else
    let shifted := r.buffer >>> (32 - r.pos - n)
    let mask := (1 <<< n) - 1
    let bits := shifted &&& BitVec.ofNat 32 mask
    (bits, { r with pos := r.pos + n })

/-- Peek at the next bit without advancing -/
def BitstreamReader.peekBit (r : BitstreamReader) : Bool :=
  let shifted := r.buffer >>> (31 - r.pos)
  (shifted &&& 1#32) != 0#32

-- ============================================================================
-- VLC decode tables (reverse lookup from encoder tables)
-- ============================================================================

/-- Decode coeff_token for 0 ≤ nC < 2.
    Input: bitstream reader.
    Output: (totalCoeff, trailingOnes, reader) -/
def decodeCoeffToken (r : BitstreamReader) : Nat × Nat × BitstreamReader := Id.run do
  -- Try each (tc, t1) entry in order of code length
  -- We decode by trying prefix matches from shortest to longest
  let mut reader := r

  -- 1-bit codes
  let (b1, r1) := reader.readBits 1
  if b1 == 1#32 then  -- TC=0, T1=0 (code=1, len=1)
    return (0, 0, r1)

  -- 2-bit codes
  let (b2, r2) := r1.readBits 1
  let code2 := b1.toNat * 2 + b2.toNat
  if code2 == 1 then  -- TC=1, T1=1 (code=01, len=2)
    return (1, 1, r2)

  -- 3-bit codes
  let (b3, r3) := r2.readBits 1
  let code3 := code2 * 2 + b3.toNat
  if code3 == 1 then  -- TC=2, T1=2 (code=001, len=3)
    return (2, 2, r3)

  -- 5-bit codes
  let (next2, r5) := r3.readBits 2
  let code5 := code3 * 4 + next2.toNat
  match code5 with
  | 3 => return (3, 3, r5)  -- 00011
  | 2 => return (3, 2, r5)  -- 00010
  | _ => pure ()

  -- 6-bit codes
  let (b6, r6) := r5.readBits 1
  let code6 := code5 * 2 + b6.toNat
  match code6 with
  | 5 => return (1, 0, r6)  -- 000101
  | 4 => return (2, 1, r6)  -- 000100
  | 7 => return (4, 3, r6)  -- 000111
  | _ => pure ()

  -- For simplicity in this baseline implementation, handle remaining codes
  -- with a fallback. Full decoder would continue with 7-16 bit codes.
  -- Return (0,0) as fallback with position advanced
  return (0, 0, r6)

/-- Decode total_zeros for given totalCoeff.
    Simplified: handles common cases for TC=1-6. -/
def decodeTotalZeros (tc : Nat) (r : BitstreamReader) : Nat × BitstreamReader := Id.run do
  if tc >= 16 then return (0, r)

  -- Read up to 9 bits and match against table
  -- Simplified: read 3-4 bits and decode
  match tc with
  | 1 =>
    let (b1, r1) := r.readBits 1
    if b1 == 1#32 then return (0, r1)
    let (b2, r2) := r1.readBits 2
    match b2.toNat with
    | 3 => return (1, r2)
    | 2 => return (2, r2)
    | _ =>
      let (b3, r3) := r2.readBits 1
      match (b2.toNat * 2 + b3.toNat) with
      | 3 => return (3, r3)
      | 2 => return (4, r3)
      | _ => return (0, r3)
  | 2 =>
    let (b3, r3) := r.readBits 3
    match b3.toNat with
    | 7 => return (0, r3)
    | 6 => return (1, r3)
    | 5 => return (2, r3)
    | 4 => return (3, r3)
    | 3 => return (4, r3)
    | _ =>
      let (b4, r4) := r3.readBits 1
      match (b3.toNat * 2 + b4.toNat) with
      | 5 => return (5, r4)
      | 4 => return (6, r4)
      | 3 => return (7, r4)
      | 2 => return (8, r4)
      | _ => return (0, r4)
  | 3 =>
    let (b3, r3) := r.readBits 3
    match b3.toNat with
    | 7 => return (1, r3)
    | 6 => return (2, r3)
    | 5 => return (3, r3)
    | 4 => return (4, r3)
    | 3 => return (5, r3)
    | _ =>
      let (b4, r4) := r3.readBits 1
      match (b3.toNat * 2 + b4.toNat) with
      | 5 => return (0, r4)
      | 4 => return (6, r4)
      | 3 => return (7, r4)
      | 2 => return (8, r4)
      | _ => return (0, r4)
  | _ => return (0, r)  -- simplified

/-- Decode run_before value for given zerosLeft. -/
def decodeRunBefore (zerosLeft : Nat) (r : BitstreamReader) : Nat × BitstreamReader := Id.run do
  if zerosLeft == 0 then return (0, r)
  match zerosLeft with
  | 1 =>
    let (b1, r1) := r.readBits 1
    return (if b1 == 1#32 then 0 else 1, r1)
  | 2 =>
    let (b1, r1) := r.readBits 1
    if b1 == 1#32 then return (0, r1)
    let (b2, r2) := r1.readBits 1
    return (if b2 == 1#32 then 1 else 2, r2)
  | 3 =>
    let (b2, r2) := r.readBits 2
    match b2.toNat with
    | 3 => return (0, r2)
    | 2 => return (1, r2)
    | 1 => return (2, r2)
    | _ => return (3, r2)
  | _ =>
    -- For zerosLeft >= 4, use 2-3 bit codes
    let (b2, r2) := r.readBits 2
    match b2.toNat with
    | 3 => return (0, r2)
    | 2 => return (1, r2)
    | _ =>
      let (b3, r3) := r2.readBits 1
      let code3 := b2.toNat * 2 + b3.toNat
      match code3 with
      | 1 => return (2, r3)
      | 3 => return (3, r3)
      | 2 => return (4, r3)
      | _ => return (0, r3)

-- ============================================================================
-- Level decoding
-- ============================================================================

/-- Decode a single level value from the bitstream.
    Returns (level, updated reader, updated suffixLength) -/
def decodeLevel (r : BitstreamReader) (suffixLen : Nat) (isFirst : Bool) (t1 : Nat)
    : Int × BitstreamReader × Nat := Id.run do
  -- Count leading zeros for prefix
  let mut reader := r
  let mut pfxLen := 0
  let mut maxPrefix := 16  -- safety limit
  while maxPrefix > 0 do
    if reader.peekBit then
      let (_, r') := reader.readBits 1  -- consume the 1-bit
      reader := r'
      maxPrefix := 0  -- break
    else
      let (_, r') := reader.readBits 1  -- consume the 0-bit
      reader := r'
      pfxLen := pfxLen + 1
      maxPrefix := maxPrefix - 1

  -- Determine suffix size
  let suffixSize :=
    if suffixLen == 0 then
      if pfxLen < 14 then 0 else if pfxLen < 15 then 4 else 12
    else
      if pfxLen >= 15 then 12 else suffixLen

  -- Read suffix
  let (sfxBits, reader') := reader.readBits suffixSize
  reader := reader'

  -- Reconstruct levelCode
  let levelCode :=
    if suffixLen == 0 then
      if pfxLen < 14 then pfxLen
      else if pfxLen < 15 then 14 + sfxBits.toNat
      else 15 + sfxBits.toNat
    else
      let base := pfxLen * (Nat.shiftLeft 1 suffixLen) + sfxBits.toNat
      base

  -- Adjust for first coefficient after trailing ones
  let levelCode' := if isFirst && t1 < 3 then levelCode + 2 else levelCode

  -- Convert levelCode to signed level
  let level : Int := if levelCode' % 2 == 0 then
    Int.ofNat (levelCode' / 2 + 1)
  else
    -Int.ofNat (levelCode' / 2 + 1)

  -- Update suffix length
  let absLevel := level.natAbs
  let nextSuffixLen :=
    if suffixLen == 0 then 1
    else if absLevel > 3 * (Nat.shiftLeft 1 (suffixLen - 1)) && suffixLen < 6 then suffixLen + 1
    else suffixLen

  return (level, reader, nextSuffixLen)

-- ============================================================================
-- Full CAVLC decoder (pure function)
-- ============================================================================

/-- Decode CAVLC bitstream to 16 quantized coefficients (zig-zag order).
    Input: 32-bit bitstream buffer, bit length.
    Output: 16 coefficients in zig-zag scan order. -/
def cavlcDecode (buffer : BitVec 32) (bitLen : Nat) : Array Int := Id.run do
  let mut reader : BitstreamReader := ⟨buffer, 0⟩

  -- 1. Decode coeff_token
  let (totalCoeff, trailingOnes, r1) := decodeCoeffToken reader
  reader := r1

  if totalCoeff == 0 then
    return Array.replicate 16 (0 : Int)

  -- 2. Decode trailing ones signs
  let mut coeffs : Array Int := #[]
  for _ in [:trailingOnes] do
    let (signBit, r') := reader.readBits 1
    reader := r'
    coeffs := coeffs.push (if signBit == 1#32 then -1 else 1)

  -- 3. Decode remaining levels
  let numLevels := totalCoeff - trailingOnes
  let mut suffixLen := if totalCoeff > 10 && trailingOnes < 3 then 1 else 0
  for i in [:numLevels] do
    let (level, r', nextSL) := decodeLevel reader suffixLen (i == 0) trailingOnes
    reader := r'
    suffixLen := nextSL
    coeffs := coeffs.push level

  -- 4. Decode total_zeros
  let mut totalZeros := 0
  if totalCoeff < 16 then
    let (tz, r') := decodeTotalZeros totalCoeff reader
    reader := r'
    totalZeros := tz

  -- 5. Decode run_before
  let mut runs : Array Nat := #[]
  let mut zerosLeft := totalZeros
  for i in [:totalCoeff - 1] do
    if zerosLeft > 0 then
      let (rb, r') := decodeRunBefore zerosLeft reader
      reader := r'
      runs := runs.push rb
      zerosLeft := zerosLeft - rb
    else
      runs := runs.push 0
  -- Last coefficient gets remaining zeros
  runs := runs.push zerosLeft

  -- 6. Reconstruct coefficients in zig-zag order
  -- coeffs are in reverse scan order: [T1_last, ..., T1_first, level_1, ..., level_n]
  -- runs[i] gives the number of zeros before coeffs[i]
  let mut result := Array.replicate 16 (0 : Int)
  let mut scanPos := totalCoeff + totalZeros - 1  -- start from the last position
  for i in [:coeffs.size] do
    if h : i < coeffs.size then
      if scanPos < 16 then
        result := result.set! scanPos coeffs[i]
      let runBefore := if h2 : i < runs.size then runs[i] else 0
      if scanPos >= runBefore + 1 then
        scanPos := scanPos - runBefore - 1
      else
        scanPos := 0

  -- Suppress unused variable warning
  let _ := bitLen

  return result

/-- Inverse zig-zag: convert from zig-zag order back to raster order -/
def inverseZigzag (zigzag : Array Int) : Array Int :=
  let order := #[0, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15]
  order.map fun i => if h : i < zigzag.size then zigzag[i] else 0

-- ============================================================================
-- Verification
-- ============================================================================

#eval do
  -- Encode test block
  let rasterCoeffs : Array Int := #[0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let (bitstream, bitLen) := cavlcEncodeFull rasterCoeffs
  IO.println s!"Encoded: 0x{String.ofList (Nat.toDigits 16 bitstream.toNat)} ({bitLen} bits)"

  -- Decode
  let decoded := cavlcDecode bitstream bitLen
  IO.println s!"Decoded (zig-zag): {decoded}"

  -- Expected zig-zag scanned: [0, 3, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  -- (position 0=DC, 1=pos1, 2=pos4(raster), 3=pos8(raster)→zigzag3=raster2, etc.)

end Sparkle.IP.Video.H264.CAVLCDecode
