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

/-- Check if the bitstream at current position matches a VLC code.
    H.264 VLC codes are prefix-free, so exactly one match exists. -/
def BitstreamReader.matchCode (r : BitstreamReader) (code : BitVec 16) (len : Nat) : Bool :=
  if len == 0 || r.pos + len > 32 then false
  else
    let shifted := r.buffer >>> (32 - r.pos - len)
    let mask := BitVec.ofNat 32 ((1 <<< len) - 1)
    (shifted &&& mask).toNat == code.toNat

-- ============================================================================
-- VLC decode functions (reverse lookup against encoder tables)
-- ============================================================================

/-- Decode coeff_token for 0 ≤ nC < 2.
    Iterates all (tc, t1) entries in the encoder table and matches against
    the bitstream prefix. VLC codes are prefix-free so exactly one matches.
    Input: bitstream reader.
    Output: (totalCoeff, trailingOnes, reader) -/
def decodeCoeffToken (r : BitstreamReader) : Nat × Nat × BitstreamReader := Id.run do
  for tc in List.range 17 do
    let maxT1 := min tc 3
    for t1 in List.range (maxT1 + 1) do
      let (code, len) := coeffTokenLookup tc t1
      if len.toNat > 0 && r.matchCode code len.toNat then
        let (_, r') := r.readBits len.toNat
        return (tc, t1, r')
  return (0, 0, r)

/-- Decode total_zeros for given totalCoeff.
    Iterates all totalZeros values and matches against encoder table. -/
def decodeTotalZeros (tc : Nat) (r : BitstreamReader) : Nat × BitstreamReader := Id.run do
  if tc >= 16 then return (0, r)
  let maxTz := 16 - tc
  for tz in List.range (maxTz + 1) do
    let (code, len) := totalZerosLookup tc tz
    if len.toNat > 0 && r.matchCode code len.toNat then
      let (_, r') := r.readBits len.toNat
      return (tz, r')
  return (0, r)

/-- Decode run_before value for given zerosLeft.
    Iterates runBefore values and matches against encoder table.
    Well-defined 3-bit codes are tried before the 1-bit fallback. -/
def decodeRunBefore (zerosLeft : Nat) (r : BitstreamReader) : Nat × BitstreamReader := Id.run do
  if zerosLeft == 0 then return (0, r)
  for rb in List.range (min zerosLeft 15 + 1) do
    let (code, len) := runBeforeLookup zerosLeft rb
    if len.toNat > 0 && r.matchCode code len.toNat then
      let (_, r') := r.readBits len.toNat
      return (rb, r')
  return (0, r)

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
-- Inverse zig-zag scan
-- ============================================================================

/-- Inverse zig-zag: convert from zig-zag order back to raster order -/
def inverseZigzag (zigzag : Array Int) : Array Int :=
  let order := #[0, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15]
  order.map fun i => if h : i < zigzag.size then zigzag[i] else 0

-- ============================================================================
-- Full CAVLC decoder (pure function)
-- ============================================================================

/-- Decode CAVLC bitstream to 16 quantized coefficients (raster order).
    Input: 32-bit bitstream buffer, bit length.
    Output: 16 coefficients in raster scan order (inverse zig-zag applied). -/
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

  return inverseZigzag result

-- ============================================================================
-- Verification
-- ============================================================================

#eval do
  -- Encode test block
  let rasterCoeffs : Array Int := #[0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let (bitstream, bitLen) := cavlcEncodeFull rasterCoeffs
  IO.println s!"Encoded: 0x{String.ofList (Nat.toDigits 16 bitstream.toNat)} ({bitLen} bits)"

  -- Decode (now returns raster order after inverse zig-zag)
  let decoded := cavlcDecode bitstream bitLen
  IO.println s!"Decoded (raster): {decoded}"
  IO.println s!"Original:         {rasterCoeffs}"
  IO.println s!"Match: {decoded == rasterCoeffs}"

end Sparkle.IP.Video.H264.CAVLCDecode
