/-
  Test: CAVLC Decoder
  Verifies CAVLC decode and encode-decode roundtrip.
-/

import LSpec
import IP.Video.H264.CAVLC
import IP.Video.H264.CAVLCDecode

open Sparkle.IP.Video.H264.CAVLC
open Sparkle.IP.Video.H264.CAVLCDecode

namespace Sparkle.Tests.Video.CAVLCDecodeTest

def testZeroRoundtrip : IO LSpec.TestSeq := do
  -- All-zero block should encode to a short code and decode back to zeros
  let zeroCoeffs := Array.replicate 16 (0 : Int)
  let (bs, bl) := cavlcEncodeFull zeroCoeffs
  let decoded := cavlcDecode bs bl

  pure $ LSpec.group "Zero Block Roundtrip" (
    LSpec.test "decode(encode(zeros)) = zeros" (decoded == zeroCoeffs)
  )

def testDecodeBasic : IO LSpec.TestSeq := do
  -- Test the basic decoding structure
  let (bs, bl) := cavlcEncodeFull (Array.replicate 16 (0 : Int))

  IO.println s!"  Zero block: bitstream=0x{String.ofList (Nat.toDigits 16 bs.toNat)} ({bl} bits)"

  let decoded := cavlcDecode bs bl
  IO.println s!"  Decoded: {decoded}"

  pure $ LSpec.group "Basic CAVLC Decode" (
    LSpec.test "zero block bitLen > 0" (bl > 0) ++
    LSpec.test "decoded has 16 elements" (decoded.size == 16)
  )

def testNonZeroRoundtrip : IO LSpec.TestSeq := do
  -- Mixed block with TC=3, T1=2, one non-T1 level
  let coeffs : Array Int := #[0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let (bs, bl) := cavlcEncodeFull coeffs
  let decoded := cavlcDecode bs bl

  IO.println s!"  Non-zero roundtrip: encoded={bl} bits"
  IO.println s!"  Original: {coeffs}"
  IO.println s!"  Decoded:  {decoded}"

  pure $ LSpec.group "Non-Zero Block Roundtrip" (
    LSpec.test "decode(encode(mixed)) = original" (decoded == coeffs)
  )

def testSingleCoeffRoundtrip : IO LSpec.TestSeq := do
  -- DC-only block
  let coeffs : Array Int := #[5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let (bs, bl) := cavlcEncodeFull coeffs
  let decoded := cavlcDecode bs bl

  IO.println s!"  Single coeff roundtrip: encoded={bl} bits"
  IO.println s!"  Original: {coeffs}"
  IO.println s!"  Decoded:  {decoded}"

  pure $ LSpec.group "Single Coeff Roundtrip" (
    LSpec.test "decode(encode(DC-only)) = original" (decoded == coeffs)
  )

def testTrailingOnesRoundtrip : IO LSpec.TestSeq := do
  -- Block with only trailing ±1 values (TC=2, T1=2)
  let coeffs : Array Int := #[-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let (bs, bl) := cavlcEncodeFull coeffs
  let decoded := cavlcDecode bs bl

  IO.println s!"  Trailing ones roundtrip: encoded={bl} bits"
  IO.println s!"  Original: {coeffs}"
  IO.println s!"  Decoded:  {decoded}"

  pure $ LSpec.group "Trailing Ones Roundtrip" (
    LSpec.test "decode(encode(T1-only)) = original" (decoded == coeffs)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- CAVLC Decode Tests ---"
  let t1 ← testZeroRoundtrip
  let t2 ← testDecodeBasic
  let t3 ← testNonZeroRoundtrip
  let t4 ← testSingleCoeffRoundtrip
  let t5 ← testTrailingOnesRoundtrip
  return LSpec.group "CAVLC Decode" (t1 ++ t2 ++ t3 ++ t4 ++ t5)

end Sparkle.Tests.Video.CAVLCDecodeTest
