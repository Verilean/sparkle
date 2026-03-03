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

def allTests : IO LSpec.TestSeq := do
  IO.println "--- CAVLC Decode Tests ---"
  let t1 ← testZeroRoundtrip
  let t2 ← testDecodeBasic
  return LSpec.group "CAVLC Decode" (t1 ++ t2)

end Sparkle.Tests.Video.CAVLCDecodeTest
