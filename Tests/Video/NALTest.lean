/-
  Test: NAL Unit Packing/Parsing
  Verifies NAL roundtrip and emulation prevention.
-/

import LSpec
import IP.Video.H264.NAL

open Sparkle.IP.Video.H264.NAL

namespace Sparkle.Tests.Video.NALTest

def testRoundtrip : IO LSpec.TestSeq := do
  -- Simple payload
  let p1 : List (BitVec 8) := [0x01#8, 0x02#8, 0x03#8, 0x04#8]
  let rt1 := nalParsePayload (nalPack p1 NAL_SLICE_IDR 3#8)

  -- Payload with 0x000001 (needs emulation prevention)
  let p2 : List (BitVec 8) := [0x00#8, 0x00#8, 0x01#8, 0xFF#8]
  let rt2 := nalParsePayload (nalPack p2 NAL_SLICE_IDR 3#8)

  -- Payload with 0x000000
  let p3 : List (BitVec 8) := [0x00#8, 0x00#8, 0x00#8, 0xAA#8]
  let rt3 := nalParsePayload (nalPack p3 NAL_SLICE_IDR 3#8)

  -- Empty payload
  let p4 : List (BitVec 8) := []
  let rt4 := nalParsePayload (nalPack p4 NAL_SPS 3#8)

  pure $ LSpec.group "NAL Roundtrip" (
    LSpec.test "simple payload" (rt1 == p1) ++
    LSpec.test "emulation prevention 0x000001" (rt2 == p2) ++
    LSpec.test "emulation prevention 0x000000" (rt3 == p3) ++
    LSpec.test "empty payload" (rt4 == p4)
  )

def testNALHeader : IO LSpec.TestSeq := do
  -- Verify NAL type extraction
  let nal := nalPack [0x01#8] NAL_SPS 3#8
  let (nalType, nalRefIdc, _) := nalParse nal

  pure $ LSpec.group "NAL Header" (
    LSpec.test "NAL type preserved" (nalType == NAL_SPS) ++
    LSpec.test "NAL ref IDC preserved" (nalRefIdc == 3#8)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- NAL Unit Tests ---"
  let t1 ← testRoundtrip
  let t2 ← testNALHeader
  return LSpec.group "NAL Unit" (t1 ++ t2)

end Sparkle.Tests.Video.NALTest
