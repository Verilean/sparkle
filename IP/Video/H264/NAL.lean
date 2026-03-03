/-
  H.264 NAL Unit Packing / Parsing

  NAL (Network Abstraction Layer) wraps encoded data with:
  - Start code prefix: 0x000001
  - NAL header: forbidden_zero_bit(1) | nal_ref_idc(2) | nal_unit_type(5)
  - Emulation prevention: insert 0x03 after 0x0000 in payload

  Reference: ITU-T H.264 Section 7.3.1, 7.4.1
-/

import Sparkle

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.Video.H264.NAL

-- ============================================================================
-- NAL unit types (H.264 Table 7-1)
-- ============================================================================

def NAL_SLICE_IDR : BitVec 8 := 5#8
def NAL_SPS       : BitVec 8 := 7#8
def NAL_PPS       : BitVec 8 := 8#8

-- ============================================================================
-- Pure NAL packing (encoder side)
-- ============================================================================

/-- Pack payload into NAL unit with start code and emulation prevention.
    nalRefIdc: 2-bit reference indicator (0-3)
    nalType: 5-bit NAL unit type -/
def nalPack (payload : List (BitVec 8)) (nalType : BitVec 8) (nalRefIdc : BitVec 8)
    : List (BitVec 8) := Id.run do
  let mut result : List (BitVec 8) := []

  -- Start code prefix (0x000001)
  result := result ++ [0x00#8, 0x00#8, 0x01#8]

  -- NAL header: forbidden_zero_bit(0) | nal_ref_idc(2 bits) | nal_unit_type(5 bits)
  let header := (nalRefIdc <<< 5) ||| nalType
  result := result ++ [header]

  -- Payload with emulation prevention
  let mut zeros : Nat := 0
  for byte in payload do
    if zeros >= 2 && byte.toNat <= 3 then
      result := result ++ [0x03#8]  -- emulation prevention byte
      zeros := 0
    result := result ++ [byte]
    if byte == 0x00#8 then zeros := zeros + 1
    else zeros := 0

  return result

-- ============================================================================
-- Pure NAL parsing (decoder side)
-- ============================================================================

/-- Parse NAL unit: extract payload, removing start code and emulation prevention.
    Returns (nalType, nalRefIdc, payload) -/
def nalParse (nalUnit : List (BitVec 8))
    : BitVec 8 × BitVec 8 × List (BitVec 8) := Id.run do
  -- Need at least 4 bytes: start code (3) + header (1)
  if nalUnit.length < 4 then return (0#8, 0#8, [])

  -- Extract NAL header (byte 3)
  let header := nalUnit[3]!
  let nalType := header &&& 0x1F#8
  let nalRefIdc := (header >>> 5) &&& 0x03#8

  -- Remove emulation prevention bytes from payload (starting at byte 4)
  let payloadBytes := nalUnit.drop 4
  let mut payload : List (BitVec 8) := []
  let mut zeros : Nat := 0

  for byte in payloadBytes do
    if zeros >= 2 && byte == 0x03#8 then
      zeros := 0
      -- skip emulation prevention byte; continue to next
    else
      payload := payload ++ [byte]
      if byte == 0x00#8 then zeros := zeros + 1
      else zeros := 0

  return (nalType, nalRefIdc, payload)

/-- Extract just the payload from a NAL unit (convenience wrapper) -/
def nalParsePayload (nalUnit : List (BitVec 8)) : List (BitVec 8) :=
  let (_, _, payload) := nalParse nalUnit
  payload

-- ============================================================================
-- Verification
-- ============================================================================

-- Test 1: Simple payload
#eval do
  let payload : List (BitVec 8) := [0x01#8, 0x02#8, 0x03#8, 0x04#8]
  let packed := nalPack payload NAL_SLICE_IDR 3#8
  let parsed := nalParsePayload packed
  IO.println s!"Packed: {packed.map (fun (b : BitVec 8) => b.toNat)}"
  IO.println s!"Parsed: {parsed.map (fun (b : BitVec 8) => b.toNat)}"
  IO.println s!"Roundtrip: {payload == parsed}"

-- Test 2: Payload with 0x000001 sequence
#eval do
  let payload : List (BitVec 8) := [0x00#8, 0x00#8, 0x01#8, 0xFF#8]
  let packed := nalPack payload NAL_SLICE_IDR 3#8
  let parsed := nalParsePayload packed
  IO.println s!"Packed: {packed.map (fun (b : BitVec 8) => b.toNat)}"
  IO.println s!"Parsed: {parsed.map (fun (b : BitVec 8) => b.toNat)}"
  IO.println s!"Roundtrip: {payload == parsed}"

-- Test 3: Empty payload
#eval do
  let payload : List (BitVec 8) := []
  let packed := nalPack payload NAL_SPS 3#8
  let parsed := nalParsePayload packed
  IO.println s!"Packed: {packed.map (fun (b : BitVec 8) => b.toNat)}"
  IO.println s!"Roundtrip: {payload == parsed}"

end Sparkle.IP.Video.H264.NAL
