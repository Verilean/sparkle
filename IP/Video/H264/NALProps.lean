/-
  NAL Formal Properties

  Properties of H.264 NAL unit packing/parsing:
  - Roundtrip: parse(pack(payload)) = payload
  - Empty payload roundtrip
  - Emulation prevention roundtrip

  Pattern follows QueueProps.lean.
-/

import IP.Video.H264.NAL

namespace Sparkle.IP.Video.H264.NALProps

open Sparkle.IP.Video.H264.NAL

-- ============================================================================
-- Roundtrip proofs (verified on concrete inputs via native_decide)
-- ============================================================================

/-- Empty payload roundtrip. -/
theorem nal_roundtrip_empty :
    nalParsePayload (nalPack [] NAL_SLICE_IDR 3#8) = [] := by
  native_decide

/-- Simple payload roundtrip (no emulation prevention needed). -/
theorem nal_roundtrip_simple :
    nalParsePayload (nalPack [0x01#8, 0x02#8, 0x03#8, 0x04#8] NAL_SLICE_IDR 3#8)
    = [0x01#8, 0x02#8, 0x03#8, 0x04#8] := by
  native_decide

/-- Payload with 0x000001 (emulation prevention needed). -/
theorem nal_roundtrip_emulation :
    nalParsePayload (nalPack [0x00#8, 0x00#8, 0x01#8, 0xFF#8] NAL_SLICE_IDR 3#8)
    = [0x00#8, 0x00#8, 0x01#8, 0xFF#8] := by
  native_decide

/-- Payload with 0x000000 (emulation prevention needed). -/
theorem nal_roundtrip_zero_seq :
    nalParsePayload (nalPack [0x00#8, 0x00#8, 0x00#8, 0xAA#8] NAL_SLICE_IDR 3#8)
    = [0x00#8, 0x00#8, 0x00#8, 0xAA#8] := by
  native_decide

/-- NAL type is preserved through pack/parse. -/
theorem nal_type_preserved :
    let nal := nalPack [0x01#8] NAL_SPS 3#8
    let (nalType, _, _) := nalParse nal
    nalType = NAL_SPS := by
  native_decide

end Sparkle.IP.Video.H264.NALProps
