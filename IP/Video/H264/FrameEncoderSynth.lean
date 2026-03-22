/-
  H.264 Frame Encoder — Synthesis Wrapper

  Generates SystemVerilog + CppSim + JIT for the autonomous frame encoder.

  Usage:
    lake build IP.Video.H264.FrameEncoderSynth
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.FrameEncoder

set_option maxRecDepth 8192
set_option maxHeartbeats 12800000

namespace Sparkle.IP.Video.H264.FrameEncoderSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Video.H264.FrameEncoder

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign h264FrameEncoder ".lake/build/gen/h264/frame_encoder.sv" ".lake/build/gen/h264/frame_encoder_cppsim.h"

end Sparkle.IP.Video.H264.FrameEncoderSynth
