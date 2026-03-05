/-
  H.264 MP4 Encoder — Synthesis Wrapper

  Generates SystemVerilog + CppSim + JIT for the hardware MP4 encoder.

  Usage:
    lake build IP.Video.H264.MP4EncoderSynth
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Video.H264.MP4Encoder

set_option maxRecDepth 8192
set_option maxHeartbeats 25600000

namespace Sparkle.IP.Video.H264.MP4EncoderSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Video.H264.MP4Encoder

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign h264MP4Encoder "IP/Video/H264/gen/mp4_encoder.sv" "IP/Video/H264/gen/mp4_encoder_cppsim.h"

end Sparkle.IP.Video.H264.MP4EncoderSynth
