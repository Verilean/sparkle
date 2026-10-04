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

/-- Internal wires the JIT drivers sample by name (`JIT.resolveWire`).
    Declaring them is what protects them; observability is opt-in
    (see `Optimize.inlineSingleUseWires`). -/
def frameEncoderObservableWires : Array String :=
  #[ "_gen_mainPhase"
   , "_gen_scanIdx"
   , "_gen_cavlcBitPos"
   , "_gen_cavlcBitBuffer"
   ]

#writeDesign h264FrameEncoder ".lake/build/gen/h264/frame_encoder.sv" ".lake/build/gen/h264/frame_encoder_cppsim.h" frameEncoderObservableWires

end Sparkle.IP.Video.H264.FrameEncoderSynth
