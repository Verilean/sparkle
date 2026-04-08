/-
  ConvBnSiLU — Signal DSL

  Fused Convolution + BatchNorm (folded into weights) + SiLU activation.
  This is the fundamental building block of YOLOv8.

  The Conv2DEngine handles the MAC accumulation. After accumulation:
  1. Requantize (multiply-shift) applies the fused BN scale
  2. SiLU activation via ROM LUT

  This module is a controller that sequences:
    Conv2DEngine → Requantize → SiLU → output
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.YOLOv8.Types
import IP.YOLOv8.Primitives.Conv2DEngine
import IP.YOLOv8.Primitives.Activation

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.YOLOv8.Blocks.ConvBnSiLU

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8.Primitives.Conv2DEngine
open Sparkle.IP.YOLOv8.Primitives.Activation

/-- ConvBnSiLU block: Conv2D + BatchNorm (fused) + SiLU.

    The Conv2DEngine already performs requantization internally.
    This block applies SiLU activation to the engine output.

    Inputs:
      - weight4:     INT4 weight from ROM
      - activation8: INT8 activation from buffer
      - scale:       requantization scale (fused with BN)
      - shift:       requantization shift
      - bias32:      INT32 bias (fused with BN)
      - start:       begin new convolution
      - macCount:    number of MAC operations

    Outputs:
      - result: INT8 activated output
      - done:   result valid pulse -/
def convBnSiLU {dom : DomainConfig}
    (weight4 : Signal dom (BitVec 4))
    (activation8 : Signal dom (BitVec 8))
    (scale : Signal dom (BitVec 16))
    (shift : Signal dom (BitVec 5))
    (bias32 : Signal dom (BitVec 32))
    (start : Signal dom Bool)
    (macCount : Signal dom (BitVec 16))
    : Signal dom (BitVec 8 × Bool) :=
  -- Run convolution engine (includes requantization)
  let convOut := conv2DEngine weight4 activation8 scale shift bias32 start macCount
  let convResult := Signal.fst convOut
  let convDone := Signal.snd convOut

  -- Apply SiLU activation
  let activated := siluLut convResult

  -- Output activated result with the same done timing
  bundle2 activated convDone

#synthesizeVerilog convBnSiLU

end Sparkle.IP.YOLOv8.Blocks.ConvBnSiLU
