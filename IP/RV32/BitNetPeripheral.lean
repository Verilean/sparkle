/-
  BitNetPeripheral — Level 1a MMIO wrapper for BitNet on picorv32 SoC.

  First-ever integration of the BitNet NN IP as a memory-mapped peripheral
  on the picorv32-based Sparkle SoC. The "Hello World" for CPU ⊕ NN
  cohabitation inside a single synthesizable Sparkle design.

  Interface (combinational, one word in / one word out):

      0x40000000  W   push a single Q16.16 activation into the BitNet input
      0x40000004  R   read the BitNet output for the current input latch
      0x40000008  R   status (always 1 in v1a; reserved for future sequential wrapper)

  Because `bitNetSoCSignal` is combinational and stateless, the result is
  valid the same cycle the input latch is updated. picorv32's multi-cycle
  store→load gap is more than enough for the combinational path to settle,
  so no explicit handshake is needed.

  Configuration: dim=4, 1 FFN layer, all-+1 ternary weights, unit scales.
  This is the smallest meaningful config — big enough to exercise every
  stage of the FFN pipeline (BitLinear → Scale → ReLU² → ElemMul →
  BitLinear → Scale → Residual), small enough that `#synthesizeVerilog`
  elaborates in seconds. Outputs are fully deterministic (captured via
  `#eval` in the integration test).

  Future (Level 1b): wrap in `Signal.loop` with `start`/`done` handshake
  registers so realistic model sizes (dim=2048, 24 layers) become
  representable as multi-cycle FSMs. See `docs/TODO.md` V-SoC.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.SoC.Top

namespace Sparkle.IP.RV32.BitNetPeripheral

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.BitNet
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.SoC

/-- The minimal BitNet SoC configuration for Level-1a integration.
    dim = ffnDim = 4, 1 layer, HardwiredUnrolled. -/
def level1aConfig : SoCConfig := {
  archMode      := .HardwiredUnrolled
  nLayers       := 1
  dim           := 4
  ffnDim        := 4
  baseBitWidth  := 32
  pipelineEvery := 0
}

/-- Identity-ish ternary weights for the single layer: every gate / up /
    down weight is +1. The per-layer output is therefore a deterministic
    but non-trivial function of the broadcast input (BitLinear accumulates
    with +1 weights, then the scale / ReLU² / elem-mul / residual stages
    transform it further). This is the simplest config that still
    exercises the full FFN datapath. -/
def level1aLayerWeights : LayerWeights := {
  gateWeights := Array.replicate 16 1   -- dim * ffnDim = 16
  upWeights   := Array.replicate 16 1
  downWeights := Array.replicate 16 1   -- ffnDim * dim = 16
}

/-- Unit scales in Q8.24 fixed-point (1.0 = 0x01000000). -/
def level1aLayerScales : LayerScales := {
  gateScale := 0x01000000
  upScale   := 0x01000000
  downScale := 0x01000000
}

def level1aWeights : Array LayerWeights := #[level1aLayerWeights]
def level1aScales  : Array LayerScales  := #[level1aLayerScales]

/-- The Level-1a BitNet peripheral as a combinational Signal function.
    One 32-bit activation in → one 32-bit activation out, same cycle.

    Now calls the REAL `hardwiredSoCSignal` (full FFN pipeline:
    BitLinear → Scale → ReLU² → ElemMul → BitLinear → Scale → Residual)
    with dim=4, 1 layer, all-+1 ternary weights, unit scales.

    The underlying helpers (`adderTree`, `macStage`, `ffnBlockSignal`,
    `hardwiredSoCSignal`) have been rewritten to be synthesizable
    (no `Id.run do` / `let mut` / pure `if-size` guards). -/
def bitNetPeripheral {dom : DomainConfig}
    (input : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  hardwiredSoCSignal level1aConfig level1aWeights level1aScales input

end Sparkle.IP.RV32.BitNetPeripheral
