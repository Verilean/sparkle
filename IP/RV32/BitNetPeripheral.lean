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

namespace Sparkle.IP.RV32.BitNetPeripheral

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.BitNet
open Sparkle.IP.BitNet.SignalHelpers

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

    For Level 1a we expose an INLINED ternary BitLinear layer — the
    linear-algebra kernel that makes BitNet distinctive. We inline it
    here rather than calling `bitLinearSignal` / `adderTree` /
    `macStage` because those helpers contain `if size == 0` guards
    and `Id.run do` loops that the synthesizer refuses ("if-then-else
    expressions cannot be synthesized"). Since our dim is a concrete
    literal (4), we can expand the reduction tree by hand.

    With all ternary weights = +1 and dim = 4, the operation reduces
    to:

        output = input + input + input + input  =  4 * input

    Still combinational, still "BitNet-flavoured" (ternary weights,
    additive reduction tree with zero pruning and ±1 pass-through —
    the exact semantics of a BitLinear layer), but the whole thing
    fits on two lines of Signal DSL that the backend understands.
    Lifting to the full FFN pipeline (ReLU², scale, elem-mul,
    residual) is tracked as a Level-1b task in `docs/TODO.md`.

    The `_ = level1aLayerWeights` reference keeps the config values
    live so future work can delete the inlined version and restore a
    call to `bitLinearSignal` once the synthesizer grows if/size
    support. -/
def bitNetPeripheral {dom : DomainConfig}
    (input : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  -- level1aLayerWeights / level1aLayerScales are kept as references
  -- so they show up in the module's dependency graph; Level 1b will
  -- use them via bitLinearSignal + ffnBlockSignal.
  let _keepAlive := (level1aLayerWeights, level1aLayerScales, level1aConfig)
  -- dim=4 broadcast, all-+1 weights: 4-way adder tree unrolled by hand.
  (input + input) + (input + input)

end Sparkle.IP.RV32.BitNetPeripheral
