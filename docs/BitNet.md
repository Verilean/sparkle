# BitNet b1.58 ASIC Inference Engine
## Killer App: BitNet b1.58 ASIC Inference Engine

Sparkle ships with a **complete, formally verified BitNet b1.58 accelerator** — a production-grade ternary-weight neural network inference core targeting ASIC synthesis, written entirely in the Signal DSL. This is the world's first formally verified LLM inference hardware generated from a theorem prover.

### What It Does

Pure Signal DSL functions compose into a **complete BitNet SoC** — simulate directly or synthesize to SystemVerilog:

```lean
import Examples.BitNet.SoC.Top

open Sparkle.Core.Signal
open Sparkle.Examples.BitNet.SoC

-- Build a 2-layer, 4-dimension BitNet SoC as a Signal function
let cfg : SoCConfig := { archMode := .HardwiredUnrolled, nLayers := 2, dim := 4, ffnDim := 4 }
let x : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x10000)  -- 1.0 Q16.16
let result := bitNetSoCSignal cfg layerWeights layerScales x

-- Simulate: evaluate at any timestep
IO.println s!"Output at t=0: {result.atTime 0}"
```

### Dual-Architecture: Choose Your Trade-off

| | HardwiredUnrolled | TimeMultiplexed |
|---|:---:|:---:|
| **Area** | 202,566 cells | **99,020 cells** |
| **Latency** | **1 cycle** (combinational) | 12 cycles (1 per layer) |
| **Throughput** | **Maximum** | 1/12 of HW |
| **Source Lines** | 19,042 | **1,909** |
| **Use Case** | Ultra-low-latency | Area-constrained |

*Yosys 0.62 technology-independent synthesis. See `hw/synth/PPA_Report.md` for full breakdown.*

### 60+ Formally Verified Theorems

Every arithmetic operation in the RTL datapath is backed by machine-checked proofs:

```lean
-- Proves ReLU²(2.0) = 4.0 in Q16.16 fixed-point (checked by Lean kernel)
theorem relu_sq_two :
    reluSquared (BitVec.ofNat 32 0x20000) = BitVec.ofNat 32 0x40000 := by
  native_decide

-- Proves 48-bit × 32-bit scale product fits in 80 bits (no overflow)
theorem scale_prod_fits_80 : (2^47 - 1) * (2^31 - 1) < (2^79 : Nat) := by
  native_decide
```

**Proof categories:** Scale multiply (5), ReLU² (6), Residual add (6), Element multiply (6), Bit-width sufficiency (7), INT8 dot product (15), Attention bit-width (7), Softmax (8), Fixed-point spec (5).

### Architecture Overview

```
x[dim] ──► BitLinear(gate) ──► Scale ──► ReLU² ──┐
        ├─► BitLinear(up)   ──► Scale ────────────┤─► ElemMul ──► ResidualAdd ──► y[dim]
        └─► BitLinear(down) ──► Scale ◄───────────┘                    ↑
                                                                  x[dim] ─┘
```

- **Ternary weights**: {-1, 0, +1} encoded as 2-bit `i2_s` (zero-weight pruning eliminates ~35% of MACs)
- **Fixed-point datapath**: Q16.16 activations, 48-bit accumulators, Q8.24 scale factors
- **Binary adder tree**: Automatic bit-width propagation with configurable pipeline registers
- **LUT-based softmax**: 256-entry exp/reciprocal lookup tables as mux trees
- **Full attention pipeline**: QKV projection, INT8 dot product, softmax, score-V multiply, multi-head

### Golden Value Validation

RTL spec functions are validated against real model data from bitnet.cpp (16 tests):

```
=== RTL Golden Value Validation ===
  [PASS] Q16.16 round-trip       (cosine: 0.9999+)
  [PASS] reluSquared              (cosine: 0.999+)
  [PASS] elemMul                  (cosine: 0.999+)
  [PASS] residualAdd              (cosine: 0.9999+)
  [PASS] fixedPointScale          (cosine: 0.9999+)
  [PASS] quantizeToInt8           (exact match)
  [PASS] FFN forward pass         (cosine: 0.999+)
  [PASS] Attention score pipeline (exact match)
  [PASS] Softmax + weighted V sum
ALL TESTS PASSED
```

---
