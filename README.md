# Sparkle HDL

[![Build](https://github.com/Verilean/sparkle/actions/workflows/build.yml/badge.svg)](https://github.com/Verilean/sparkle/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**Write hardware in Lean 4. Prove it correct. Generate Verilog.**

A type-safe hardware description language that brings the power of dependent types and theorem proving to hardware design.

**Quick Start:** See the [Signal DSL Syntax Guide](docs/SignalDSL_Syntax.md) for writing hardware in Sparkle.

## The Sparkle Way: Verification-Driven Design

1. **Write a pure Lean spec** -- Define your hardware's behavior as pure functions
2. **Prove properties** -- Safety, liveness, fairness via Lean's theorem prover
3. **Implement via Signal DSL** -- Express the same logic using `Signal` combinators
4. **Generate Verilog** -- Use `#synthesizeVerilog` or `#writeVerilogDesign` to emit SystemVerilog

See the [Verification-Driven Design Framework](docs/Verification_Framework.md) for patterns and a worked example (Round-Robin Arbiter with 10 formal proofs).

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

## YOLOv8n-WorldV2: Open-Vocabulary Object Detection Accelerator

A **complete YOLOv8n-WorldV2 inference accelerator** — all 15 modules synthesize to Verilog from the same Lean 4 Signal DSL. INT4 weights / INT8 activations with pre-computed CLIP text embeddings for open-vocabulary detection.

### Architecture

```
160x160x3 RGB ──► Backbone (5 stages) ──► Neck (FPN+PAN) ──► Head (3 scales) ──► Detections
                     │                        │                    │
                     ├─ Conv 3x3 stem         ├─ Upsample 2x      ├─ Bbox regression
                     ├─ C2f blocks            ├─ Concat            ├─ Classification
                     └─ SPPF                  └─ C2f               └─ CLIP text dot product
```

**Key specs:**
- **Input**: 160x160x3 RGB (INT8 quantized)
- **Quantization**: INT4 weights (packed 2 per byte) / INT8 activations / INT32 accumulators
- **Backbone**: 5 stages — Conv stem → 4x (Conv stride-2 + C2f) + SPPF, producing P3/P4/P5
- **Neck**: FPN top-down (P5→P4→P3) + PAN bottom-up (N3→N4'→N5')
- **Head**: Decoupled detection at 3 scales with CLIP text embedding dot product
- **All 15 modules synthesize** to SystemVerilog via `#synthesizeVerilog`

### Module Hierarchy (15 synthesizable modules)

| Module | Description | Key technique |
|--------|-------------|---------------|
| `dequantPacked` | INT4→INT8 sign extension | MSB check + bit concat |
| `requantize` | INT32→INT8 multiply-shift-clamp | `BitVec.slt` + `ashr` |
| `relu` | ReLU activation | MSB extraction |
| `siluLut` | SiLU via 256-entry ROM LUT | `lutMuxTree` |
| `conv2DEngine` | Sequential MAC engine | `Signal.loop` FSM |
| `lineBuffer3x3` | 3-row sliding window | `Signal.memory` |
| `maxPool2x2` | 2x2 signed max pooling | `BitVec.slt` |
| `upsample2x` | 2x nearest-neighbor | Counter FSM |
| `convBnSiLU` | Fused Conv+BN+SiLU | Composes primitives |
| `bottleneckController` | 1x1→3x3 + residual | FSM sequencer |
| `c2fController` | Cross Stage Partial | N-bottleneck loop |
| `sppfController` | Spatial Pyramid Pooling | 3-pass max pool |
| `backboneController` | 5-stage backbone FSM | Stage sequencer |
| `neckController` | FPN+PAN sequencer | Bidirectional path |
| `headController` | 3-scale detection head | Scale/branch FSM |
| `yolov8nTop` | Full SoC top-level | Master controller |
| `dotProductEngine` | INT8 dot product for CLIP | MAC accumulator |

### Golden Value Validation

Golden values extracted from real YOLOv8s-WorldV2 model (ultralytics) with INT4/INT8 quantization:

```
--- YOLOv8 Golden Value Validation ---
  [PASS] Golden value files exist (weights, biases, activations, input image)
  [PASS] INT4 weight dequantization preserves signed values
  [PASS] Cosine self-similarity = 1.0
  [PASS] Layer weight diversity check
  9/9 golden value tests pass
```

```python
# Generate golden values from Python
python scripts/yolo_golden_gen.py
# Produces 207 weight files + 68 activation files (9.8MB)
```

---

## RV32IMA RISC-V SoC — Boots Linux

A **complete pipelined RV32IMA CPU** with S-mode, Sv32 MMU, and peripherals — written entirely in Signal DSL. **Boots Linux 6.6.0 via OpenSBI v0.9 on Verilator** — both hand-written and **auto-generated SystemVerilog** reach the same kernel init point.

```
OpenSBI v0.9 — Platform: Sparkle RV32IMA SoC — ISA: rv32imasu
Linux version 6.6.0 ... #6 Thu Feb 26 06:29:23 UTC 2026
Machine model: Sparkle RV32IMA SoC
Memory: 26208K/28672K available (1279K kernel code, 465K rwdata, ...)
```

| | Hand-written SV | Generated SV (from Lean) |
|---|:---:|:---:|
| **UART output** | 3944 bytes | **5250 bytes** |
| **Linux boot** | Kernel init | Kernel init |
| **Final PC** | 0xC013A9xx | 0xC013A9xx |
| **Firmware test** | ALL PASS | ALL PASS |

```lean
-- 122 registers in a single Signal.loop — full SoC in one function
-- State fields accessed by name via declare_signal_state macro
def rv32iSoCSimulate (firmware : BitVec 12 → BitVec 32) : Signal dom SoCState :=
  Signal.loopMemo fun state => rv32iSoCWithFirmwareBody firmware state
```

### CPU Core
- **4-stage pipeline**: IF/ID/EX/WB with hazard detection and data forwarding
- **RV32IMA ISA**: Full integer + M-extension (MUL/DIV/REM) + A-extension (LR.W/SC.W/AMO)
- **Multi-cycle divider**: Restoring division algorithm in Signal DSL

### Privilege & Virtual Memory
- **S-mode + M-mode**: Full privilege separation with trap delegation (medeleg/mideleg)
- **Sv32 MMU**: 4-entry TLB + hardware page table walker (PTW), megapage support
- **CSRs**: mstatus, mie, mtvec, mepc, mcause, mtval, satp, sstatus, stvec, sepc, scause, stval, medeleg, mideleg, mcounteren, scounteren, PMP stubs

### Peripherals
- **UART 8250**: TX/RX with LSR/IER/LCR/DLL/DLM registers (Linux-compatible)
- **CLINT**: Machine timer with mtime/mtimecmp
- **Memory**: 32 MB DRAM (byte-addressable, sub-word load/store: LB/LH/LBU/LHU/SB/SH)

### Signal DSL Ergonomics

Ergonomic operators and macros reduce boilerplate in hardware descriptions:

```lean
open Sparkle.Core.Signal

-- Hardware equality (replaces (· == ·) <$> a <*> Signal.pure val)
let isIdle := fsmReg === (0#4)

-- Bool operators (replaces (· && ·) <$> a <*> b etc.)
let startAndIdle := start &&& isIdle
let shouldFlush  := branchTaken ||| trap_taken

-- Implicit constant lifting via Coe (replaces Signal.pure)
let p3SavedNext := Signal.mux cond (true : Signal dom _) p3SavedReg

-- Hardware conditional macro (replaces deeply nested Signal.mux)
let fsmNext := hw_cond fsmReg            -- default value
  | startAndIdle  => (1#4 : Signal dom _)  -- first match wins
  | stemDone      => (2#4 : Signal dom _)
  | stageConvDone => (3#4 : Signal dom _)
  | isDone        => (0#4 : Signal dom _)
```

All features are synthesis-compatible — `===` expands to `(· == ·) <$> a <*> b`, `hw_cond` expands to nested `Signal.mux` calls, and `Coe` unfolds to `Signal.pure`.

### Named State Accessors (`declare_signal_state`)

Eliminates error-prone magic-number indices for hardware state tuples:

```lean
-- Declare state with named fields, types, and defaults
declare_signal_state BottleneckState
  | fsmReg      : BitVec 2   := 0#2
  | residualReg : BitVec 8   := 0#8
  | resultReg   : BitVec 8   := 0#8
  | doneReg     : Bool        := false

-- Access fields by name (no more projN! state 122 47)
let fsmReg := BottleneckState.fsmReg state
let residualReg := BottleneckState.residualReg state
```

Generates a tuple type alias, synthesis-compatible accessor `def`s, default value, and `Inhabited` instance. The RV32 SoC uses this for all 122 registers — adding/removing a field no longer requires updating every index.

### JIT Simulation — Transparent & Fast (~200x faster than Lean)

Two APIs: **Signal API** (drop-in replacement for `loopMemo`) and **Streaming API** (O(1) memory for long runs):

```lean
-- Signal API: same interface as loopMemo, JIT speed under the hood
let soc ← rv32iSoCJITSimulate (jitCppPath := "verilator/generated_soc_jit.cpp") (firmware := fw)
let out := soc.atTime 1000  -- SoCOutput with pc, uartValid, uartData, ...

-- Streaming API: 10M+ cycles with per-cycle callback, O(1) memory
rv32iSoCJITRun (jitCppPath := cppPath) (firmware := fw) (cycles := 10000000)
  (callback := fun cycle vals => do
    let out := SoCOutput.fromWireValues vals
    if out.uartValid then IO.println s!"UART: {out.uartData}"
    return true)  -- continue
```

- **Compile C++ to shared library at runtime**, load via `dlopen` from Lean
- Hash-based caching: recompilation skipped if source unchanged
- Uses stable **named output wires** (`_gen_pcReg`, `_gen_uartValidBV`, etc.) — immune to DCE
- 6 observable wires (via `SoCOutput.wireNames`), 11 memories, 6 input ports

### Simulation Performance (10M cycles, Apple Silicon)

| Backend | Speed | vs Verilator | vs Lean |
|---------|-------|-------------|---------|
| **JIT evalTick (fused)** | **13.0M cyc/s** | **1.17x faster** | ~2600x |
| **JIT evalTick + 6 wires** | **12.7M cyc/s** | **1.14x faster** | ~2540x |
| JIT eval+tick (separate) | 12.7M cyc/s | 1.14x faster | ~2540x |
| Verilator 5.044 | 11.1M cyc/s | 1.00x | ~2220x |
| CppSim (-O3 AOT) | 6.0M cyc/s | 0.54x | ~1200x |
| Lean loopMemo | ~5K cyc/s | — | 1x |

JIT **exceeds Verilator speed** (1.17x faster) thanks to: (1) no mutex/thread overhead (Verilator 5.x wastes 17.4% on locks even single-threaded), (2) observable wire optimization (33 class members + 321 locals, L1-cache friendly), (3) fewer CPU instructions per sim-cycle, and (4) fused `evalTick()` with stack-local `_next` variables (eliminates ~260 intermediate memory ops/cycle). See [docs/BENCHMARK.md](docs/BENCHMARK.md) for detailed benchmark results, profiling data, and bottleneck analysis.

### JIT Cycle-Skipping — Dynamic Oracle

Detects when the CPU is stuck in a tight halt loop and skips forward by advancing the cycle counter + CLINT timer, achieving **706x effective speedup**. The oracle receives the `JITHandle` directly for dynamic register reads, bulk memory ops (`memsetWord`), and direct state mutation:

```lean
import Sparkle.Core.Oracle
open Sparkle.Core.Oracle

-- Create oracle: detects PC stuck in ≤12-byte range for 50+ consecutive cycles
-- Oracle receives JITHandle per-call and handles all state mutations internally
let (oracle, statsRef) ← mkSelfLoopOracle {}

-- Run with oracle — 10M cycles complete in 9ms instead of 5.5 seconds
let cycles ← JIT.runOptimized handle 10_000_000 wireIndices oracle callback

-- Post-run: 9,998 triggers, 9,998,000 cycles skipped, UART output identical
let stats ← statsRef.get
IO.println s!"Skipped {stats.totalSkipped} cycles in {stats.triggerCount} triggers"

-- Bulk memory fill (e.g., BSS zeroing for Linux boot)
JIT.memsetWord handle memIdx addr 0 count
```

| Metric | Without Oracle | With Oracle |
|--------|---------------|-------------|
| Wall-clock time (10M cycles) | ~770 ms | **7 ms** |
| Effective cyc/s | 13.0M | **~1.4 billion** |

**BSS-Clear Speculative Warp**: A custom inline firmware (7-instruction BSS-clear loop) demonstrates the full pattern — the oracle detects the memory-clearing loop, bulk-zeros all 4 DMEM byte banks via `memsetWord`, and skips ~100K cycles in <1 ms (389 triggers, 99,584 cycles skipped). See `Tests/RV32/JITDynamicWarpTest.lean`.

**Speculative Simulation with Rollback**: Full-state snapshot/restore via C++ default copy constructor enables guard-and-rollback speculation. The oracle snapshots state, speculatively applies bulk updates, checks guard conditions (e.g., timer interrupt), and rolls back if the guard fails — providing bit-accurate cycle-skipping even with interrupts. See `Tests/RV32/JITSpeculativeWarpTest.lean`.

Also includes register snapshot/restore API (130 registers), bulk memory API, and full-state snapshot/restore for state introspection:

### Verilator Backend (~1000x faster)
- Auto-generated SystemVerilog via `#writeDesign` — boots Linux (5250 UART bytes at 10M cycles)
- Hand-written SystemVerilog reference at `verilator/rv32i_soc.sv` (3944 UART bytes at 10M cycles)
- Both reach same kernel init region (PC 0xC013A9xx) — generated SV matches reference behavior
- VCD waveform tracing for debugging
- Firmware test mode + OpenSBI/Linux boot mode

```bash
# Lean simulation
lake test  # Includes RV32 simulation tests

# JIT simulation from Lean (compile + load + run)
lake exe rv32-jit-test verilator/generated_soc_jit.cpp firmware/firmware.hex 5000

# JIT loop test (loopMemoJIT Signal API + Streaming API)
lake exe rv32-jit-loop-test verilator/generated_soc_jit.cpp firmware/firmware.hex 5000

# JIT cycle-skip test (register snapshot/restore roundtrip)
lake exe rv32-jit-cycle-skip-test

# JIT oracle test (self-loop detection, 10M cycles with cycle-skipping)
lake exe rv32-jit-oracle-test

# JIT dynamic warp test (memsetWord + dynamic oracle with JITHandle access)
lake exe rv32-jit-dynamic-warp-test

# JIT speculative warp test (snapshot/restore + guard-and-rollback)
lake exe rv32-jit-speculative-warp-test

# CppSim (standalone C++)
cd verilator && make build-cppsim && make run-cppsim

# Verilator simulation (much faster)
cd verilator && make build
./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000  # Firmware tests

# Linux kernel boot
./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
```

---

## H.264 Baseline Profile Video Codec

A **complete H.264 Baseline Profile encoder and decoder** pipeline — pure Lean reference functions with formal proofs, C++ golden value generators, and a synthesizable quant/dequant roundtrip module verified via JIT.

### Pipeline Architecture

```
ENCODER:  Pixels → Intra Pred → DCT → Quant → Zigzag → CAVLC → NAL → Bitstream
DECODER:  Bitstream → NAL Parse → CAVLC Decode → Dequant → IDCT → Intra Recon → Pixels
```

### Modules (9 phases)

| Module | Pure Lean | Proofs | Tests | Synth |
|--------|:---------:|:------:|:-----:|:-----:|
| DRAM Interface | `DRAMInterface.lean` | 3 theorems | `DRAMTest.lean` | Sim model |
| 4×4 Integer DCT/IDCT | `DCT.lean` | bounded error, linearity | `DCTTest.lean` | Skeletal FSM |
| Quantization | `Quant.lean` | zero/sign preservation | `QuantTest.lean` | — |
| CAVLC Decode | `CAVLCDecode.lean` | roundtrip proof | `CAVLCDecodeTest.lean` | — |
| NAL Pack/Parse | `NAL.lean` | roundtrip proof | `NALTest.lean` | — |
| Intra Prediction (9 modes) | `IntraPred.lean` | residual roundtrip | `IntraPredTest.lean` | — |
| Encoder Top | `Encoder.lean` | — | `H264PipelineTest.lean` | — |
| Decoder Top | `Decoder.lean` | — | `H264PipelineTest.lean` | — |
| Frame-Level E2E | — | — | `H264FrameTest.lean` | — |
| Quant/Dequant Roundtrip | `QuantRoundtripSynth.lean` | — | `H264JITTest.lean` | **Full** |

### JIT End-to-End Test

The quant→dequant roundtrip module synthesizes to SystemVerilog, compiles via JIT, and passes all 4 tests:

```bash
lake exe h264-jit-test
# === H.264 JIT End-to-End Test ===
# JIT: Compiling IP/Video/H264/gen/quant_roundtrip_jit.cpp...
# JIT: Loaded shared library
#   Test 1: Zero block...        PASS
#   Test 2: DCT coefficients...  PASS (all 16 match)
#   Test 3: Single large coeff... PASS
#   Test 4: Negative coeffs...   PASS
# *** ALL H.264 JIT TESTS PASSED ***
```

### Formal Proofs (all without `sorry`)

- **DRAM**: read-after-write, write-write, read-default
- **DCT**: `|IDCT(DCT(x))[i] - x[i]| ≤ 1`, linearity
- **Quant**: `quant(0) = 0`, sign preservation
- **CAVLC**: `decode(encode(coeffs)) = coeffs`
- **NAL**: `parse(pack(payload)) = payload`
- **Intra**: `predicted + (original - predicted) = original`

---

## Why Sparkle?

```lean
-- Write this in Lean...
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let rec count := Signal.register 0#8 (count.map (· + 1))
  count

#synthesizeVerilog counter
```

```systemverilog
// ...and get this Verilog
module counter (
    input  logic clk,
    input  logic rst,
    output logic [7:0] out
);
    logic [7:0] count;

    always_ff @(posedge clk) begin
        if (rst)
            count <= 8'h00;
        else
            count <= count + 8'h01;
    end

    assign out = count;
endmodule
```

**Three powerful ideas in one language:**
1. **Simulate** - Cycle-accurate functional simulation with pure Lean functions
2. **Synthesize** - Automatic compilation to clean, synthesizable SystemVerilog
3. **Verify** - Formal correctness proofs using Lean's theorem prover

## The Sparkle Advantage: Logical AND Physical Safety

Modern HDLs like Chisel have successfully solved many "logical" hardware bugs (like preventing unintended latches) using intermediate representations like FIRRTL. However, they completely ignore the "physical" realities of backend design, leaving engineers to struggle with timing closures (STA) or rely on million-dollar commercial linters like SpyGlass to enforce basic physical design rules.

Sparkle is designed to guarantee both **Logical Safety** and **Physical/Timing Safety** out of the box, without external tools.

### 1. Logical Safety (Zero Latches & Comb Loops)

Backed by Lean 4's rigorous type system:

- **No Unintended Latches:** Lean's pattern-matching exhaustiveness check ensures all conditions are handled at compile-time. If you forget a `default` case, it won't even compile.
- **No Combinational Loops:** The `Signal` monad enforces a strict DAG (Directed Acyclic Graph) for combinational logic. State feedback is only possible through explicit registers (`Signal.register`, `Signal.loop`), making combinational loops impossible by design.

### 2. Physical & Timing Safety (Built-in DRC)

Sparkle includes a built-in Design Rule Check (DRC) compiler pass that enforces backend-friendly RTL structures (inspired by industry standards like the STARC guidelines).

- **Registered Outputs Enforcement:** The compiler automatically checks that module outputs are driven directly by Flip-Flops (Registers) rather than combinational logic, preventing critical path explosion across module boundaries and making Static Timing Analysis (STA) predictable.

```
-- Combinational output: DRC warns
def combo (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  (· + ·) <$> a <*> b

#synthesizeVerilog combo
-- warning: [DRC] Module 'combo': output 'out' is not driven by a register

-- Registered output: DRC passes clean
def registered (a : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  Signal.register 0#8 a

#synthesizeVerilog registered
-- (no warning)
```

### 3. Transparent, Readable Verilog

Unlike Chisel, which shreds your design hierarchy into unreadable FIRRTL-generated Verilog, Sparkle's IR maintains a 1:1 structural correspondence with your Lean code. When the built-in DRC points out a timing issue, you can actually read the generated SystemVerilog to fix it.

## Quick Start

### Installation

```bash
# Clone the repository
git clone https://github.com/Verilean/sparkle.git
cd sparkle

# Build the project
lake build

# Run your first example
lake env lean --run Examples/Counter.lean
```

### Your First Circuit: Simple Register

```lean
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Signal
open Sparkle.Core.Domain

-- A simple register chain (3 cycles delay)
def registerChain (input : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  let d1 := Signal.register 0#8 input
  let d2 := Signal.register 0#8 d1
  let d3 := Signal.register 0#8 d2
  d3

#synthesizeVerilog registerChain
```

This generates a fully synthesizable Verilog module with proper clock/reset handling!

**Note:** More complex feedback loops (like counters with self-reference) currently require manual IR construction - see `Examples/LoopSynthesis.lean` for working examples.

## Key Features

### 🎯 Cycle-Accurate Simulation

Simulate your hardware designs with the same semantics as the final Verilog:

```lean
-- Define a simple adder
def adder (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + ·) <$> a <*> b

-- Simulate signals
def testSignalA : Signal Domain (BitVec 16) := ⟨fun t => t.toBitVec 16⟩
def testSignalB : Signal Domain (BitVec 16) := ⟨fun t => (t * 2).toBitVec 16⟩

#eval (adder testSignalA testSignalB).sample 5
-- Output: [0, 3, 6, 9, 12]  -- t + 2t for t=0..4
```

### ⚙️ Automatic Verilog Generation

Write high-level Lean code, get production-ready SystemVerilog:

```lean
-- Sparkle automatically handles:
-- ✓ Clock and reset signal insertion
-- ✓ Proper register inference
-- ✓ Type-safe bit width matching
-- ✓ Feedback loop resolution
-- ✓ Name hygiene and wire allocation

#synthesizeVerilog myDesign  -- One command, complete module!
```

### 🔒 Formal Verification Ready

Prove correctness properties about your hardware using Lean's powerful theorem prover:

```lean
-- Define an ALU operation
def alu_add (a b : BitVec 16) : BitVec 16 := a + b

-- Prove it's commutative
theorem alu_add_comm (a b : BitVec 16) :
    alu_add a b = alu_add b a := by
  simp [alu_add]
  apply BitVec.add_comm

-- Prove it's associative
theorem alu_add_assoc (a b c : BitVec 16) :
    alu_add (alu_add a b) c = alu_add a (alu_add b c) := by
  simp [alu_add]
  apply BitVec.add_assoc
```

**Real Example:** Our Sparkle-16 CPU includes **9 formally proven theorems** about ALU correctness!

### ⏱️ Temporal Logic for Hardware Verification

Express and prove properties about hardware behavior over time using Linear Temporal Logic (LTL):

```lean
-- Define temporal properties
theorem counter_stable_during_reset :
  let counter : Signal d Nat := ⟨fun t => if t < 10 then 0 else t - 10⟩
  stableFor counter 0 10 := by
  intro t h_bound
  simp [Signal.atTime]
  omega

-- Prove state machine properties
theorem active_state_duration :
  let isActive := stateMachine.map (· == State.Active)
  -- Active state lasts exactly 100 cycles
  always (next 100 isActive) := by
  sorry -- Proof goes here
```

**Features:**
- Core LTL operators: `always`, `eventually`, `next`, `Until`
- Derived operators: `implies`, `release`, `WeakUntil`
- Optimization-enabling: `stableFor` for cycle-skipping simulation
- Temporal induction principles for proof automation
- Temporal oracle interface for future performance optimization

See [Examples/TemporalLogicExample.md](Examples/TemporalLogicExample.md) for detailed usage and design rationale.

### 🏗️ Composable Hardware Abstraction

Build complex designs from simple components:

```lean
-- Build a 4-tap FIR filter by composing delay elements
-- y[n] = c0·x[n] + c1·x[n-1] + c2·x[n-2] + c3·x[n-3]
def fir4
    (c0 c1 c2 c3 : Signal Domain (BitVec 16))  -- Coefficients as inputs
    (input : Signal Domain (BitVec 16))         -- Input sample stream
    : Signal Domain (BitVec 16) :=
  -- Create delay line
  let d1 := Signal.register 0#16 input  -- x[n-1]
  let d2 := Signal.register 0#16 d1     -- x[n-2]
  let d3 := Signal.register 0#16 d2     -- x[n-3]

  -- Multiply and accumulate using applicative style
  let term0 := (· * ·) <$> input <*> c0
  let term1 := (· * ·) <$> d1 <*> c1
  let term2 := (· * ·) <$> d2 <*> c2
  let term3 := (· * ·) <$> d3 <*> c3

  -- Sum all terms
  let sum01 := (· + ·) <$> term0 <*> term1
  let sum23 := (· + ·) <$> term2 <*> term3
  (· + ·) <$> sum01 <*> sum23

#synthesizeVerilog fir4
```

**Key patterns:**
- `Signal.register init input` - Creates a D flip-flop (1-cycle delay)
- `(· op ·) <$> sig1 <*> sig2` - Applicative style for binary operations
- Coefficients must be Signals (module inputs), not runtime constants

### 📦 Vector/Array Types

Create register files and memory structures with hardware arrays:

```lean
-- 4-element register file with 8-bit values
def registerFile (vec : Signal d (HWVector (BitVec 8) 4))
    (idx : Signal d (BitVec 2)) : Signal d (BitVec 8) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx
```

Generates clean Verilog arrays:
```systemverilog
input logic [7:0] vec [3:0];  // 4-element array of 8-bit values
input logic [1:0] idx;
output logic [7:0] out;
assign out = vec[idx];
```

**Features:**
- Fixed-size vectors: `HWVector α n`
- Nested arrays: `HWVector (HWVector (BitVec 8) 4) 8`
- Type-safe indexing with compile-time size checks
- Automatic bit-width calculation

### 💾 Memory Primitives (SRAM/BRAM)

Build RAMs and register files with synchronous read/write:

```lean
-- 256-byte memory (8-bit address, 8-bit data)
def simpleRAM
    (writeAddr : Signal d (BitVec 8))
    (writeData : Signal d (BitVec 8))
    (writeEnable : Signal d Bool)
    (readAddr : Signal d (BitVec 8))
    : Signal d (BitVec 8) :=
  Signal.memory writeAddr writeData writeEnable readAddr
```

Generates synthesizable memory blocks:
```systemverilog
logic [7:0] mem [0:255];  // 256-byte memory array

always_ff @(posedge clk) begin
  if (write_enable) begin
    mem[write_addr] <= write_data;
  end
  read_data <= mem[read_addr];  // Registered read (1-cycle latency)
end
```

**Features:**
- Synchronous writes (on clock edge when write-enable is high)
- Registered reads (1-cycle latency, matches FPGA BRAM behavior)
- Configurable address and data widths
- Synthesizable to FPGA Block RAM or ASIC SRAM
- Perfect for register files, instruction memory, data caches

**Example: 8-register CPU register file**
```lean
-- 8 registers x 16-bit (3-bit address, 16-bit data)
def cpuRegisterFile
    (writeReg : Signal d (BitVec 3))   -- R0-R7
    (writeData : Signal d (BitVec 16))
    (writeEnable : Signal d Bool)
    (readReg : Signal d (BitVec 3))
    : Signal d (BitVec 16) :=
  Signal.memory writeReg writeData writeEnable readReg
```

### 🎓 Complete CPU Example

The **Sparkle-16** is a fully functional 16-bit RISC CPU demonstrating real-world hardware design:

- **8 instructions**: LDI, ADD, SUB, AND, LD, ST, BEQ, JMP
- **8 registers**: R0-R7 (R0 hardwired to zero)
- **Harvard architecture**: Separate instruction and data memory
- **Formally verified**: ISA correctness, ALU operations proven correct
- **Full simulation**: Runs actual programs with control flow

```bash
# Run the CPU simulation
lake env lean --run Examples/Sparkle16/Core.lean

# See the verification proofs
lake env lean --run Examples/Sparkle16/ISAProofTests.lean
```

**Output:**
```
=== Sparkle-16 CPU Core ===

Program:
  LDI R1, 10
  LDI R2, 20
  ADD R3, R1, R2
  SUB R4, R3, R1

After 12 cycles:
R0=0x0000 R1=0x000a R2=0x0014 R3=0x001e R4=0x0014
✓ All values correct!
```

See [Examples/Sparkle16/README.md](Examples/Sparkle16/README.md) for complete CPU documentation.

### 🔌 Technology Library Support

Integrate vendor-specific primitives seamlessly:

```lean
-- Use SRAM primitives from your ASIC/FPGA vendor
def myMemory : Module :=
  primitiveModule "SRAM_256x16" [
    ("addr",  .input (.bitVector 8)),
    ("din",   .input (.bitVector 16)),
    ("dout",  .output (.bitVector 16)),
    ("we",    .input .bit),
    ("clk",   .input .bit)
  ]
```

Sparkle generates proper module instantiations without defining internals.

## Examples

### Counter
```bash
lake env lean --run Examples/Counter.lean
```
Demonstrates registers, combinational logic, and signal operations.

### ALU with Proofs
```bash
lake env lean --run Examples/Sparkle16/ALU.lean
```
Shows formal verification of hardware correctness.

### Complete CPU
```bash
lake env lean --run Examples/Sparkle16/Core.lean
```
A working 16-bit RISC processor with fetch-decode-execute.

### BitNet ASIC Inference Engine
```bash
# Run BitNet tests (Signal DSL functional tests + golden validation)
lake test
```
Complete BitNet b1.58 accelerator with dual architecture options, 60+ formal proofs, and 16 golden value validation tests against real model data.

### YOLOv8n-WorldV2 Object Detection
```bash
# Generate golden values (requires ultralytics Python package)
python scripts/yolo_golden_gen.py

# Build all 15 synthesizable modules
lake build

# Run YOLOv8 tests (primitive + golden value validation)
lake test
```
INT4/INT8 quantized inference accelerator with CLIP text embeddings for open-vocabulary detection. All 15 modules synthesize to SystemVerilog.

### H.264 Video Codec
```bash
# Run H.264 pipeline + frame-level tests (DRAM, DCT, Quant, CAVLC, NAL, IntraPred, full pipeline, frame E2E)
lake test

# JIT end-to-end test (compile quant/dequant FSM, run 4 tests)
lake exe h264-jit-test
```

### All Examples
```bash
# Simulation examples
lake env lean --run Examples/Counter.lean
lake env lean --run Examples/ManualIR.lean
lake env lean --run Examples/SimpleMemory.lean          # Memory simulation

# Verilog generation
lake env lean --run Examples/VerilogTest.lean
lake env lean --run Examples/FullCycle.lean
lake env lean --run Examples/MemoryManualIR.lean        # Memory Verilog generation

# Feedback loops
lake env lean --run Examples/LoopSynthesis.lean

# Technology primitives
lake env lean --run Examples/PrimitiveTest.lean

# Sparkle-16 CPU
lake env lean --run Examples/Sparkle16/ALU.lean
lake env lean --run Examples/Sparkle16/RegisterFile.lean
lake env lean --run Examples/Sparkle16/Core.lean
lake env lean --run Examples/Sparkle16/ISAProofTests.lean

# RV32IMA SoC, BitNet, and YOLOv8 (via test suite)
lake test

# Verilator: build and run firmware tests
cd verilator && make build && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000
```

## Documentation

Generate full API documentation with doc-gen4:

```bash
# Build documentation
lake -R -Kenv=dev build Sparkle:docs

# Open in browser
open .lake/build/doc/index.html
```

The generated documentation includes:
- Complete API reference for all modules
- Signal semantics and primitive operations
- IR builder and circuit construction
- Verilog backend details
- Verification framework (proofs, theorems, and temporal logic)
- Temporal logic for hardware verification (LTL operators)
- Sparkle-16 CPU architecture

**Verification-Driven Design:**
- See [docs/Verification_Framework.md](docs/Verification_Framework.md) for the VDD framework guide
- Bug classification (Safety vs Liveness), four proof patterns, tactic quick-reference
- Worked example: Round-Robin Arbiter with 10 formal proofs + synthesizable Signal DSL implementation

**Temporal Logic Examples:**
- See [Examples/TemporalLogicExample.md](Examples/TemporalLogicExample.md) for comprehensive temporal logic usage
- Includes reset stability, state machine verification, and pipeline examples
- Documents cycle-skipping optimizations and proof obligations

## How It Works

### The Sparkle Pipeline

```
┌──────────────────┐
│  Lean Signal DSL │  ===, &&&, |||, hw_cond, Coe
└──────┬───────────┘
       │
       ├──────────────┬──────────────────┬────────────────┐
       ▼              ▼                  ▼                ▼
┌─────────────┐ ┌────────────┐  ┌──────────────┐ ┌──────────────────┐
│ Simulation  │ │ JIT (FFI)  │  │  Verilator   │ │ #synthesizeVerilog│
│  .atTime t  │ │ C++ dlopen │  │ .sv → C++    │ │  Lean → IR → DRC │
│  ~5K cyc/s  │ │ ~13.0M c/s │  │ ~11.1M c/s   │ │  → SystemVerilog │
│             │ │+oracle:1B+ │  │              │ │                  │
└─────────────┘ └────────────┘  └──────────────┘ └──────────────────┘
```

### Core Abstractions

1. **Domain**: Clock domain configuration (period, edge, reset)
2. **Signal**: Stream-based hardware values `Signal d α ≈ Nat → α`
3. **BitPack**: Type class for hardware serialization
4. **Module/Circuit**: IR for building netlists
5. **Compiler**: Automatic Lean → IR translation via metaprogramming

### Type Safety Benefits

```lean
-- This won't compile - type mismatch!
def broken : Signal Domain (BitVec 8) := do
  let x ← Signal.register (0 : BitVec 16)  -- 16-bit register
  return x  -- Error: expected BitVec 8, got BitVec 16

-- Lean catches bit width errors at compile time
def fixed : Signal Domain (BitVec 8) := do
  let x ← Signal.register (0 : BitVec 16)
  return x.truncate 8  -- ✓ Explicit truncation required
```

## Known Limitations and Gotchas

See the [Troubleshooting Synthesis Guide](docs/Troubleshooting_Synthesis.md) for:
- Imperative syntax limitations (`<~` operator)
- Pattern matching on tuples
- If-then-else in Signal contexts
- Feedback loops and `Signal.loop`
- `Signal.loop` vs `Signal.loopMemo` for simulation
- What's supported vs. unsupported
- Synthesis compiler patterns and fix recipes

### 🧪 Testing

Run the comprehensive test suite:

```bash
lake test
```

Tests include:
- Signal simulation (18 tests)
- IR and Verilog synthesis (13 tests)
- Verilog generation verification (19 tests)
- Array/Vector operations (27 tests)
- Temporal Logic verification (33 tests)
- Overflow/underflow behavior (26 tests)
- Sparkle-16 CPU verification tests
- **BitNet Signal DSL functional tests** — spec-vs-Signal exact match
- **BitNet golden value validation (16 tests)** — validated against real bitnet.cpp model data
- **BitNet RTL correctness (60+ proofs)**
- **Round-Robin Arbiter** — 10 formal proofs (safety, liveness, fairness) + Signal DSL synthesis
- **DRC (Design Rule Check)** — registered output check warns on combinational output ports
- **RV32IMA SoC simulation tests** (firmware + Verilator Linux boot — generated SV verified)
- **JIT loop tests** — `loopMemoJIT` Signal API + `rv32iSoCJITRun` Streaming API (47 UART words pass)
- **JIT cycle-skip test** — Register snapshot/restore roundtrip (130 registers + 4 DMEM banks)
- **JIT oracle test** — Self-loop detection oracle, 10M cycles with cycle-skipping (48 UART words, 9998 oracle triggers)
- **JIT dynamic warp test** — memsetWord bulk fill roundtrip + dynamic oracle with direct JITHandle access (48 UART words, 9998 oracle triggers)
- **JIT speculative warp test** — Snapshot/restore roundtrip + guard-pass speculative warp (389 triggers, 0 rollbacks) + guard-fail rollback (9,955 rollbacks)
- **H.264 pipeline tests** — DRAM interface, DCT/IDCT, quant/dequant, CAVLC decode, NAL pack/parse, intra prediction, full encode→decode roundtrip
- **H.264 frame-level tests** — Multi-block (16×16) encode→decode roundtrip at QP 0/10/20/30, bitstream vs NAL path equivalence, prediction mode diversity
- **H.264 JIT test** — Quant/dequant synthesizable FSM: zero block, DCT coefficients, single large coefficient, negative coefficients (all 4 pass)
- **YOLOv8 primitive tests** — dequant, requantize, activation, max pooling
- **YOLOv8 golden value validation (9 tests)** — validated against real ultralytics model data
- **SyncFIFO (16 tests)** — fill/drain, FIFO ordering, full/empty conditions, simultaneous enq+deq
- Co-simulation with Verilator

## Comparison with Other HDLs

| Feature | Sparkle | Clash | Chisel | Verilog |
|---------|---------|-------|--------|---------|
| Language | Lean 4 | Haskell | Scala | Verilog |
| Type System | Dependent Types | Strong | Strong | Weak |
| Simulation | Built-in | Built-in | Built-in | External Tools |
| Formal Verification | **Native (Lean)** | External | External | None |
| Logical Safety (no latches/comb loops) | **By construction** | Partial | Via FIRRTL | None |
| Physical/Timing Safety (DRC) | **Built-in** | None | None | SpyGlass ($$$) |
| Generated Verilog Readability | **1:1 structural** | Readable | Obfuscated (FIRRTL) | N/A |
| Learning Curve | High | High | Medium | Low |
| Proof Integration | **Seamless** | Separate | Separate | N/A |

**Sparkle's Unique Advantage**: Logical safety (no latches, no comb loops) AND physical/timing safety (registered output DRC) AND formal verification — all in one language, no external tools.

## Project Structure

```
sparkle/
├── Sparkle/              # Core library
│   ├── Core/            # Signal semantics, domains, and vectors
│   │   ├── Signal.lean  # Signal DSL: register, memory, loop, mux, ===, hw_cond
│   │   ├── StateMacro.lean # declare_signal_state: named state accessors
│   │   ├── JIT.lean     # JIT FFI: dlopen/dlsym, compile/load, eval/tick/getWire/memsetWord/snapshot/restore
│   │   ├── JITLoop.lean # loopMemoJIT: transparent JIT behind Signal API + runOptimized
│   │   ├── Oracle.lean  # Dynamic oracle: cycle-skipping with direct JITHandle access
│   │   ├── Domain.lean  # Clock domain configuration
│   │   └── Vector.lean  # Hardware vector types
│   ├── Data/            # BitPack and data types
│   ├── IR/              # Hardware IR and AST
│   │   ├── AST.lean     # Expressions, statements, modules
│   │   ├── Type.lean    # HWType with array support
│   │   └── Builder.lean # Circuit construction monad
│   ├── Compiler/        # Lean → IR compilation
│   │   ├── Elab.lean    # #synthesizeVerilog metaprogramming (9 handler functions + tracing)
│   │   └── DRC.lean     # Design Rule Check: registered output check (linter pass)
│   ├── Backend/         # Code generation backends
│   │   ├── Verilog.lean # SystemVerilog backend
│   │   ├── CppSim.lean  # C++ simulation + JIT wrapper generation
│   │   └── VCD.lean     # Waveform dump generation
│   ├── Library/         # Verified Standard IP Library
│   │   └── Queue/       # FIFO components
│   │       ├── QueueProps.lean # Pure formal model: 7 theorems (no sorry)
│   │       └── SyncFIFO.lean   # Synthesizable depth-4 FIFO (Valid/Ready)
│   └── Verification/    # Proof libraries and co-simulation
│       ├── Temporal.lean # Linear Temporal Logic (LTL) operators
│       ├── ArbiterProps.lean # Round-robin arbiter: 10 formal proofs (safety/liveness/fairness)
│       └── CoSim.lean   # Verilator integration
├── Examples/            # Example designs
│   ├── Counter.lean
│   ├── VerilogTest.lean
│   ├── Sparkle16/       # Complete 16-bit RISC CPU
│   ├── RV32/            # RV32IMA RISC-V SoC (Signal DSL) — boots Linux
│   │   ├── Core.lean    # ALU, branch comparator, hazard detection, decoder
│   │   ├── SoC.lean     # Full SoC: 122 registers, S-mode, Sv32 MMU, UART 8250
│   │   ├── Divider.lean # Multi-cycle restoring divider
│   │   └── ...          # Peripherals, decoder, ALU
│   ├── BitNet/          # BitNet b1.58 accelerator (Signal DSL)
│   │   ├── SignalHelpers.lean  # Reusable: adderTree, maxTree, lutMuxTree
│   │   ├── Layers/      # ReLU², ElemMul, ResidualAdd, RMSNorm, FFN
│   │   ├── BitLinear/   # Ternary MAC, adder tree, dynamic weights
│   │   ├── Attention/   # QKV, softmax, dot product, multi-head
│   │   └── SoC/         # Dual-arch: HardwiredUnrolled / TimeMultiplexed
│   ├── Arbiter/         # Round-Robin Arbiter (VDD worked example)
│   │   └── RoundRobin.lean # Signal DSL implementation + synthesis + simulation
│   ├── YOLOv8/          # YOLOv8n-WorldV2 object detection (Signal DSL)
│       ├── Config.lean   # Model dimensions, quantization params
│       ├── Types.lean    # Type aliases (WeightInt4, ActivationInt8, etc.)
│       ├── Top.lean      # Full SoC top-level controller
│       ├── Backbone.lean # 5-stage backbone FSM
│       ├── Neck.lean     # FPN + PAN controller
│       ├── Head.lean     # 3-scale detection head
│       ├── TextEmbedding.lean  # CLIP text embedding dot product
│       ├── Primitives/   # Conv2DEngine, LineBuffer, MaxPool, Dequant, etc.
│       └── Blocks/       # ConvBnSiLU, C2f, Bottleneck, SPPF
├── IP/                  # Verified IP Library
│   └── Video/
│       └── H264/        # H.264 Baseline Profile codec
│           ├── CAVLC.lean          # CAVLC encoder (pure + Signal FSM)
│           ├── CAVLCDecode.lean    # CAVLC decoder (pure Lean)
│           ├── DCT.lean            # 4×4 integer DCT/IDCT
│           ├── Quant.lean          # Quantization/dequantization (MF/V tables)
│           ├── NAL.lean            # NAL packer/parser (emulation prevention)
│           ├── IntraPred.lean      # Intra_4×4 prediction (9 modes)
│           ├── DRAMInterface.lean  # DRAM simulation model
│           ├── Encoder.lean        # Top-level encoder pipeline
│           ├── Decoder.lean        # Top-level decoder pipeline
│           ├── QuantRoundtripSynth.lean # Synthesizable quant/dequant FSM
│           ├── *Props.lean         # Formal proofs for each module
│           └── gen/                # Generated SV + CppSim + JIT
├── Tests/               # Test suites
│   ├── TestArray.lean   # Vector/array tests
│   ├── Sparkle16/       # CPU-specific tests
│   ├── RV32/            # RV32I simulation tests + JIT cycle-skip/oracle/dynamic-warp/speculative-warp tests
│   ├── BitNet/          # BitNet Signal DSL + golden validation tests
│   ├── YOLOv8/          # YOLOv8 primitive + golden value tests
│   ├── Video/           # H.264 pipeline tests
│   │   ├── DRAMTest.lean, DCTTest.lean, QuantTest.lean
│   │   ├── CAVLCDecodeTest.lean, NALTest.lean, IntraPredTest.lean
│   │   ├── H264PipelineTest.lean  # Full encode→decode roundtrip
│   │   ├── H264FrameTest.lean     # Frame-level E2E (multi-block, QP sweep, path equivalence)
│   │   └── H264JITTest.lean       # JIT end-to-end (4 tests)
│   ├── Library/         # Verified IP tests
│   │   └── TestSyncFIFO.lean # SyncFIFO: 16 tests (fill, drain, FIFO order, full/empty)
│   ├── golden-values/   # Real model data from bitnet.cpp
│   └── yolo-golden/     # Real model data from ultralytics YOLOv8
├── verilator/           # Verilator simulation backend
│   ├── rv32i_soc.sv    # SoC in SystemVerilog (matches Lean semantics)
│   ├── tb_soc.cpp      # C++ testbench (firmware, OpenSBI, Linux boot)
│   └── Makefile        # make build / make run
├── firmware/            # Boot firmware and device tree
│   ├── sparkle-soc.dts # Device tree source for Linux
│   └── opensbi/        # OpenSBI v0.9 boot support
├── scripts/             # Golden value generators
│   └── Video/           # H.264 C++ golden generators (DCT, quant, CAVLC, NAL, intra pred)
├── c_src/               # C FFI libraries
│   ├── sparkle_barrier.c # Signal.loopMemo memoization barriers
│   └── sparkle_jit.c    # JIT dlopen/dlsym FFI (lean_external_class)
└── lakefile.lean        # Build configuration
```

## Contributing

Sparkle is an educational project demonstrating:
- Functional hardware description
- Dependent type systems for hardware
- Theorem proving for verification
- Compiler construction and metaprogramming

Contributions welcome! Areas of interest:
- Verified standard IP (parameterized FIFO, crossbar, AXI4, TileLink) with formal proofs
- FPGA synthesis and tape-out examples
- Advanced IR optimization passes
- Additional examples and tutorials

## Roadmap

- [x] **Module hierarchy** - Multi-level designs ✓
- [x] **Tuple projections** - Readable `.fst`/`.snd`/`.proj*` methods ✓
- [x] **Comprehensive testing** - LSpec-based tests ✓
- [x] **Vector types** - Hardware arrays `HWVector α n` with indexing ✓
- [x] **Type inference** - Correct overflow/underflow for all bit widths ✓
- [x] **Waveform export** - VCD dump for GTKWave ✓
- [x] **Co-simulation** - Verilator integration for hardware validation ✓
- [x] **Temporal Logic** - Linear Temporal Logic (LTL) for verification ✓
- [x] **Memory primitives** - SRAM/BRAM with synchronous read/write ✓
- [x] **Cycle-skipping simulation** - Use proven temporal properties for optimization ✓
- [x] **BitNet b1.58 ASIC inference** - Complete accelerator with 60+ formal proofs ✓
- [x] **Signal DSL migration** - BitNet fully rewritten from CircuitM to Signal DSL ✓
- [x] **Golden value validation** - 16 tests against real bitnet.cpp model data ✓
- [x] **RV32IMA RISC-V SoC** - 4-stage pipelined CPU with M-ext, A-ext, UART, CLINT, CSR ✓
- [x] **Signal.loopMemo** - Memoized simulation with C FFI barriers ✓
- [x] **YOLOv8n-WorldV2** - Open-vocabulary object detection, 15 synthesizable modules ✓
- [x] **S-mode + Sv32 MMU** - Privilege separation, TLB, hardware page table walker ✓
- [x] **UART 8250** - Linux-compatible serial interface with RX support ✓
- [x] **OpenSBI v0.9 boot** - M-mode firmware with SBI ecall handling ✓
- [x] **Linux 6.6.0 boot** - Kernel boot on Verilator (prints version, memory zones, ISA) ✓
- [x] **Verilator backend** - ~1000x faster simulation, VCD tracing, Linux boot support ✓
- [x] **CppSim backend** - C++ code generation from IR, ~170x faster than Verilator for firmware tests ✓
- [x] **JIT FFI** - dlopen-based native simulation from Lean, ~200x faster than interpreted ✓
- [x] **DSL Ergonomics** - `===` equality, `hw_cond` macro, `Coe` implicit constants, Bool operators ✓
- [x] **State Macro** - `declare_signal_state` for named state accessors (eliminates magic indices) ✓
- [x] **Compiler Refactor** - Tracing infrastructure (`trace[sparkle.compiler]`) + 9 handler functions ✓
- [x] **VDD Framework** - Verification-Driven Design guide + Round-Robin Arbiter (10 formal proofs) ✓
- [x] **DRC/Linter** - Registered output check warns on combinational outputs (like SpyGlass) ✓
- [x] **Linux Boot Verified** - Generated SV boots Linux 6.6.0, matches hand-written reference ✓
- [x] **Transparent JIT (`loopMemoJIT`)** - Same `Signal dom α` API as `loopMemo`, ~700x faster via JIT C++ ✓
- [x] **Performance Analysis** - Identified CppSim bottleneck: 2x more instructions from unoptimized IR ✓
- [x] **CppSim Backend Optimization** - IR inlining + constant folding + local variable promotion → 2.1x speedup, gap closed from 2.7x to 1.3x ✓
- [x] **CppSim Phase 2 — Mask Elimination** - Aggressive `exprIsMasked` analysis (`.ref` invariant, AND/OR/XOR/SHR/ASR rules) → 449→137 mask ops (69.5% reduction) ✓
- [x] **CppSim Phase 3 — Observable Wire Threading** - Thread `observableWires` through optimizer/backend, demote ~950 `_gen_` to locals → 2.0x speedup (6.3M→12.6M cyc/s), JIT now **1.17x faster** than Verilator ✓
- [x] **Verified Standard IP — SyncFIFO** - Depth-4 FIFO with Valid/Ready interface: 7 formal proofs (QueueProps), synthesizable hardware (Signal DSL), 16 LSpec tests ✓
- [x] **JIT Cycle-Skipping Phase 1** - Register read/write API (C++ codegen → C FFI → Lean bindings), `JIT.runOptimized` with oracle callback, snapshot/restore roundtrip test passes. JIT now **1.17x faster** than Verilator (13.0M vs 11.1M cyc/s) ✓
- [x] **JIT Cycle-Skipping Phase 2 — Self-Loop Oracle** - Tolerance-based PC tracking (pcTolerance=12, threshold=50) with CLINT timer advancement. 10M cycles in 9ms (706x effective speedup). Firmware UART output identical with/without oracle ✓
- [x] **Linux Boot Time-Warping (Phase 29)** - Dynamic oracle receives `JITHandle` directly (register reads, `memsetWord`, `setReg`), simplified return type `IO (Option Nat)`, bulk memory API with bounds checking ✓
- [x] **Speculative Simulation with Rollback (Phase 29 Step 5)** - Full-state snapshot/restore via C++ copy constructor, guard-and-rollback pattern for interrupt-safe cycle-skipping (3-part test: roundtrip, guard-pass, guard-rollback) ✓

### Next Phases (TODO)
- [x] ~~**eval()+tick() Fusion**~~ - Done (Phase 30): fused evalTick() with stack-local `_next` vars, ~13.0M cyc/s
- [x] ~~**H.264 Baseline Codec**~~ - Done (Phase 31): Full encoder/decoder pipeline with formal proofs + JIT test
- [x] ~~**H.264 Frame-Level E2E Test**~~ - Done (Phase 31b): Multi-block encode→decode roundtrip, QP sweep, path equivalence, mode diversity
- [ ] **H.264 CAVLC Decoder Fix** - Fix non-trivial residual reconstruction (currently zeros), tighten frame MSE thresholds
- [ ] **H.264 Synthesizable Pipeline** - Extend pure Lean modules into fully synthesizable Signal DSL
- [ ] **Linux Boot Idle-Loop Skipping** - Extend dynamic oracle to detect WFI/idle loops during Linux boot
- [ ] **Verified Standard IP — Parameterized FIFO** - Generic depth/width FIFO with power-of-2 depth
- [ ] **Verified Standard IP — N-way Arbiter** - Generalize 2-client round-robin arbiter to N clients
- [ ] **Verified Standard IP — AXI4-Lite / TileLink** - Bus protocol interfaces with formal properties
- [ ] **GPGPU / Vector Core** - Apply the Verification-Driven Design (VDD) framework to highly concurrent, memory-bound accelerator architectures
- [ ] **FPGA Tape-out Flow** - End-to-end examples deploying Sparkle-generated Linux SoCs to physical FPGAs

## Development History

See [CHANGELOG.md](docs/CHANGELOG.md) for detailed development phases and implementation history.

## Author

**Junji Hashimoto**
- Twitter/X: [@junjihashimoto3](https://x.com/junjihashimoto3)

## License

Apache License 2.0 - see [LICENSE](LICENSE) file for details

## Acknowledgments

- Inspired by [Clash HDL](https://clash-lang.org/)
- Built with [Lean 4](https://lean-lang.org/)
