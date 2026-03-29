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

## IP Catalog

Sparkle ships with production-grade IP cores — each with pure Lean specs, formal proofs, and synthesizable Signal DSL implementations.

| IP | Description | Proofs | Synth | Details |
|----|-------------|:------:|:-----:|---------|
| **[BitNet b1.58](docs/BitNet.md)** | Formally verified LLM inference accelerator. Ternary weights, Q16.16 datapath, dual architecture (1-cycle vs 12-cycle) | 60+ theorems | Full | 202K / 99K cells |
| **[YOLOv8n-WorldV2](docs/YOLOv8.md)** | Open-vocabulary object detection. INT4/INT8 quantized, 15 modules, CLIP text embeddings | Golden validation | Full | Backbone + Neck + Head |
| **[RV32IMA SoC](docs/RV32.md)** | RISC-V CPU — boots Linux 6.6.0. 4-stage pipeline, Sv32 MMU, UART, CLINT. JIT at 14M cyc/s (1.6x Verilator). LiteX PicoRV32 SoC at 11.5M (1.08x Verilator). 102 formal proofs | 102 theorems | Full | 122 registers |
| **[AXI4-Lite Bus](docs/RV32.md)** | Verified AXI4-Lite slave/master. Protocol compliance (valid persistence, deadlock-free), synthesizable | 14 theorems | Full | 23 sim tests |
| **[SV→Sparkle Transpiler](docs/RV32.md#sv-transpiler)** | Parse Verilog → JIT simulation. LiteX SoC (1730 lines) at 11.5M cyc/s — exceeds Verilator. Constant propagation, self-ref if-else, decoder guard, wire localization. 34 CI-safe tests | 6+ theorems | JIT | 34 tests |
| **[H.264 Codec](docs/H264.md)** | Baseline Profile encoder + decoder. Hardware MP4 muxer produces playable files. 14 modules | 15+ theorems | Full | 709-byte MP4 output |
| **[CDC Infrastructure](docs/CDC.md)** | Lock-free multi-clock simulation. SPSC queue (210M ops/sec), rollback mechanism, JIT.runCDC | 12 theorems | C++ | 2-thread Time-Warping |

---

## Why Sparkle?

```lean
-- Write this in Lean...
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.circuit do
    let count ← Signal.reg 0#8;
    count <~ count + 1#8;
    return count

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
  a + b

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

**Feedback loops** use `Signal.circuit` with imperative `<~` register assignment — see the counter example above. For complex state machines, see `Examples/RV32/SoC.lean`.

## Key Features

### 🎯 Cycle-Accurate Simulation

Simulate your hardware designs with the same semantics as the final Verilog:

```lean
-- Define a simple adder
def adder (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  a + b

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

  -- Multiply and accumulate using operator syntax
  let term0 := input * c0
  let term1 := d1 * c1
  let term2 := d2 * c2
  let term3 := d3 * c3

  -- Sum all terms
  let sum01 := term0 + term1
  let sum23 := term2 + term3
  sum01 + sum23

#synthesizeVerilog fir4
```

**Key patterns:**
- `Signal.register init input` - Creates a D flip-flop (1-cycle delay)
- `a + b`, `a * b` - Natural operators work between Signal ↔ Signal and Signal ↔ BitVec
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
# Run H.264 pipeline + frame-level + decoder synth tests
lake test

# JIT end-to-end test (compile quant/dequant FSM, run 4 tests)
lake exe h264-jit-test

# Generate decoder pipeline Verilog + CppSim + JIT
lake build IP.Video.H264.DecoderSynth
# → IP/Video/H264/gen/decoder_pipeline.sv (29KB)
# → IP/Video/H264/gen/decoder_pipeline_cppsim.h
# → IP/Video/H264/gen/decoder_pipeline_jit.cpp
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

**IP Documentation:**
- [docs/BitNet.md](docs/BitNet.md) — BitNet b1.58 ASIC inference engine (60+ proofs)
- [docs/YOLOv8.md](docs/YOLOv8.md) — YOLOv8n object detection accelerator (15 modules)
- [docs/RV32.md](docs/RV32.md) — RV32IMA RISC-V SoC (boots Linux, JIT at 13M cyc/s)
- [docs/H264.md](docs/H264.md) — H.264 Baseline codec (hardware MP4 encoder)
- [docs/CDC.md](docs/CDC.md) — Lock-free CDC infrastructure (210M ops/sec SPSC queue)

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
- **H.264 decoder synth tests** — Dequant reference (QP=20 V×scale), IDCT reference (butterfly), reconstruct reference (clamp), full pipeline consistency, edge cases (clamp to 0/255, zero block)
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
│           ├── Decoder.lean        # Top-level decoder pipeline (pure)
│           ├── QuantRoundtripSynth.lean # Synthesizable quant/dequant FSM
│           ├── DequantSynth.lean   # Synthesizable dequant FSM (QP=20)
│           ├── IDCTSynth.lean      # Synthesizable inverse DCT FSM (butterfly)
│           ├── ReconstructSynth.lean # Synthesizable reconstruction FSM (add+clamp)
│           ├── DecoderSynth.lean   # Synthesizable decoder pipeline (monolithic FSM)
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
│   │   ├── H264JITTest.lean       # JIT end-to-end (4 tests)
│   │   └── H264DecoderSynthTest.lean # Decoder synth reference tests (dequant, IDCT, recon, pipeline)
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
- [x] ~~**H.264 CAVLC Decoder Fix**~~ - Done (Phase 31c): Complete VLC tables + inverse zig-zag, QP=30 MSE 3071→284, 4 formal proofs
- [x] ~~**H.264 Synthesizable Decoder Pipeline**~~ - Done (Phase 32): Dequant + IDCT + Reconstruct FSMs, monolithic pipeline, pure reference tests
- [x] ~~**Type-Safe JIT Wrappers**~~ - Done (Phase 45): `SimInput`/`SimOutput`/`Simulator` generated by `verilog!` macro
- [x] ~~**Signal Operator Refactoring**~~ - Done (Phase 46): Mixed Signal/BitVec operators (`a + 1#8`, `1#64 <<< b`), compiler fix for inline expansion
- [x] ~~**Imperative `<~` Assignment**~~ - Done (Phase 47): `Signal.circuit` macro with `<~` register assignment, unified `Signal.loop` memoization
- [x] ~~**AXI4-Lite Bus Protocol**~~ - Done (Phase 48): Verified slave/master, 14 proofs, 23 sim tests, synthesizable
- [x] ~~**RV32I Formal Verification**~~ - Done (Phase 49): 102 theorems, **MSTATUS WPRI bug found**, Signal DSL ↔ spec equivalence
- [x] ~~**Linux Boot Idle-Loop Skipping**~~ - Done (Phase 50): MIE/MTIE interrupt guard, WFI fast-path, 4 CI oracle accuracy tests
- [ ] **Verified Standard IP — Parameterized FIFO** - Generic depth/width FIFO with power-of-2 depth
- [ ] **Verified Standard IP — N-way Arbiter** - Generalize 2-client round-robin arbiter to N clients
- [ ] **Verified Standard IP — TileLink / AXI4 Interconnect** - Full AXI4 (bursts, IDs) and TileLink
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
