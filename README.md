# Sparkle HDL

[![Build](https://github.com/Verilean/sparkle/actions/workflows/build.yml/badge.svg)](https://github.com/Verilean/sparkle/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**Write hardware in Lean 4. Prove it correct. Generate Verilog.**

A type-safe hardware description language that brings the power of dependent types and theorem proving to hardware design.

## Killer App: BitNet b1.58 ASIC Inference Engine

Sparkle ships with a **complete, formally verified BitNet b1.58 RTL generator** — a production-grade ternary-weight neural network inference core targeting ASIC synthesis. This is the world's first formally verified LLM inference hardware generated from a theorem prover.

### What It Does

One Lean command generates a **complete 12-layer, 64-dimension BitNet SoC** as synthesizable SystemVerilog:

```lean
import Examples.BitNet

-- Generate a TimeMultiplexed SoC: 1 shared core + weight ROM + FSM
let soc ← buildBitNetSoC {
  archMode := .TimeMultiplexed, nLayers := 12, dim := 64, ffnDim := 64
} weights scales

-- Emit 1,909 lines of synthesizable SystemVerilog
IO.println (toVerilog soc)
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

### End-to-End RTL Simulation

```bash
# Compile and simulate with Icarus Verilog
cd hw/sim/tb
iverilog -g2012 -o tb_soc_hello tb_soc_hello.sv ../../synth/time_muxed.sv
vvp tb_soc_hello
```

```
=== BitNet End-to-End RTL Simulation ===
Input: "hello" (5 chars as Q16.16)
Architecture: TimeMultiplexed, 12 layers, dim=64

  Char[0] 'h': x_in=0x00680000 -> y_out=0x80000000
  Char[1] 'e': x_in=0x00650000 -> y_out=0x3af75fc5
  Char[2] 'l': x_in=0x006c0000 -> y_out=0x80000000
  Char[3] 'l': x_in=0x006c0000 -> y_out=0x80000000  (deterministic!)
  Char[4] 'o': x_in=0x006f0000 -> y_out=0x4ae5ffa3

=== Simulation Complete ===
```

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
# Generate and simulate BitNet SoC RTL
lake env lean --run Examples/BitNet/Top.lean
```
Generates a complete 12-layer BitNet SoC with dual architecture options, 60+ formal proofs, and Yosys-synthesizable SystemVerilog.

### All Examples
```bash
# Simulation examples
lake env lean --run Examples/Counter.lean
lake env lean --run Examples/ManualIR.lean
lake env lean --run Examples/SimpleMemory.lean          # NEW: Memory simulation

# Verilog generation
lake env lean --run Examples/VerilogTest.lean
lake env lean --run Examples/FullCycle.lean
lake env lean --run Examples/MemoryManualIR.lean        # NEW: Memory Verilog generation

# Feedback loops
lake env lean --run Examples/LoopSynthesis.lean

# Technology primitives
lake env lean --run Examples/PrimitiveTest.lean

# Sparkle-16 CPU
lake env lean --run Examples/Sparkle16/ALU.lean
lake env lean --run Examples/Sparkle16/RegisterFile.lean
lake env lean --run Examples/Sparkle16/Core.lean
lake env lean --run Examples/Sparkle16/ISAProofTests.lean
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

**Temporal Logic Examples:**
- See [Examples/TemporalLogicExample.md](Examples/TemporalLogicExample.md) for comprehensive temporal logic usage
- Includes reset stability, state machine verification, and pipeline examples
- Documents cycle-skipping optimizations and proof obligations

## How It Works

### The Sparkle Pipeline

```
┌─────────────┐
│  Lean Code  │  Write hardware using Signal monad
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ Simulation  │  Test with cycle-accurate semantics
└──────┬──────┘
       │
       ▼
┌─────────────┐
│   IR Builder│  Compile to hardware netlist
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Verilog    │  Generate SystemVerilog
└─────────────┘
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

### ⚠️ Imperative Syntax NOT Supported (IMPORTANT!)

**The `<~` feedback operator and imperative do-notation shown in some older documentation DO NOT WORK:**

```lean
-- ❌ WRONG: This syntax doesn't exist yet!
def counter : Signal Domain (BitVec 8) := do
  let count ← Signal.register 0
  count <~ count + 1  -- ❌ The <~ operator is not implemented!
  return count

-- ❌ WRONG: This won't work either
def fir4 (coeffs : Array (BitVec 16)) (input : BitVec 16) := do
  let d1 ← Signal.register 0  -- ❌ Missing input signal argument!
  d1 <~ input                 -- ❌ <~ doesn't exist!
  ...
```

**Why these don't work:**
1. **`<~` operator**: Not defined in the codebase - this is aspirational future syntax
2. **`do`-notation for feedback**: Signal Monad doesn't support imperative assignment
3. **Runtime values**: `Array`, single `BitVec` values can't be synthesized to hardware
4. **Wrong mental model**: Signals are dataflow, not imperative assignments

**✓ CORRECT approaches:**

```lean
-- For simple feedback: use let rec
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let rec count := Signal.register 0#8 (count.map (· + 1))
  count

-- For feed-forward: direct dataflow
def registerChain (input : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  let d1 := Signal.register 0#16 input
  let d2 := Signal.register 0#16 d1
  d2

-- For complex feedback: manual IR construction
-- See Examples/LoopSynthesis.lean and Examples/Sparkle16/
```

**Key differences:**
- Signals are **wire streams**, not variables you assign to
- Use `Signal.register init input` with both arguments
- Coefficients/constants must be Signal inputs, not runtime values
- Operations use applicative style: `(· + ·) <$> sig1 <*> sig2`

See `test.lean` for a working FIR filter example.

### ⚠️ Pattern Matching on Tuples (IMPORTANT!)

**unbundle2 and pattern matching DO NOT WORK in synthesis:**

```lean
-- ❌ WRONG: This will fail with "Unbound variable" errors
def example_WRONG (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let (a, b) := unbundle2 input  -- ❌ FAILS!
  (· + ·) <$> a <*> b

-- ✓ RIGHT: Use .fst and .snd projection methods
def example_RIGHT (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let a := input.fst  -- ✓ Works!
  let b := input.snd  -- ✓ Works!
  (· + ·) <$> a <*> b
```

**Why this happens:**
- `unbundle2` returns a Lean-level tuple `(Signal α × Signal β)`
- Lean compiles pattern matches into intermediate forms during elaboration
- By the time synthesis runs, these patterns are compiled away
- The synthesis compiler cannot track the destructured variables

**Solution:** Use projection methods instead:
- For 2-tuples: `.fst` and `.snd`
- For 3-tuples: `.proj3_1`, `.proj3_2`, `.proj3_3`
- For 4-tuples: `.proj4_1`, `.proj4_2`, `.proj4_3`, `.proj4_4`
- For 5-8 tuples: `unbundle5` through `unbundle8` (but access via tuple projections, not pattern matching)

See [Tests/TestUnbundle2.lean](Tests/TestUnbundle2.lean) for detailed examples.

### 🔀 If-Then-Else in Signal Contexts

**Standard if-then-else gets compiled to match expressions and doesn't work:**

```lean
-- ❌ WRONG: if-then-else in Signal contexts
def example_WRONG (cond : Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  if cond then a else b  -- ❌ Error: Cannot instantiate Decidable.rec

-- ✓ RIGHT: Use Signal.mux instead
def example_RIGHT (cond : Signal Domain Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  Signal.mux cond a b  -- ✓ Works!
```

**Why this happens:**
- Lean compiles `if-then-else` into `ite` which becomes `Decidable.rec`
- The synthesis compiler cannot handle general recursors
- This is a fundamental limitation of how conditionals are compiled

**Solution:** Always use `Signal.mux` for hardware multiplexers, which generates proper Verilog.

### 🔁 Feedback Loops (Circular Dependencies)

**Simple feedback with `let rec` works:**

```lean
-- ✓ RIGHT: Simple counter with let rec
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let rec count := Signal.register 0#8 (count.map (· + 1))
  count

#synthesizeVerilog counter  -- ✓ Works!
```

**Complex feedback with multiple signals requires manual IR:**

```lean
-- ❌ WRONG: Multiple interdependent signals
def stateMachine : Signal Domain State :=
  let next := computeNext state input
  let state := Signal.register Idle next  -- ❌ Forward reference
  state

-- ✓ RIGHT: Use manual IR construction for complex feedback
-- See Examples/LoopSynthesis.lean and Examples/Sparkle16/ for working patterns
```

**Why this limitation exists:**
- Lean evaluates let-bindings sequentially (no forward references)
- `let rec` works for single self-referential definitions
- Multiple circular bindings need explicit fixed-point construction

**Workarounds:**
- **Simple loops**: Use `let rec` (counters, single-register state)
- **Complex feedback**: Use manual IR construction with `CircuitM`
- See `Examples/LoopSynthesis.lean` for comprehensive examples

### 📋 What's Supported

**✓ Fully supported in synthesis:**
- Basic arithmetic: `+`, `-`, `*`, `&&&`, `|||`, `^^^`
- Comparisons: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Bitwise operations: shifts, rotations
- Signal operations: `map`, `pure`, `<*>` (applicative)
- Registers: `Signal.register`
- Mux: `Signal.mux`
- Tuples: `bundle2`/`bundle3` and `.fst`/`.snd`/`.proj*` projections
- **Arrays/Vectors**: `HWVector α n` with `.get` indexing
- **Memory primitives**: `Signal.memory` for SRAM/BRAM with synchronous read/write
- **Correct overflow**: All bit widths preserve wrap-around semantics
- Hierarchical modules: function calls generate module instantiations
- **Co-simulation**: Verilator integration for validation

**⚠️ Current Limitations:**
- **No `<~` feedback operator** - Use `let rec` or manual IR construction
- **No imperative do-notation** - Use dataflow style with applicative operators
- **No runtime constants** - Arrays, single BitVec values can't be synthesized
- Pattern matching on Signal tuples (use `.fst`/`.snd` instead)
- Recursive let-bindings for complex feedback (use manual IR construction)
- Higher-order functions beyond `map`, `<*>`, and basic combinators
- General match expressions on Signals
- Array writes (only indexing reads supported currently)

### 🧪 Testing

Run the comprehensive test suite (190+ tests):

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
- **BitNet RTL correctness (60+ proofs)** - NEW!
- Combinational and sequential circuits
- Hierarchical module instantiation
- Co-simulation with Verilator

## Comparison with Other HDLs

| Feature | Sparkle | Clash | Chisel | Verilog |
|---------|---------|-------|--------|---------|
| Language | Lean 4 | Haskell | Scala | Verilog |
| Type System | Dependent Types | Strong | Strong | Weak |
| Simulation | Built-in | Built-in | Built-in | External Tools |
| Formal Verification | **Native (Lean)** | External | External | None |
| Learning Curve | High | High | Medium | Low |
| Proof Integration | **Seamless** | Separate | Separate | N/A |

**Sparkle's Unique Advantage**: Write your hardware and its correctness proofs in the *same language* with no tool boundaries.

## Project Structure

```
sparkle/
├── Sparkle/              # Core library
│   ├── Core/            # Signal semantics, domains, and vectors
│   │   ├── Signal.lean  # Signal monad and operations
│   │   ├── Domain.lean  # Clock domain configuration
│   │   └── Vector.lean  # Hardware vector types (NEW!)
│   ├── Data/            # BitPack and data types
│   ├── IR/              # Hardware IR and AST
│   │   ├── AST.lean     # Expressions, statements, modules
│   │   ├── Type.lean    # HWType with array support
│   │   └── Builder.lean # Circuit construction monad
│   ├── Compiler/        # Lean → IR compilation
│   │   └── Elab.lean    # Metaprogramming synthesis
│   ├── Backend/         # Verilog code generation
│   │   ├── Verilog.lean # SystemVerilog backend
│   │   └── VCD.lean     # Waveform dump generation
│   └── Verification/    # Proof libraries and co-simulation
│       ├── Temporal.lean # Linear Temporal Logic (LTL) operators (NEW!)
│       └── CoSim.lean   # Verilator integration
├── Examples/            # Example designs
│   ├── Counter.lean
│   ├── VerilogTest.lean
│   ├── Sparkle16/       # Complete 16-bit RISC CPU
│   └── BitNet/          # BitNet b1.58 ASIC inference engine (NEW!)
├── Tests/               # Test suites (100+ tests)
│   ├── TestArray.lean   # Vector/array tests
│   ├── Sparkle16/       # CPU-specific tests
│   └── BitNet/          # BitNet correctness tests (NEW!)
└── lakefile.lean        # Build configuration
```

## Contributing

Sparkle is an educational project demonstrating:
- Functional hardware description
- Dependent type systems for hardware
- Theorem proving for verification
- Compiler construction and metaprogramming

Contributions welcome! Areas of interest:
- Additional examples and tutorials
- More comprehensive verification proofs
- Advanced synthesis optimizations
- Tool integration (simulation viewers, waveform dumps)

## Roadmap

- [x] **Module hierarchy** - Multi-level designs ✓
- [x] **Tuple projections** - Readable `.fst`/`.snd`/`.proj*` methods ✓
- [x] **Comprehensive testing** - 130+ LSpec-based tests ✓
- [x] **Vector types** - Hardware arrays `HWVector α n` with indexing ✓
- [x] **Type inference** - Correct overflow/underflow for all bit widths ✓
- [x] **Waveform export** - VCD dump for GTKWave ✓
- [x] **Co-simulation** - Verilator integration for hardware validation ✓
- [x] **Temporal Logic** - Linear Temporal Logic (LTL) for verification ✓
- [x] **Memory primitives** - SRAM/BRAM with synchronous read/write ✓
- [x] **Cycle-skipping simulation** - Use proven temporal properties for optimization ✓
- [x] **BitNet b1.58 ASIC inference** - Complete RTL generator with 60+ formal proofs ✓
- [ ] **Feedback operator `<~`** - Ergonomic syntax for register feedback loops
- [ ] **Imperative do-notation** - More intuitive syntax for stateful circuits
- [ ] **Constant synthesis** - Support for BitVec literals and Arrays as parameters
- [ ] **More proofs** - State machine invariants, protocol correctness
- [ ] **Optimization passes** - Dead code elimination, constant folding
- [ ] **FIRRTL backend** - Alternative to Verilog for formal tools
- [ ] **Memory initialization** - Load memory from files for ROM/RAM init

## Development History

See [CHANGELOG.md](CHANGELOG.md) for detailed development phases and implementation history.

## Author

**Junji Hashimoto**
- Twitter/X: [@junjihashimoto3](https://x.com/junjihashimoto3)

## License

Apache License 2.0 - see [LICENSE](LICENSE) file for details

## Acknowledgments

- Inspired by [Clash HDL](https://clash-lang.org/)
- Built with [Lean 4](https://lean-lang.org/)
