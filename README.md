# Sparkle HDL

[![Build](https://github.com/Verilean/sparkle/actions/workflows/build.yml/badge.svg)](https://github.com/Verilean/sparkle/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**Write hardware in Lean 4. Prove it correct. Generate Verilog.**

A type-safe hardware description language that brings the power of dependent types and theorem proving to hardware design.

## Why Sparkle?

```lean
-- Write this in Lean...
def counter : Signal Domain (BitVec 8) := do
  let count ← Signal.register 0
  count <~ count + 1
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

### Your First Circuit: Blinking LED

```lean
import Sparkle

open Sparkle.Core.Signal
open Sparkle.Core.Domain

-- A simple blinker that toggles every 1000 cycles
def blinker : Signal Domain Bool := do
  let counter ← Signal.register (0 : BitVec 10)
  let led ← Signal.register false

  -- Count up to 1000
  let nextCount := if counter == 999 then 0 else counter + 1

  -- Toggle LED when counter wraps
  let nextLed := if counter == 999 then !led else led

  counter <~ nextCount
  led <~ nextLed

  return led

#synthesizeVerilog blinker
```

This generates a fully synthesizable Verilog module with proper clock/reset handling!

## Key Features

### 🎯 Cycle-Accurate Simulation

Simulate your hardware designs with the same semantics as the final Verilog:

```lean
-- Define a multiply-accumulate circuit
def mac (a b : BitVec 16) : Signal Domain (BitVec 32) := do
  let acc ← Signal.register 0
  let product := a.zeroExtend 32 * b.zeroExtend 32
  acc <~ acc + product
  return acc

-- Simulate it
#eval Signal.simulate mac [(10, 20), (5, 3), (2, 8)] |>.take 3
-- Output: [0, 200, 215, 231]
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
-- Build a 4-stage FIR filter by composing delay elements
def fir4 (coeffs : Array (BitVec 16)) (input : BitVec 16) : Signal Domain (BitVec 32) := do
  let d1 ← Signal.register 0
  let d2 ← Signal.register 0
  let d3 ← Signal.register 0

  d1 <~ input
  d2 <~ d1
  d3 <~ d2

  let sum := input * coeffs[0]! +
             d1 * coeffs[1]! +
             d2 * coeffs[2]! +
             d3 * coeffs[3]!

  return sum.zeroExtend 32
```

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

### 🔁 Feedback Loops (Circular Let-Bindings)

**Recursive definitions with forward references don't work:**

```lean
-- ❌ WRONG: Forward reference in let-bindings
def counter_WRONG : Signal Domain (BitVec 16) :=
  let next := Signal.map (· + 1) count  -- ❌ Error: count not defined yet
  let count := Signal.register 0 next   -- ❌ Circular dependency
  count

-- ✓ RIGHT: For complex state, use manual IR construction
-- See Examples/Sparkle16/ALU.lean for working examples
```

**Why this happens:**
- Lean evaluates let-bindings sequentially
- No forward references are allowed
- Circular dependencies cannot be expressed with let-bindings

**Workaround:** Use manual IR construction with `CircuitM` for stateful circuits with feedback.

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

**⚠️ Limitations:**
- Pattern matching on Signal tuples (use `.fst`/`.snd` instead)
- Recursive let-bindings (use manual IR for feedback loops)
- Higher-order functions beyond `map`, `<*>`, and basic combinators
- General match expressions on Signals
- Array writes (only indexing reads supported currently)

### 🧪 Testing

Run the comprehensive test suite (130+ tests):

```bash
lake test
```

Tests include:
- Signal simulation (18 tests)
- IR and Verilog synthesis (13 tests)
- Verilog generation verification (19 tests)
- Array/Vector operations (27 tests)
- **Temporal Logic verification (33 tests)** - NEW!
- Overflow/underflow behavior (26 tests)
- Sparkle-16 CPU verification tests
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
│   └── Sparkle16/       # Complete CPU example
├── Tests/               # Test suites (100+ tests)
│   ├── TestArray.lean   # Vector/array tests (NEW!)
│   └── Sparkle16/       # CPU-specific tests
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
- [ ] **Cycle-skipping simulation** - Use proven temporal properties for optimization
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
