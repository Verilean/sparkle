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

# Verilog generation
lake env lean --run Examples/VerilogTest.lean
lake env lean --run Examples/FullCycle.lean

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
- Verification framework (proofs and theorems)
- Sparkle-16 CPU architecture

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
│   ├── Core/            # Signal semantics and domains
│   ├── Data/            # BitPack and data types
│   ├── IR/              # Hardware IR and AST
│   ├── Compiler/        # Lean → IR compilation
│   ├── Backend/         # Verilog code generation
│   └── Verification/    # Proof libraries
├── Examples/            # Example designs
│   ├── Counter.lean
│   ├── VerilogTest.lean
│   └── Sparkle16/       # Complete CPU example
├── Tests/               # Test suites
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

- [ ] **Vector types** - Parameterized hardware `Vec n α`
- [ ] **Module hierarchy** - Multi-level designs
- [ ] **Waveform export** - VCD dump for GTKWave
- [ ] **More proofs** - State machine invariants, protocol correctness
- [ ] **Optimization passes** - Dead code elimination, constant folding
- [ ] **FIRRTL backend** - Alternative to Verilog for formal tools

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
