# Sparkle HDL

A type-safe hardware description language in Lean 4, inspired by Haskell's Clash.

## Overview

Sparkle is a functional HDL that allows you to:
- **Simulate** hardware designs with cycle-accurate semantics
- **Build** hardware netlists using a composable IR
- **Generate** synthesizable SystemVerilog code

## Features

### ✅ Phase 1: Simulation (Complete)
- **Domain Configuration**: Type-safe clock domains with configurable period, edge, and reset
- **Signal Semantics**: Stream-based signals (Nat → α) with Functor/Applicative/Monad instances
- **Hardware Primitives**: `register`, `registerWithEnable`, `mux`, bundling
- **BitPack**: Type class for hardware-representable types

### ✅ Phase 2: Netlist IR (Complete)
- **Hardware Types**: Bit, BitVector, Array
- **AST**: Expressions (const, ref, op), Statements (assign, register, inst)
- **Circuit Builder**: Compositional monad for building netlists
- **Name Hygiene**: Automatic unique wire naming with collision avoidance

### ✅ Phase 3: Compiler (Complete)
- **Primitive Registry**: Maps Lean functions (BitVec.add, BitVec.and, etc.) to hardware operators
- **Translation Kernel**: Translates Lean expressions to hardware IR
- **Synthesis Commands**: `#synthesize` and `#synthesizeVerilog` for automatic compilation
- **Signal Synthesis**: Automatic compilation of `Signal.register` and `Signal.mux` primitives
- **Automatic Clock/Reset**: Detects registers and adds clock/reset inputs automatically
- **Supported**: Combinational logic, registers, mux, feedback loops (Signal.loop), constants, let-bindings, binary operations
- **Name Hygiene**: `_gen_` prefix on generated wires prevents collisions with user code
- **Limitations**: Complex higher-order functions may need manual IR construction

### ✅ Phase 4: Verilog Backend (Complete)
- **Code Generation**: Clean, synthesizable SystemVerilog output
- **Type Mapping**: Lean types → Verilog types
- **Operator Mapping**: IR operators → Verilog syntax
- **Register Generation**: Proper always_ff blocks with reset
- **Advanced Examples**: MAC, FIR filter, traffic light, shift register, FIFO

### ✅ Phase 5: Feedback Loops (Complete)
- **Signal.loop Primitive**: Fixed-point combinator for feedback loops
- **Counter Support**: Enable circuits where output feeds back to input
- **State Machines**: Support for stateful hardware designs
- **Loop Closure**: Automatic wire allocation and connection for feedback paths
- **Variable Mapping**: Scoped tracking of loop variables during compilation

## Quick Start

### Running Examples

#### Phase 1: Simulation
```bash
lake env lean --run Examples/Counter.lean
```

Demonstrates:
- Combinational logic (addition, multiplication)
- Register delays
- Multiplexers
- Signal bundling

#### Phase 2: Manual IR Construction
```bash
lake env lean --run Examples/ManualIR.lean
```

Builds hardware netlists for:
- Half adder and full adder
- 4-bit adder
- Registers and counters
- Accumulator
- Comparator

#### Phase 3: Automatic Synthesis
```bash
lake env lean --run Examples/SynthesisTest.lean
```

Demonstrates metaprogramming-based compilation:
- Automatic translation of Lean functions to hardware IR
- `#synthesize` command for IR generation
- `#synthesizeVerilog` command for direct Verilog output
- Combinational logic with let-bindings
- BitVec operations (add, and, or, xor, mul, sub)

Example usage in Lean files:
```lean
def myCircuit (a b : BitVec 8) : BitVec 8 :=
  let x := a + b
  let y := x &&& 5#8
  y

#synthesize myCircuit        -- Generate IR
#synthesizeVerilog myCircuit -- Generate Verilog
```

**Signal-level synthesis** (NEW):
```bash
lake env lean --run Examples/SignalSynthesis.lean
```

Demonstrates automatic Signal-to-IR compilation:
- Simple register with constant input
- Register chains (multi-cycle delays)
- Mux selection
- Combined register + mux (enabled register)
- Automatic clock/reset input generation

Example usage:
```lean
def simpleRegister {dom} : Signal dom (BitVec 8) :=
  let input := Signal.pure 42#8
  register 0#8 input

#synthesizeVerilog simpleRegister
-- Generates module with clk, rst inputs and always_ff block
```

**Feedback loop synthesis** (NEW):
```bash
lake env lean --run Examples/LoopSynthesis.lean
```

Demonstrates Signal.loop for feedback paths:
- Counter with feedback (cnt = cnt + 1)
- Automatic loop wire allocation
- Loop closure with register to break combinational cycles

Example usage:
```lean
def counter {dom} : Signal dom (BitVec 8) :=
  Signal.loop fun cnt =>
    let next := (· + ·) <$> cnt <*> Signal.pure 1#8
    register 0#8 next

#synthesizeVerilog counter
-- Generates counter with feedback path properly closed
```

#### Phase 4: Verilog Generation
```bash
lake env lean --run Examples/VerilogTest.lean
```

Generates basic `.sv` files for:
- HalfAdder.sv
- Register8.sv
- Counter8.sv
- Mux2to1.sv
- ALU4Bit.sv
- Accumulator.sv

```bash
lake env lean --run Examples/FullCycle.lean
```

Generates advanced `.sv` files for:
- MAC.sv (Multiply-Accumulate unit)
- FIR3Tap.sv (3-tap FIR filter)
- TrafficLight.sv (State machine)
- ShiftRegister8.sv (Serial-to-parallel converter)
- FIFO4.sv (4-entry FIFO buffer)

#### Test Suites
```bash
lake env lean --run Tests/Simulation.lean  # Phase 1 tests
lake env lean --run Tests/Synthesis.lean   # Phase 2 & 4 tests
lake env lean --run Tests/Compiler.lean    # Phase 3 tests
```

## Example: Building a Counter

### Step 1: Simulate
```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- Create a simple input signal
let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩

-- Add a register (one-cycle delay)
let delayed := Signal.register 0#8 input

-- Test simulation
#eval delayed.atTime 0  -- outputs 0 (initial value)
#eval delayed.atTime 1  -- outputs 0 (input at t=0)
#eval delayed.atTime 2  -- outputs 1 (input at t=1)
```

### Step 2: Build IR
```lean
import Sparkle.IR.Builder

open Sparkle.IR.Type
open Sparkle.IR.Builder
open CircuitM

def counter8 : Module :=
  runModule "Counter8" do
    addInput "clk" .bit
    addInput "rst" .bit

    let nextCount ← makeWire "next_count" (.bitVector 8)
    let currentCount ← emitRegister "count" "clk" "rst" (.ref nextCount) 0 (.bitVector 8)

    emitAssign nextCount (Expr.add (.ref currentCount) (.const 1 8))

    addOutput "count" (.bitVector 8)
    emitAssign "count" (.ref currentCount)
```

### Step 3: Generate Verilog
```lean
import Sparkle.Backend.Verilog

let verilog := Verilog.toVerilog counter8
IO.println verilog
Verilog.writeVerilogFile counter8 "Counter8.sv"
```

Output:
```systemverilog
// Generated by Sparkle HDL
// Module: Counter8

module Counter8 (
    input logic clk,
    input logic rst,
    output logic [7:0] count
);
    logic [7:0] next_count_0;
    logic [7:0] count_1;

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            count_1 <= 8'd0;
        else
            count_1 <= next_count_0;
    end

    assign next_count_0 = (count_1 + 8'd1);
    assign count = count_1;
endmodule
```

## Design Philosophy

### Lessons from Clash

Sparkle improves on Clash HDL by addressing common pain points:

1. **Compiler Independence**: Lean 4 is self-hosted (no GHC dependency issues)
2. **Name Hygiene**: Robust unique name generation prevents HDL name clashing
3. **Clear Primitives**: Explicit operator registry, no hidden blackboxes
4. **Type Safety**: Leverages Lean's dependent types for compile-time guarantees
5. **Fast Compilation**: Simple IR structure avoids deep normalization chains
6. **Simulation Consistency**: Stream-based simulation matches synthesis semantics

### Type-Safe Clock Domains

Clock domains prevent accidental mixing of signals from different frequencies:

```lean
let signal100MHz : Signal domain100MHz (BitVec 8) := ...
let signal50MHz  : Signal domain50MHz (BitVec 8) := ...

-- This won't type-check! Domains don't match.
-- let mixed := (·  + ·) <$> signal100MHz <*> signal50MHz
```

### Separation of Simulation and Synthesis

- **Simulation**: Pure Lean functions (Nat → α)
- **Synthesis**: Explicit IR generation
- **Benefit**: Easy to test designs before committing to hardware

## Project Structure

```
sparkle/
├── Sparkle/
│   ├── Core/
│   │   ├── Domain.lean      # Clock domain configuration
│   │   └── Signal.lean      # Signal types and simulation
│   ├── Data/
│   │   └── BitPack.lean     # Hardware type serialization
│   ├── IR/
│   │   ├── Type.lean        # Hardware type system
│   │   ├── AST.lean         # Netlist AST
│   │   └── Builder.lean     # Circuit builder monad
│   ├── Compiler/
│   │   └── Elab.lean        # Metaprogramming compiler
│   └── Backend/
│       └── Verilog.lean     # SystemVerilog code generation
├── Examples/
│   ├── Counter.lean         # Phase 1: Simulation examples
│   ├── ManualIR.lean        # Phase 2: IR building examples
│   ├── SynthesisTest.lean   # Phase 3: Automatic synthesis (BitVec)
│   ├── SignalSynthesis.lean # Phase 3: Signal-to-IR synthesis
│   ├── LoopSynthesis.lean   # Phase 5: Feedback loop synthesis
│   ├── VerilogTest.lean     # Phase 4: Verilog generation
│   └── FullCycle.lean       # Phase 4: Advanced examples
├── Tests/
│   ├── Simulation.lean      # Phase 1 tests
│   ├── Synthesis.lean       # Phase 2 & 4 tests
│   └── Compiler.lean        # Phase 3 tests
└── lakefile.lean
```

## Building

```bash
# Build the entire project
lake build

# Run examples
lake env lean --run Examples/Counter.lean
lake env lean --run Examples/ManualIR.lean
lake env lean --run Examples/VerilogTest.lean
```

## Future Work

### Additional Features
- Vector types (`Vec n α`) for parameterized hardware
- Module instantiation and hierarchical designs
- RAM/ROM inference
- Testbench generation
- Formal verification hooks

## Comparison with Other HDLs

| Feature | Sparkle | Clash | Chisel | Traditional Verilog |
|---------|---------|-------|--------|---------------------|
| Language | Lean 4 | Haskell | Scala | Verilog |
| Type Safety | ✅ Dependent | ✅ Strong | ✅ Strong | ⚠️ Weak |
| Simulation | ✅ Built-in | ✅ Built-in | ✅ Built-in | ❌ Separate |
| Proof Integration | ✅ Native | ⚠️ External | ⚠️ External | ❌ None |
| Compiler Deps | ✅ Self-hosted | ⚠️ GHC | ⚠️ JVM/Scala | ✅ Standalone |
| Learning Curve | High | High | Medium | Low |

## Contributing

Sparkle is an educational project demonstrating:
- Functional HDL design
- Lean 4 metaprogramming
- Compiler construction
- Hardware synthesis

Improvements welcome!

## License

MIT

## Acknowledgments

- Inspired by [Clash HDL](https://clash-lang.org/)
- Built with [Lean 4](https://lean-lang.org/)
- Informed by lessons from Clash's GitHub issues and community discussions
