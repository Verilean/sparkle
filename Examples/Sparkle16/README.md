# Sparkle-16 CPU

A 16-bit RISC CPU implemented in Sparkle HDL to demonstrate hardware design with formal verification.

## Architecture Overview

**Sparkle-16** is a simplified 16-bit RISC architecture designed for clarity and ease of formal verification.

### Specifications

- **Data Width**: 16 bits
- **Address Width**: 16 bits (64KB address space)
- **Registers**: 8 general-purpose registers (R0-R7)
  - R0 is hardwired to 0 (zero register)
  - R1-R7 are writable
- **Architecture**: Harvard (separate instruction and data memory)
- **Execution**: Single-cycle (simplified, no pipelining)

### Instruction Set

| Instruction | Encoding | Description |
|-------------|----------|-------------|
| `LDI Rd, Imm8` | `000_ddd_iiiiiiii_pp` | Load 8-bit immediate into Rd (zero-extended) |
| `ADD Rd, Rs1, Rs2` | `001_ddd_sss_ttt_pppp` | Rd = Rs1 + Rs2 |
| `SUB Rd, Rs1, Rs2` | `010_ddd_sss_ttt_pppp` | Rd = Rs1 - Rs2 |
| `AND Rd, Rs1, Rs2` | `011_ddd_sss_ttt_pppp` | Rd = Rs1 & Rs2 |
| `LD Rd, [Rs1]` | `100_ddd_sss_ppppppp` | Load word from memory[Rs1] |
| `ST [Rs1], Rs2` | `101_sss_ttt_ppppppp` | Store Rs2 to memory[Rs1] |
| `BEQ Rs1, Rs2, Offset` | `110_sss_ttt_ooooooo` | Branch to PC+Offset if Rs1==Rs2 |
| `JMP Addr` | `111_aaaaaaaaaaaaa` | Jump to absolute address (13-bit) |

**Legend**: `ooo`=opcode, `ddd`=Rd, `sss`=Rs1, `ttt`=Rs2, `iii`=immediate, `ppp`=padding

## Components

### 1. ISA (ISA.lean)

Defines the instruction set architecture with:
- `Instruction` inductive type for all 8 instructions
- `encode : Instruction → BitVec 16` - Convert instruction to machine code
- `decode : BitVec 16 → Option Instruction` - Parse machine code
- Helper functions: `isBranch`, `writesRegister`, `destReg?`

**Example:**
```lean
open Sparkle16

-- Create an instruction
let instr := Instruction.LDI ⟨1, by omega⟩ 0x42

-- Encode to machine code
let encoded := Instruction.encode instr  -- Returns BitVec 16

-- Decode back
let decoded := Instruction.decode encoded  -- Returns some instr

-- Display
#eval instr.toString  -- "LDI R1, 66"
```

### 2. ALU (ALU.lean)

Arithmetic Logic Unit performing:
- **ADD**: 16-bit addition
- **SUB**: 16-bit subtraction
- **AND**: 16-bit bitwise AND

**Interface:**
```systemverilog
module ALU (
    input  logic [2:0] opcode,
    input  logic [15:0] a, b,
    output logic [15:0] result,
    output logic zero
);
```

**Features:**
- Combinational logic (no registers)
- All operations computed in parallel
- Mux selects result based on opcode
- Zero flag indicates result == 0

**Generate Verilog:**
```bash
lake env lean --run Examples/Sparkle16/ALU.lean
```

### 3. Register File (RegisterFile.lean)

8-register file with special R0 behavior:

**Interface:**
```systemverilog
module RegisterFile (
    input  logic clk, rst,
    input  logic we,                  // Write enable
    input  logic [2:0] rd_addr, wr_addr,
    input  logic [15:0] wr_data,
    output logic [15:0] rd_data
);
```

**Features:**
- R0 hardwired to 0 (cannot be written)
- R1-R7 are 16-bit writable registers
- Single read port (asynchronous)
- Single write port (synchronous on clk)
- Reset clears all registers to 0

**Implementation:**
- Each register (R1-R7) has conditional write enable
- 8-way mux tree for read selection
- Proper feedback to maintain register state

**Generate Verilog:**
```bash
lake env lean --run Examples/Sparkle16/RegisterFile.lean
```

## Formal Verification

### Verification Framework (Sparkle/Verification/)

#### Basic.lean

Fundamental lemmas about BitVec operations:
- **Commutativity**: `bitvec_add_comm`, `bitvec_and_comm`, etc.
- **Associativity**: `bitvec_add_assoc`, `bitvec_and_assoc`, etc.
- **Identity elements**: `bitvec_add_zero`, `bitvec_or_zero`, etc.
- **De Morgan's Laws**: `bitvec_not_and`, `bitvec_not_or`
- **Bit manipulations**: Extensions, truncations, shifts

#### ALUProps.lean

Correctness proofs for ALU operations:

**Proven Theorems:**
1. `alu_add_correct`: ADD operation matches mathematical addition
2. `alu_sub_correct`: SUB operation matches mathematical subtraction
3. `alu_and_correct`: AND operation matches bitwise AND
4. `alu_zero_flag_correct`: Zero flag is set iff result is zero
5. `alu_deterministic`: Same inputs always produce same output
6. `alu_add_comm`: Addition is commutative
7. `alu_add_assoc`: Addition is associative
8. `alu_and_comm`: AND is commutative
9. `alu_preserves_width`: All operations preserve 16-bit width

**Example:**
```lean
import Sparkle.Verification.ALUProps

-- Prove that ADD is correct
theorem my_add_proof (a b : BitVec 16) :
    aluSpec .ADD a b = a + b := by
  apply alu_add_correct
```

## Building and Testing

### Prerequisites

- Lean 4 (v4.26.0 or later)
- Lake (Lean build tool)

### Build

```bash
# Build entire project
lake build

# Build and test ALU
lake env lean --run Examples/Sparkle16/ALU.lean

# Build and test RegisterFile
lake env lean --run Examples/Sparkle16/RegisterFile.lean
```

### Generated Verilog

Running the examples generates SystemVerilog files:
- `ALU.sv` - Arithmetic Logic Unit
- `RegisterFile.sv` - 8-register file

These files are synthesizable and can be used in FPGA or ASIC flows.

## Project Structure

```
Examples/Sparkle16/
├── ISA.lean           # Instruction set definitions
├── ALU.lean           # Arithmetic Logic Unit
├── RegisterFile.lean  # 8-register file
└── README.md          # This file

Sparkle/Verification/
├── Basic.lean         # Fundamental BitVec lemmas
└── ALUProps.lean      # ALU correctness proofs
```

## Design Principles

1. **Simplicity**: Single-cycle execution, no complex pipelining
2. **Formal Verification**: Proofs alongside implementation
3. **Modularity**: Components can be tested independently
4. **Clear Mapping**: Hardware directly corresponds to Lean code
5. **Type Safety**: Lean's type system prevents many HDL bugs

## Future Work

### Near Term
- **Memory Interface**: Instruction and data memory modules
- **CPU Core**: State machine integrating all components
- **Control Unit**: Fetch-decode-execute FSM
- **Test Programs**: Assembly programs for validation

### Extended Features
- **More Instructions**: OR, XOR, SLT (set less than), shifts
- **Branch Prediction**: Simple static prediction
- **Pipeline**: 3-stage pipeline (Fetch, Decode, Execute)
- **Interrupts**: Basic interrupt handling
- **Formal Proofs**: State machine invariants, ISA correctness

### Verification Goals
- Prove R0 always reads as 0
- Prove PC increments correctly (except branches)
- Prove instruction decode is bijective
- Prove register writes are isolated (no crosstalk)
- Prove memory safety (bounds checking)

## Example Usage

### Encoding Instructions

```lean
import Sparkle16.ISA

open Sparkle16

-- LDI R1, 42
let ldi := Instruction.LDI ⟨1, by omega⟩ 42
let encoded := Instruction.encode ldi
-- encoded = 0b000_001_00101010_00

-- ADD R2, R1, R3
let add := Instruction.ADD ⟨2, by omega⟩ ⟨1, by omega⟩ ⟨3, by omega⟩
#eval Instruction.encode add

-- BEQ R1, R2, 5
let beq := Instruction.BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 5
#eval beq.toString  -- "BEQ R1, R2, 5"
```

### Verifying ALU

```lean
import Sparkle.Verification.ALUProps

open Sparkle.Verification.ALUProps

-- Prove commutativity
example (a b : BitVec 16) : aluSpec .ADD a b = aluSpec .ADD b a := by
  apply alu_add_comm

-- Prove associativity
example (a b c : BitVec 16) :
    aluSpec .ADD (aluSpec .ADD a b) c = aluSpec .ADD a (aluSpec .ADD b c) := by
  apply alu_add_assoc
```

## Contributing

This is an educational project demonstrating:
- **Functional HDL design** in Lean 4
- **Formal verification** of hardware
- **Hardware synthesis** to SystemVerilog
- **Type-safe hardware development**

Contributions welcome! Areas of interest:
- Additional CPU instructions
- Pipelining
- Memory system
- More formal proofs
- Test programs
- Documentation

## References

- [Sparkle HDL Documentation](../../README.md)
- [RISC-V Specification](https://riscv.org/specifications/) (inspiration)
- [Computer Organization and Design](https://www.elsevier.com/books/computer-organization-and-design-risc-v-edition/patterson/978-0-12-820331-6) by Patterson & Hennessy

## License

MIT

---

**Status**: Foundation Complete ✓
- ISA defined with encode/decode
- ALU implemented and tested
- RegisterFile implemented with R0=0
- Verification framework established
- Basic proofs completed

**Next Steps**: CPU Core integration, memory system, test programs
