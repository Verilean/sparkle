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

### 4. CPU Core (Core.lean)

Complete CPU implementation integrating all components:

**Features:**
- **Fetch-Decode-Execute** state machine
- **3-phase pipeline**: Fetch, Decode, Execute
- **Harvard architecture**: Separate instruction and data memory
- **Single-cycle execution**: Simplified design for clarity
- **Memory interface**: SimMemory for simulation
- **Full ISA support**: All 8 instructions implemented

**CPU State:**
```lean
structure CPUState where
  pc : Word                    -- Program counter
  regs : Fin 8 → Word         -- Register file (functional)
  phase : Phase                -- Current execution phase
  instr : Option Instruction   -- Currently decoded instruction
  memData : Word               -- Data from memory load
```

**Execution Phases:**
1. **Fetch**: Read instruction from instruction memory at PC
2. **Decode**: Parse instruction fields (opcode, registers, immediates)
3. **Execute**: Perform operation, update registers, PC, or memory

**Run CPU Simulation:**
```bash
lake env lean --run Examples/Sparkle16/Core.lean
```

**Example Output:**
```
=== Sparkle-16 CPU Core ===

Example 1: Simple arithmetic
Program:
  LDI R1, 10
  LDI R2, 20
  ADD R3, R1, R2
  SUB R4, R3, R1

After 12 cycles:
PC=4 Phase=Fetch Instr=None
R0=0x0000#16 R1=0x000a#16 R2=0x0014#16 R3=0x001e#16
R4=0x0014#16 R5=0x0000#16 R6=0x0000#16 R7=0x0000#16

✓ All values correct!
```

**Implementation Details:**
- Pure functional execution semantics (`executeInstruction`)
- Separate memory handling for LD/ST instructions
- R0 always reads as 0, writes ignored
- Branch instructions update PC directly
- Jump instruction sets PC to absolute address

### 5. Memory Interface (Memory.lean)

Provides both simulation and synthesis-level memory:

**SimMemory (for testing):**
- Functional array model (256 words × 16 bits)
- Synchronous read/write operations
- Address wrapping for bounds safety

**Hardware Modules (for synthesis):**
- `instructionMemoryModule`: Read-only SRAM for instructions
- `dataMemoryModule`: Read/write SRAM for data
- Uses vendor SRAM primitives (SRAM_256x16)

**Run Memory Tests:**
```bash
lake env lean --run Examples/Sparkle16/Memory.lean
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

#### ISAProps.lean

ISA correctness proofs for instruction encoding/decoding:

**Proven Theorems:**
1. `opcode_encode_decode`: Opcode encoding is bijective (all opcodes roundtrip)
2. `opcode_decode_total`: Every 3-bit value maps to an opcode
3. `writes_has_dest`: Instructions that write have a destination register
4. `branch_no_write`: Branch instructions don't write to registers
5. `encode_preserves_dest`: Encoding preserves destination registers
6. `encode_decode_id`: Full instruction encode/decode roundtrip (in progress)

**Example:**
```lean
import Sparkle.Verification.ISAProps

-- Prove opcode roundtrip
example : Opcode.fromBitVec (Opcode.toBitVec Opcode.ADD) = some Opcode.ADD :=
  opcode_encode_decode Opcode.ADD

-- Prove branch instructions don't write
example (instr : Instruction) (h : instr.isBranch = true) :
    instr.writesRegister = false :=
  branch_no_write instr h
```

**Test ISA Proofs:**
```bash
lake env lean --run Examples/Sparkle16/ISAProofTests.lean
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

# Build and test Memory
lake env lean --run Examples/Sparkle16/Memory.lean

# Run CPU Core simulation
lake env lean --run Examples/Sparkle16/Core.lean
```

### Generated Verilog

Running the examples generates SystemVerilog files:
- `ALU.sv` - Arithmetic Logic Unit
- `RegisterFile.sv` - 8-register file
- `InstructionMemory.sv` - Instruction memory (SRAM)
- `DataMemory.sv` - Data memory (SRAM)

These files are synthesizable and can be used in FPGA or ASIC flows.

## Project Structure

```
Examples/Sparkle16/
├── ISA.lean            # Instruction set definitions
├── ALU.lean            # Arithmetic Logic Unit
├── RegisterFile.lean   # 8-register file
├── Memory.lean         # Memory interface (instruction & data)
├── Core.lean           # Complete CPU core with state machine
├── ISAProofTests.lean  # ISA correctness proof tests
└── README.md           # This file

Sparkle/Verification/
├── Basic.lean          # Fundamental BitVec lemmas
├── ALUProps.lean       # ALU correctness proofs
└── ISAProps.lean       # ISA encoding/decoding correctness
```

## Design Principles

1. **Simplicity**: Single-cycle execution, no complex pipelining
2. **Formal Verification**: Proofs alongside implementation
3. **Modularity**: Components can be tested independently
4. **Clear Mapping**: Hardware directly corresponds to Lean code
5. **Type Safety**: Lean's type system prevents many HDL bugs

## Future Work

### Near Term
- **Test Programs**: More comprehensive assembly programs for validation
- **ISA Correctness Proofs**: Encode/decode bijectivity, instruction semantics
- **State Machine Proofs**: PC increment correctness, phase transitions
- **Hardware Synthesis**: Generate complete CPU Verilog (currently simulation-only)

### Extended Features
- **More Instructions**: OR, XOR, SLT (set less than), shifts, rotates
- **Branch Prediction**: Simple static or dynamic prediction
- **Pipeline**: Multi-stage pipeline with hazard detection
- **Interrupts**: Basic interrupt handling and exception support
- **Cache**: Simple instruction/data caches

### Verification Goals
- ✅ Prove ALU operations are correct
- ⏳ Prove R0 always reads as 0
- ⏳ Prove PC increments correctly (except branches)
- ⏳ Prove instruction decode is bijective
- ⏳ Prove register writes are isolated (no crosstalk)
- ⏳ Prove memory safety (bounds checking)
- ⏳ Prove state machine invariants hold

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

**Status**: CPU Core Complete ✓

**Completed Components:**
- ✅ ISA defined with encode/decode
- ✅ ALU implemented with formal correctness proofs
- ✅ RegisterFile implemented with R0=0 invariant
- ✅ Memory interface (simulation and hardware modules)
- ✅ CPU Core with fetch-decode-execute state machine
- ✅ Verification framework with BitVec lemmas
- ✅ Example programs demonstrating all instruction types

**Verification Status:**
- ✅ ALU correctness proven (9 theorems)
- ✅ ISA opcode correctness (encode/decode bijection)
- ✅ ISA instruction classification (branches, register writes)
- ⏳ Full instruction encode/decode bijectivity (in progress)
- ⏳ State machine invariants
- ⏳ R0=0 invariant
- ⏳ Memory safety proofs

**Next Steps**:
- Complete full instruction encode/decode roundtrip proofs
- State machine verification (phase transitions, PC increment)
- R0=0 invariant proof
- Hardware synthesis for complete CPU
- More comprehensive test programs
