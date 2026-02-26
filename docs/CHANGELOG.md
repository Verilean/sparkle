# Sparkle HDL Development History

This document tracks the development phases and implementation milestones of Sparkle HDL.

## Phase 9: Auto-Generate SystemVerilog from SoC.lean (Complete)

**Date**: 2026-02-27

**Goal**: Make `#synthesizeVerilog` generate SystemVerilog from the RV32IMA SoC (`SoC.lean`) that matches the hand-written `verilator/rv32i_soc.sv`.

**Compiler Enhancements**:
- Added `memoryComboRead` support (combo read codegen: `assign readData = mem[readAddr]`)
- `unfoldDefinition?` instead of `whnf` — prevents exponential blowup on 119-register tuple projections
- Diagnostic error messages for unsupported constructs

**SoC Bug Fixes Ported from Hand-Written SV**:
- Bug #1: `exwb_physAddr` register (WB bus decode uses physical address)
- Bug #2: `holdEX` mechanism (freeze EX when DMEM port hijacked by pending write)
- Bug #3: `fetchPC` flush logic (`flush ? pcNext : (stall ? fetchPC : pcReg)`)

**Synthesizable Variant**:
- `Examples/RV32/SoCVerilog.lean` — `rv32iSoCSynth` with external IMEM/DMEM write ports
- `mulComputeSignal` — synthesizable 64-bit multiply for MUL/MULH/MULHSU/MULHU
- `amoComputeSignal` — Signal.mux chains replacing non-synthesizable match/if-then-else
- Multi-cycle restoring divider integration (divPending, divStall, holdEX gating, abort on flush)

**Result**: `#synthesizeVerilog rv32iSoCSynth` succeeds — 9 modules, 119 registers.

**Files Modified**:
- `Sparkle/IR/AST.lean` — `comboRead` flag on `Stmt.memory`
- `Sparkle/IR/Builder.lean` — `emitMemoryComboRead`
- `Sparkle/Compiler/Elab.lean` — `memoryComboRead` pattern, `unfoldDefinition?` fix
- `Sparkle/Backend/Verilog.lean` — Combo read codegen
- `Examples/RV32/SoC.lean` — 3 bug fixes, divider integration (117→119 registers)
- `Examples/RV32/SoCVerilog.lean` — Synthesizable variant with `#synthesizeVerilog`
- `Examples/RV32/Core.lean` — `mulComputeSignal`, `amoComputeSignal`
- `Examples/RV32/Divider.lean` — `abort` parameter

## Phase 8: Linux Kernel Boot (Complete)

**Goal**: Boot Linux 6.6.0 on the Sparkle RV32IMA SoC via OpenSBI v0.9

**Result**: Linux 6.6.0 boots, printing 3944 UART bytes in ~7M cycles. Kernel panic in `kmem_cache_init` (SLUB allocator NULL pointer dereference) — deep into early kernel init.

**Key Output**:
```
Linux version 6.6.0 ... #6 Thu Feb 26 06:29:23 UTC 2026
Machine model: Sparkle RV32IMA SoC
Memory: 26208K/28672K available
```

**SoC Additions**:
- mcounteren + scounteren CSR registers (115-116)
- PMP CSR stubs (0x3A0-0x3EF return 0)
- MRET decoder fix (`funct3 == 0` check)

**3 Critical Pipeline Bug Fixes** (in `verilator/rv32i_soc.sv`):

1. **WB bus decode used virtual address**: Added `exwb_physAddr` pipeline register. All WB-stage bus decode now uses physical address.
2. **pendingWriteEn hijacks DMEM address**: Added `holdEX` mechanism — freezes ID/EX registers and suppresses EX/WB side-effects during `pendingWriteEn`.
3. **Stale fetchPC after flush**: `fetchPC_next = flush ? pcReg_next : (stall ? fetchPC : pcReg)` — fetchPC immediately points to flush target.

**Verilator Testbench**:
- `--payload` flag for loading kernel binary at 0x80400000
- Device tree `bootargs = "earlycon=sbi console=ttyS0"`

**Files Modified**:
- `verilator/rv32i_soc.sv` — Pipeline fixes, CSRs, PMP stubs
- `verilator/tb_soc.cpp` — `--payload` flag
- `Examples/RV32/SoC.lean` — CSR registers, MRET fix
- `firmware/sparkle-soc.dts` — bootargs

## Phase 7: Example CPU & Formal Verification (Complete)

**Goal**: Demonstrate real-world hardware design with formal verification

**Completed Components**:
- **Sparkle-16 CPU**: 16-bit RISC processor with 8 instructions
- **ISA Definition**: Complete instruction encoding/decoding (LDI, ADD, SUB, AND, LD, ST, BEQ, JMP)
- **ALU**: Arithmetic Logic Unit with 9 formal correctness proofs
- **Register File**: 8 registers with R0 hardwired to zero
- **Memory Interface**: Instruction/data memory with SimMemory and SRAM modules
- **CPU Core**: Complete fetch-decode-execute state machine with simulation
- **Verification Framework**: ISA correctness, ALU proofs, instruction classification
- **Example Programs**: Arithmetic operations and control flow demonstrations

**Verification Status**:
- ALU correctness proven (9 theorems)
- ISA opcode correctness (encode/decode bijection)
- ISA instruction classification (branches, register writes)

**Files Added**:
- `Examples/Sparkle16/ISA.lean` - Instruction set architecture
- `Examples/Sparkle16/ALU.lean` - Arithmetic Logic Unit
- `Examples/Sparkle16/RegisterFile.lean` - 8-register file
- `Examples/Sparkle16/Memory.lean` - Memory interface
- `Examples/Sparkle16/Core.lean` - CPU core with state machine
- `Examples/Sparkle16/ISAProofTests.lean` - ISA correctness tests
- `Sparkle/Verification/Basic.lean` - Fundamental BitVec lemmas
- `Sparkle/Verification/ALUProps.lean` - ALU correctness proofs
- `Sparkle/Verification/ISAProps.lean` - ISA encoding/decoding correctness

## Phase 6: Primitive Module Support (Complete)

**Goal**: Support vendor-specific blackbox modules (ASIC/FPGA primitives)

**Implementation**:
- **Blackbox Support**: Declare technology-specific modules without defining them
- **Vendor Integration**: Support for ASIC/FPGA vendor libraries (TSMC, Intel, Xilinx, etc.)
- **Common Primitives**: Helper functions for SRAM, ROM, clock gating cells
- **Module Instantiation**: Seamless instantiation of primitive modules

**Files Added**:
- `Sparkle/Primitives.lean` - Primitive module support
- `Examples/PrimitiveTest.lean` - SRAM and clock gating examples

## Phase 5: Feedback Loops (Complete)

**Goal**: Enable stateful circuits with feedback paths

**Implementation**:
- **Signal.loop Primitive**: Fixed-point combinator for feedback loops
- **Counter Support**: Enable circuits where output feeds back to input
- **State Machines**: Support for stateful hardware designs
- **Loop Closure**: Automatic wire allocation and connection for feedback paths

**Files Added**:
- `Examples/LoopSynthesis.lean` - Feedback loop examples

## Phase 4: Verilog Backend (Complete)

**Goal**: Generate synthesizable SystemVerilog from IR

**Implementation**:
- Clean, synthesizable SystemVerilog output matching hand-written style
- Type mapping: Lean types → Verilog types (logic, bit, packed arrays)
- Operator mapping: IR operators → Verilog syntax
- Proper always_ff blocks with reset

**Files Added**:
- `Sparkle/Backend/Verilog.lean` - SystemVerilog code generator
- `Examples/VerilogTest.lean` - Verilog generation examples
- `Examples/FullCycle.lean` - Advanced examples (MAC, FIR filter, traffic light, FIFO)

## Phase 3: Compiler (Complete)

**Goal**: Automatically compile Lean code to hardware IR

**Implementation**:
- Primitive registry mapping Lean functions to hardware operators
- `#synthesize` and `#synthesizeVerilog` commands
- Automatic clock/reset detection from registers

**Files Added**:
- `Sparkle/Compiler/Elab.lean` - Metaprogramming compiler
- `Examples/SynthesisTest.lean` - Automatic synthesis examples

## Phase 2: Netlist IR (Complete)

**Goal**: Create a compositional intermediate representation for hardware

**Implementation**:
- Hardware types (Bit, BitVector, Array), AST, Circuit builder monad (`CircuitM`)
- All standard operators (arithmetic, logical, bitwise, comparison, mux, concat, slice)

**Files Added**:
- `Sparkle/IR/Type.lean`, `Sparkle/IR/AST.lean`, `Sparkle/IR/Builder.lean`

## Phase 1: Simulation (Complete)

**Goal**: Cycle-accurate functional simulation of hardware

**Implementation**:
- Domain configuration, stream-based signals (`Signal d α ≈ Nat → α`)
- Hardware primitives: `register`, `registerWithEnable`, `mux`, bundling
- Functor/Applicative/Monad instances for Signal

**Files Added**:
- `Sparkle/Core/Domain.lean`, `Sparkle/Core/Signal.lean`, `Sparkle/Data/BitPack.lean`
