# Sparkle HDL Development History

This document tracks the development phases and implementation milestones of Sparkle HDL.

## Phase 12: LSpec Flow Tests for RV32 SoC (Complete)

**Date**: 2026-03-02

**Goal**: Add automated LSpec tests covering the full RV32 SoC build/simulation pipeline — Verilog compilation, Lean-native simulation, CppSim JIT, and Verilator simulation. Catch regressions early, skip gracefully when external tools are unavailable.

**Result**: 18 test assertions across 4 categories, all passing. Integrated into `lake test` and available standalone via `lake exe rv32-flow-test`.

**Test Categories**:
1. **Verilog Compilation** (12 tests): Verifies `generated_soc.sv` has module declaration, clock input, `always_ff`, imem write enable; `generated_soc_cppsim.h` has class declaration, `eval()`/`tick()`/`reset()` methods
2. **Lean-native Simulation** (1 test): Runs `rv32iSoCSimulateFull` via subprocess (`LeanSimRunner.lean`); skips gracefully on macOS (8MB stack limit, exit code 134 detection)
3. **CppSim JIT** (3 tests): Detects `clang++`/`g++`, compiles `tb_cppsim.cpp`, runs 5000 cycles, checks `ALL TESTS PASSED`
4. **Verilator** (3 tests): Detects `verilator`, builds via `make obj_dir/Vrv32i_soc`, runs 5000 cycles, checks `ALL TESTS PASSED`

**Design Decisions**:
- Lean simulation runs as a subprocess to work around macOS 8MB stack limit (122-register SoC body causes stack overflow on main thread)
- Stack overflow (exit code 134) treated as skip, not failure — it's an environment limitation
- Uses `which` for tool detection (same pattern as `Tests/Sparkle16/TestCoSim.lean`)
- Verilator build uses `obj_dir/Vrv32i_soc` target (not `build`) to avoid re-generating SV

**Files Added**:
- `Tests/RV32/TestFlow.lean` — All 4 test categories (`synthTests`, `leanSimTests`, `cppSimTests`, `verilatorTests`)
- `Tests/RV32/TestFlowMain.lean` — Standalone `main` entry point (separated from TestFlow to avoid `main` conflict with AllTests)
- `Tests/RV32/LeanSimRunner.lean` — Subprocess for Lean-native simulation

**Files Modified**:
- `Tests/AllTests.lean` — Added `import Tests.RV32.TestFlow`, integrated `flowTests` into `allTests`
- `lakefile.lean` — Added `rv32-flow-test` and `rv32-lean-sim-runner` executable targets

## Phase 11: CppSim Benchmark — IR Optimization + End-to-End Simulation (Complete)

**Date**: 2026-03-02

**Goal**: Make CppSim compile and run on the RV32I SoC, benchmark against Verilator, and optimize to beat Verilator's performance.

**Result**: CppSim runs firmware test correctly (47/47 UART words match Verilator, `0xCAFE0000` at cycle 2904). **~170x faster** than Verilator for the firmware test workload. Sustained throughput: 3.6M cycles/sec.

**IR Optimization Pass** (`Sparkle/IR/Optimize.lean`):
- Eliminates nested concat/slice chains from tuple packing/unpacking
- Recursive `resolveSlice` follows ref aliases, composes slice-of-slice, resolves slice-of-concat
- Uses `Std.HashMap` for O(1) lookups (critical for 10K+ wire designs)
- Fuel=500 to handle 244-level deep chains (124 slice + 120 concat)
- Dead-code elimination removes unused wires and assigns
- Result: 20,543 → 4,919 lines (76% reduction)

**CppSim Backend Enhancements** (`Sparkle/Backend/CppSim.lean`):
- Wide types (>64-bit): `std::array<uint32_t, N>` declarations, assigns skipped (dead after optimization)
- No wide-type expressions remain in generated code after IR optimization

**Combined `#writeDesign` Command** (`Sparkle/Compiler/Elab.lean`):
- Single `synthesizeHierarchical` call emits both Verilog and optimized CppSim
- Prevents 2x synthesis overhead from separate commands

**C++ Testbench** (`verilator/tb_cppsim.cpp`):
- Firmware loaded directly into IMEM array (no CPU cycles consumed)
- Heap allocation for SoC (8MB DRAM arrays exceed stack)
- UART monitoring, halt detection, timing measurement

**Files Added**:
- `Sparkle/IR/Optimize.lean` — IR optimization pass (~200 lines)
- `verilator/tb_cppsim.cpp` — CppSim testbench (~150 lines)

**Files Modified**:
- `Sparkle/Backend/CppSim.lean` — >64-bit type handling, wide assign skip
- `Sparkle/Compiler/Elab.lean` — `#writeDesign` combined command, imports
- `Sparkle.lean` — Added `import Sparkle.IR.Optimize`
- `Examples/RV32/SoCVerilog.lean` — `#writeDesign` with both output paths
- `verilator/Makefile` — CppSim build targets

## Phase 10: C++ Simulation Backend (Complete)

**Date**: 2026-03-01

**Goal**: Generate C++ simulation code from IR (`Module`/`Design`), producing a C++ class with `eval()`/`tick()`/`reset()` methods. Phase 1 — purely string generation (no compilation or FFI).

**Implementation**:
- **CppSim backend**: Mirrors `Verilog.lean` structure — same IR traversal, C++ target
- **Type mapping**: `HWType` → `uint8_t`/`uint16_t`/`uint32_t`/`uint64_t`/`std::array<T,N>`
- **Expression translation**: constants as `(uint32_t)42ULL`, signed ops via `(int32_t)` casts, concat as shift+OR chain, slice as `(expr >> lo) & mask`
- **Statement splitting**: `StmtParts` structure separates declarations/eval/tick/reset
- **Sub-module instantiation**: resolves input/output ports via `Design` lookup
- **Masking**: applied at assignment for non-native widths (∉ {8,16,32,64})

**Tests**: 25 tests across 4 modules — counter (10 tests), combo-read memory (5), combinational ops (5), registered memory (3). Verified via `String.containsSubstr` checks on generated C++.

**Files Added**:
- `Sparkle/Backend/CppSim.lean` — C++ simulation code generator (~280 lines)
- `Tests/TestCppSim.lean` — Test suite (25 tests)

**Files Modified**:
- `Sparkle.lean` — Added `import Sparkle.Backend.CppSim`
- `Tests/AllTests.lean` — Added `import Tests.TestCppSim`, integrated `cppSimTests`

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
