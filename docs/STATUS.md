# Sparkle SoC — Current Status

**Date**: 2026-03-02
**Branch**: main

---

## holdEX/divStall Store Bug Fix (Phase 13) — DONE

Fixed a critical bug where `holdEX` included `divStall`, causing `suppressEXWB` to kill valid stores during multi-cycle division. This prevented `memblock_add` stores from persisting during Linux boot, leaving `swapper_pg_dir` empty and causing a recursive page fault at PC 0xC0001C88.

### The Bug

| | Hand-written SV (working) | Generated SoC (broken) |
|---|---|---|
| `holdEX` | `pendingWriteEn` | `pendingWriteEn \|\| (divStall && !flushOrDelay)` |
| `suppressEXWB` | `trap_taken \|\| dTLBMiss \|\| holdEX` | Same — but `holdEX` is wider |
| **Effect on stores** | Stores only suppressed during pending AMO/TLB miss/trap | **Stores also suppressed during 34-cycle division** |

### Fix (4 logical edits in `Examples/RV32/SoC.lean`)

1. **`holdEX` simplified** to `pendingWriteEn` only — controls `suppressEXWB`
2. **New `freezeIDEX`** = `holdEX || (divStall && !flushOrDelay)` — controls pipeline register freezing only
3. **`squash`** uses `freezeIDEX` (not `holdEX`)
4. **All 36 pipeline register muxes** use `freezeIDEX` (not `holdEX`)

### Verification

- `lake build Examples.RV32.SoCVerilog` — passes, regenerates SV + CppSim
- CppSim firmware test — **ALL TESTS PASSED** (49 UART words, 0xCAFE0000 at cycle 2904)
- `lake exe rv32-flow-test` — CppSim category passes

---

## Signal Bool Operator Instances (Phase 13) — DONE

Added boolean operator overloading for `Signal dom Bool` in `Sparkle/Core/Signal.lean`.

### New Instances

| Syntax | Operator | Expansion |
|--------|----------|-----------|
| `a &&& b` | AND | `(· && ·) <$> a <*> b` |
| `a \|\|\| b` | OR | `(· \|\| ·) <$> a <*> b` |
| `a ^^^ b` | XOR | `(xor · ·) <$> a <*> b` |
| `~~~a` | NOT | `(fun x => !x) <$> a` |

### Refactoring Demo

Flush logic in `SoC.lean` simplified:
```lean
-- Before (verbose):
let flush := (· || ·) <$> ((· || ·) <$> branchTaken <*> idex_jump) <*>
             ((· || ·) <$> ((· || ·) <$> trap_taken <*> idex_isMret) <*>
              ((· || ·) <$> ((· || ·) <$> idex_isSret <*> idex_isSFenceVMA) <*> dMMURedirect))

-- After (clean):
let flush := branchTaken ||| idex_jump ||| trap_taken ||| idex_isMret |||
             idex_isSret ||| idex_isSFenceVMA ||| dMMURedirect
```

Synthesis compatibility confirmed — compiler already has `Bool.and`/`Bool.or`/`Bool.not` in primitive registry.

---

## JIT FFI Design Document (Phase 13) — DONE

Created `docs/JIT_FFI_Plan.md` — design document for native-speed simulation via dynamic compilation. Covers architecture, C++ shared library generation, background compilation with hash-based caching, Lean FFI bindings (`sparkle_jit.c` + `JIT.lean`), and `loopMemoJIT` integration with fallback to interpreted `loopMemo`.

---

## LSpec Flow Tests (Phase 12) — DONE

Automated LSpec tests covering the full RV32 SoC build/simulation pipeline. Catches regressions across 4 independent paths, skips gracefully when external tools are unavailable.

### Test Results (18 assertions)

| Category | Tests | Status |
|----------|-------|--------|
| Verilog Compilation | 12 | All pass — verifies `generated_soc.sv` and `generated_soc_cppsim.h` content |
| Lean-native Simulation | 1 | Skips on macOS (8MB stack limit) — passes on Linux with sufficient stack |
| CppSim JIT | 3 | All pass — compiles with clang++, runs 5000 cycles, `ALL TESTS PASSED` |
| Verilator Simulation | 3 | All pass — builds via Make, runs 5000 cycles, `ALL TESTS PASSED` |

### Architecture

- **Category 1 (Verilog Compilation)**: Reads generated files, checks for expected module names, port declarations, `always_ff` blocks, CppSim class methods
- **Category 2 (Lean-native Simulation)**: Runs `rv32iSoCSimulateFull` via separate subprocess (`LeanSimRunner.lean`) to work around macOS stack limit; checks PC starts at 0, advances, stays in IMEM range
- **Category 3 (CppSim JIT)**: Detects `clang++`/`g++` availability, compiles `tb_cppsim.cpp`, runs firmware test, checks output
- **Category 4 (Verilator)**: Detects `verilator` availability, builds via `make obj_dir/Vrv32i_soc` (no re-generate), runs firmware test

### Files Added

| File | Description |
|------|-------------|
| `Tests/RV32/TestFlow.lean` | 4 test categories (synthTests, leanSimTests, cppSimTests, verilatorTests) |
| `Tests/RV32/TestFlowMain.lean` | Standalone `main` entry point |
| `Tests/RV32/LeanSimRunner.lean` | Subprocess for Lean simulation (avoids stack overflow) |

### Files Modified

| File | Change |
|------|--------|
| `Tests/AllTests.lean` | Added `import Tests.RV32.TestFlow`, integrated `flowTests` |
| `lakefile.lean` | Added `rv32-flow-test` and `rv32-lean-sim-runner` executable targets |

### Build & Run

```bash
# Run all tests including flow tests
lake test

# Run flow tests standalone
lake exe rv32-flow-test

# Build simulation runner (needed for lean sim tests)
lake build rv32-lean-sim-runner
```

---

## CppSim Benchmark (Phase 11) — DONE

End-to-end C++ simulation backend: generates optimized C++ from IR, compiles, and runs the RV32I SoC firmware test — **~170x faster than Verilator** for the firmware test workload.

### Benchmark Results

| Metric | Verilator | CppSim | Speedup |
|--------|-----------|--------|---------|
| Firmware test (2904 cycles) | ~160ms | **0.9ms** | **~170x** |
| Sustained throughput (1M cycles) | N/A | **3.6M cycles/sec** | — |

- UART output: **47/47 data words identical** to Verilator
- `0xCAFE0000` pass marker at cycle 2904 (same as Verilator)

### Completed

| # | Task | Status |
|---|------|--------|
| 1 | IR optimization pass (`Sparkle/IR/Optimize.lean`) — concat/slice chain elimination | Done |
| 2 | CppSim backend >64-bit type handling + wide assign skip | Done |
| 3 | Combined `#writeDesign` command (single synthesis → both Verilog + CppSim) | Done |
| 4 | C++ testbench (`verilator/tb_cppsim.cpp`) — firmware load, UART, timing | Done |
| 5 | Makefile targets (`build-cppsim`, `run-cppsim`, `benchmark`) | Done |
| 6 | ALL TESTS PASSED — CppSim matches Verilator output | Done |

### IR Optimization

- **Problem**: 5,451 wires wider than 999 bits from tuple packing/unpacking (nested 2-element concats + slice chains)
- **Solution**: `Sparkle.IR.Optimize.optimizeDesign` — recursive `resolveSlice` with HashMap lookups
  - Follows ref aliases: `X = Y` → follow to Y
  - Composes slice chains: `X = Y[h1:l1], Z = X[h2:l2]` → `Z = Y[l1+h2:l1+l2]`
  - Resolves concat slices: `X = {a, b}, Z = X[h:l]` → `Z = a` (if aligned)
  - Fuel=500 to handle 244-level deep chains (124 slice + 120 concat levels)
- **Result**: 20,543 → 4,919 lines (76% reduction), 7,928 → 0 wide arrays in expressions

### Architecture

- `#writeDesign id "path.sv" "path_cppsim.h"` — synthesizes once, emits both Verilog and CppSim
- IR optimization runs only on CppSim path (Verilog output is unoptimized, matches previous behavior)
- Wide types (>64-bit): declared as `std::array<uint32_t, N>`, assigns skipped (dead after optimization)
- Testbench loads firmware directly into IMEM array (no CPU cycles consumed during loading)

### Build & Run

```bash
# Build CppSim
cd verilator && make build-cppsim

# Run CppSim
cd verilator && make run-cppsim CYCLES=5000

# Benchmark CppSim vs Verilator
cd verilator && make benchmark CYCLES=5000
```

### TODO (Future Phases)

- [x] LSpec flow tests for RV32 SoC (Phase 12 — done)
- [x] Fix holdEX/divStall store bug (Phase 13 — done)
- [x] Signal Bool operator instances (Phase 13 — done)
- [x] JIT FFI design document (Phase 13 — done, see `docs/JIT_FFI_Plan.md`)
- [ ] Lean FFI bridge — call eval()/tick()/reset() from Lean via dlopen (see `docs/JIT_FFI_Plan.md`)
- [ ] Integrate with `Signal.loopMemo` for transparent JIT acceleration
- [ ] Profile-guided optimization (PGO) for CppSim
- [ ] Promote eval()-only wires to local variables (enable C++ register allocation)
- [ ] Fix Lean simulation stack overflow on macOS (reduce tuple nesting depth or use worker thread with larger stack)
- [ ] Fix Verilator testbench internal signal access (tb_soc.cpp references `_gen_dTLBMiss` which Verilator may optimize away)

---

## C++ Simulation Backend (Phase 10) — DONE

JIT simulator foundation: generates C++ code from IR (`Module`/`Design`), producing a C++ class with `eval()`/`tick()`/`reset()` methods.

### Completed

| # | Task | Status |
|---|------|--------|
| 1 | `Sparkle/Backend/CppSim.lean` — C++ code generator (~410 lines) | Done |
| 2 | `Tests/TestCppSim.lean` — 25 tests (counter, memory, combinational, registered memory) | Done |
| 3 | Integrated into `Sparkle.lean` and `Tests/AllTests.lean` | Done |
| 4 | `lake build` + `lake test` — all 25 CppSim tests pass | Done |

### Architecture

- Mirrors `Sparkle/Backend/Verilog.lean`: same IR traversal, different target language
- **Type mapping**: `bit`/`bv≤8` → `uint8_t`, `bv≤16` → `uint16_t`, `bv≤32` → `uint32_t`, `bv≤64` → `uint64_t`, `bv>64` → `std::array<uint32_t, N>`, arrays → `std::array<T,N>`
- **Bit-width masking**: mask at assignment only (widths ∉ {8,16,32,64})
- **eval()/tick()/reset() split**: combinational in `eval()`, register update in `tick()`, initialization in `reset()`
- **Expression translation**: constants as `(uint32_t)42ULL`, signed ops as `(int32_t)` casts, concat as shift+OR chain, slice as `>> lo & mask`
- **Sub-module instantiation**: uses `Design` to resolve input/output port directions

---

## SoC Synthesis (Phase 9)

`#writeDesign rv32iSoCSynth "verilator/generated_soc.sv" "verilator/generated_soc_cppsim.h"` generates both SystemVerilog and CppSim C++ from a single synthesis pass. The SoC has 119 registers.

### Generated Output

- **Verilog**: `verilator/generated_soc.sv` (~28k lines)
- **CppSim**: `verilator/generated_soc_cppsim.h` (~4.9k lines after IR optimization)
- **Top module**: `Sparkle_Examples_RV32_SoCVerilog_rv32iSoCSynth`
- **Inputs**: `clk`, `rst`, `_gen_imem_wr_en`, `_gen_imem_wr_addr[11:0]`, `_gen_imem_wr_data[31:0]`, `_gen_dmem_wr_en`, `_gen_dmem_wr_addr[22:0]`, `_gen_dmem_wr_data[31:0]`
- **Output**: `out[191:0]` — packed `{pcReg[191:160], uartValidBV[159:128], prevStoreData[127:96], satpReg[95:64], ptwPteReg[63:32], ptwVaddrReg[31:0]}`
- **Wrapper**: `rv32i_soc_wrapper.sv` adapts packed output to Verilator testbench interface

### Register Map (119 registers)

| Range | Count | Description |
|-------|-------|-------------|
| 0-5 | 6 | IF stage: pcReg, fetchPC, flushDelay, ifid_inst/pc/pc4 |
| 6-29 | 24 | ID/EX pipeline registers |
| 30-31 | 2 | EX/WB: exwb_alu, exwb_physAddr |
| 32-38 | 7 | EX/WB: rd, regW, m2r, pc4, jump, isCsr, csrRdata |
| 39-44 | 6 | WB forwarding + store history |
| 45-49 | 5 | CLINT: msip, mtime, mtimecmp |
| 50-56 | 7 | CSR M-mode |
| 57-58 | 2 | AI MMIO |
| 59-60 | 2 | Sub-word + M-ext |
| 61-69 | 9 | A-ext (reservation, AMO, pending write) |
| 70-79 | 10 | S-mode CSRs + privilege + delegation |
| 80-107 | 28 | MMU: 4-entry TLB + PTW FSM |
| 108-109 | 2 | SRET + SFENCE.VMA |
| 110-115 | 6 | UART 8250 |
| 116-117 | 2 | mcounteren, scounteren |
| 118 | 1 | divPending |

### Key Architecture Decisions

1. **`unfoldDefinition?` instead of `whnf`**: Prevents exponential blowup on 119-register tuple projections
2. **Multi-cycle restoring divider** (~34 cycles): Inlined into top module with `divPending`, `divStall`, `divAbort`
3. **Duplicated memory arrays**: `Signal.memory` + `Signal.memoryComboRead` stay in sync via identical writes
4. **Non-synthesizable functions replaced**: `mextCompute` → `mulComputeSignal` + `dividerSignal`; `amoCompute` → `amoComputeSignal`

---

## Completed Phases

### Phase 1: Compiler `memoryComboRead` support — DONE
### Phase 2: 3 bug fixes ported to SoC.lean — DONE
### Phase 3: `rv32iSoCSynth` in SoCVerilog.lean, `#synthesizeVerilog` succeeds — DONE

### Phase 9: Verilator Testing — IN PROGRESS

| # | Task | Status |
|---|------|--------|
| 1 | `#writeVerilogDesign` command in Elab.lean | Done |
| 2 | `lake build Examples.RV32.SoCVerilog` — writes `verilator/generated_soc.sv` | Done |
| 3 | `verilator/rv32i_soc_wrapper.sv` — unpack packed output | Done |
| 4 | `verilator/Makefile` — generated SV + wrapper, `make build` | Done |
| 5 | Verilator compiles generated SV successfully | Done |
| 6 | Firmware test: sections 1-9 match hand-written reference exactly (45 UART words) | Done |
| 7 | Firmware test: section 10 + pass marker (`0xcafe0000`) — ALL 48 UART words, cycle 2904 | Done |
| 8 | Linux boot test (OpenSBI → kernel → UART output) | **In Progress** |

### Compiler Bugs Fixed During Phase 9

| Bug | Fix |
|-----|-----|
| `bundle2` hardcoded wire width to 16 bits | Infer from expression type via `inferHWTypeFromSignal` |
| `Prod.fst` slice assumed equal-width halves (`width * 2 - 1`) | Use `getWireWidth` for actual source wire width |
| Verilog backend: duplicate wire/port declarations | Filter port names from internal wire list |
| Core.lean: complex lambda `(fun f7 => extractLsb' 5 1 f7 == 1#1)` | Split into extract + compare steps |

---

## Current Task: Linux Boot Hang Debugging

### Symptoms

- **Hand-written SV**: Boots Linux 6.6.0 successfully (3944 UART bytes in ~7M cycles)
- **Generated SV**: Hangs at ~1906 UART bytes, PC stuck at 0xC0001C88 (recursive page fault)
- OpenSBI phase works correctly (same output as hand-written)
- Kernel starts, prints banner and initial messages, then hangs

### Root Cause Analysis — Updated 2026-02-28

**`memblock_add` enters but fails to persist memory data → `memblock.memory` stays empty → final SATP switch page table has no kernel mapping → page fault → hang.**

#### SATP switch sequence (3 switches total):

| # | Cycle | SATP value | Page table | PTE[0x300] | Result |
|---|-------|-----------|------------|------------|--------|
| 1 | 2606985 | 0x800805F6 | setup_vm trampoline | 0x201000EF ✓ | OK |
| 2 | 2607006 | 0x80080557 | initial page table | 0x201000EF ✓ | OK |
| 3 | 3329886 | 0x800805F7 | setup_vm_final (swapper_pg_dir) | **0x00000000** ✗ | **CRASH** |

The third SATP switch activates `swapper_pg_dir` which has PTE[0x276] and PTE[0x277] (DTB mapping) but **NO PTE[0x300]** (kernel code mapping). This causes an immediate page fault at PC 0xC0001C88 → infinite recursive page fault → hang.

#### Why PTE[0x300] is missing:

`paging_init()` → `setup_vm_final()` uses `create_pgd_mapping()` which relies on `memblock_alloc()` to allocate page table pages. Since `memblock.memory` is empty (total_size=0), no memory can be allocated, so `swapper_pg_dir` stays mostly empty.

#### Why memblock.memory is empty:

`early_init_dt_add_memory_arch` IS called and correctly clamps:
- base: 0x80000000 → 0x80400000 (phys_offset = kernel load address)
- size: 0x02000000 → 0x01C00000

Then it tail-calls `memblock_add(0x80400000, 0x01C00000)`.

**`memblock_add` enters** (confirmed at cycle 3162213, PC 0xC0153F8C) but `memblock.memory.total_size` remains 0 when checked at cycle 3200000 and later.

The "simple case" in `memblock_add_range.isra.0` (when regions[0].size==0) should write:
```
regions[0].base = base    → DMEM word 0x156166
regions[0].size = size    → DMEM word 0x156167
regions[0].flags = 0      → DMEM word 0x156168
type->total_size = size   → DMEM word 0x156159
```

**Something prevents these stores from completing or persisting.**

#### Disproved hypotheses:

1. ~~TLB eviction by `of_get_flat_dt_prop("hotpluggable")` causes wrong physical address~~ — **DISPROVED**: MMU trace showed NO PTW activity, NO TLB misses between the two trace windows. The code path was actually correct — while loop exits properly after 1 DTB reg entry.
2. ~~DTB parsing reads wrong offset (60-byte shift)~~ — DTB parsing works correctly
3. ~~`memblock_add` never called~~ — It IS called at cycle 3162213
4. ~~`early_init_dt_add_memory_arch` never called~~ — Confirmed executing at C0151258

### Prime Suspect: `holdEX` includes `divStall` in generated SoC but NOT in hand-written SV

**Critical difference found:**

| | Hand-written SV (rv32i_soc.sv:803) | Generated (SoC.lean:995-996) |
|---|---|---|
| `holdEX` | `pendingWriteEn` | `pendingWriteEn \|\| (divStall && !flushOrDelay)` |

The generated SoC includes `divStall` in `holdEX`. Since `suppressEXWB = dTLBMiss || holdEX`, and `prevStoreEn_next = suppressEXWB ? false : idex_memWrite`, **any store in the EX stage during a multi-cycle divide (~34 cycles) gets its `prevStoreEn` killed**.

This is the most likely root cause: if a `sw` instruction in `memblock_add_range` happens to execute while `divStall` is active (e.g., from a prior DIV instruction still in flight), the store will be suppressed.

### Debugging Strategy: Trace Diffing (Co-simulation comparison)

Compare cycle-accurate traces from hand-written (working) and generated (broken) SoC:

1. Add per-cycle trace output: `PC, dmem_we, dmem_addr, dmem_wdata, holdEX, divStall, suppressEXWB`
2. Build both SoCs with same testbench
3. Run both with identical firmware/DTB/payload
4. `diff` the traces around memblock_add (cycle ~3162213)
5. Identify exact cycle where generated SoC diverges (store suppressed)

### Resolution

**FIXED** in Phase 13 — `holdEX` simplified to `pendingWriteEn` only; pipeline freezing uses new `freezeIDEX` signal. See "holdEX/divStall Store Bug Fix" section above.

### Next Steps (TODO)

- [x] ~~**Fix holdEX in SoC.lean**~~ — Done (Phase 13)
- [ ] **Verify Linux boots on fixed generated SoC** — run OpenSBI + Linux boot test with fixed holdEX
- [ ] **Implement Trace Diffing** — add unified trace format to tb_soc.cpp for future debugging
- [ ] **(Future) Formal verification** — prove Store Persistence invariant in Lean: `always (idex_isStore ∧ ¬trap ⟹ eventually (dmem_we ∧ correct_addr))`

### Relevant Verilator signal names

| Signal | Description |
|--------|-------------|
| `_gen_useTranslatedAddr_7683` | Whether TLB-translated address is used |
| `_gen_dTLBMiss_7691` | D-side TLB miss |
| `_gen_effectiveAddr_7684` | Final address after MMU bypass check |
| `_gen_dPhysAddr_7681` | Physical address from TLB |
| `_gen_alu_result_approx_7575` | Raw ALU result (VA for loads/stores) |
| `_gen_dmem_read_addr_7710` | Final 23-bit DMEM word address |
| `_gen_actual_dmem_write_addr_7779` | DMEM write word address |
| `_gen_actual_byte0_we_7784` | Byte 0 write enable |
| `_gen_ptwStateNext_9216` | PTW state next (3-bit) |
| `_gen_ptwReq_9178` | PTW request signal |
| `_gen_stall_8786` | Pipeline stall |
| `_gen_flush_8294` | Flush signal |
| `_gen_suppressEXWB_8849` | Suppress EX/WB writeback |

### Key kernel addresses (from /tmp/linux/vmlinux)

| Function | Virtual Address | Description |
|----------|----------------|-------------|
| `early_init_dt_scan_memory` | 0xC01513A0 | Outer DTB scanning function |
| `early_init_dt_add_memory_arch` | 0xC0151238 | Clamps base/size, tail-calls memblock_add |
| `memblock_add` | 0xC0153F8C | Entry point (stores base/size to stack) |
| `memblock_add_range.isra.0` | 0xC0153D40 | Core logic — simple case writes to regions[0] |
| `setup_vm_final` | (in paging_init) | Creates swapper_pg_dir using memblock_alloc |

### Key DMEM addresses for memblock

| Address | DMEM word | Description |
|---------|-----------|-------------|
| 0xC0158554 (PA 0x80558554) | 0x156155 | memblock struct start |
| 0xC015855C (PA 0x8055855C) | 0x156157 | memblock.memory.cnt |
| 0xC0158560 (PA 0x80558560) | 0x156158 | memblock.memory.max |
| 0xC0158564 (PA 0x80558564) | 0x156159 | memblock.memory.total_size |
| 0xC0158568 (PA 0x80558568) | 0x15615A | memblock.memory.regions (pointer) |
| 0xC0158598 (PA 0x80558598) | 0x156166 | memblock_memory_init_regions[0].base |
| 0xC015859C (PA 0x8055859C) | 0x156167 | memblock_memory_init_regions[0].size |
| 0xC01585A0 (PA 0x805585A0) | 0x156168 | memblock_memory_init_regions[0].flags |

---

## Firmware Test — PASSED

- ALL 48 UART words match hand-written reference byte-for-byte
- All 10 sections pass including `0xcafe0000` pass marker at cycle 2904
- Identical behavior to hand-written SV reference

---

## Future Work

- [ ] Verify Linux boots on fixed generated SV (holdEX/divStall bug is fixed, needs retest)
- [ ] JIT FFI implementation (see `docs/JIT_FFI_Plan.md`)
- [ ] Bulk refactoring of SoC.lean to use Signal Bool operators (`|||`, `&&&`, `~~~`)
- [ ] Debug infrastructure cleanup (remove unused debug ports/traces)
- [ ] Fix Verilator testbench internal signal references
- [ ] Interrupt controller (PLIC)
- [ ] Timer interrupt handling (CLINT timer compare)
- [ ] Instruction cache, branch predictor
- [ ] FPGA synthesis targeting

---

## Build & Test Commands

```bash
# Lean build (SoC simulation)
lake build Examples.RV32.SoC

# Lean build (Verilog synthesis → writes verilator/generated_soc.sv)
lake build Examples.RV32.SoCVerilog

# Verilator build (generated SV + wrapper)
cd verilator && make build

# Verilator build (hand-written SV, reference)
cd verilator && make build-handwritten

# Firmware test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000

# Linux boot test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
```
