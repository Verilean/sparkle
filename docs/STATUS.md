# Sparkle SoC — Current Status

**Date**: 2026-03-04
**Branch**: main

---

## Next Phases (TODO)

| Priority | Phase | Description | Status |
|----------|-------|-------------|--------|
| 1 | **eval()+tick() Fusion** | Eliminate 260 `_next` memory ops/cycle by fusing eval and tick into single function (est. ~1.3x → 17M cyc/s) | Not started |
| 2 | **Linux Boot Idle-Loop Skipping** | Extend self-loop oracle to detect WFI/idle loops during Linux boot (larger pcTolerance, interrupt-aware timer advancement) | Not started |
| 3 | **Verified Standard IP — Parameterized FIFO** | Generic depth/width FIFO with power-of-2 depth, extending SyncFIFO pattern | Not started |
| 4 | **Verified Standard IP — N-way Arbiter** | Generalize 2-client round-robin arbiter to N clients | Not started |
| 5 | **Verified Standard IP — AXI4-Lite / TileLink** | Bus protocol interfaces with formal properties | Not started |
| 6 | **GPGPU / Vector Core** | Apply VDD framework to highly concurrent, memory-bound accelerator architectures | Not started |
| 7 | **FPGA Tape-out Flow** | End-to-end examples deploying Sparkle-generated Linux SoCs to physical FPGAs | Not started |

---

## Completed Phases

### Linux Boot Time-Warping — Dynamic Oracle + Bulk Memory API (Phase 29) — DONE

Direct JITHandle access for oracles and bulk memory API, enabling dynamic register introspection and fast BSS zeroing for Linux boot acceleration.

### What Was Built

| Component | File | Description |
|-----------|------|-------------|
| **memsetWord API** | `Sparkle/Backend/CppSim.lean` | `emitMemsetWordSwitch` generates per-memory bulk fill with bounds checking |
| **memsetWord FFI** | `c_src/sparkle_jit.c` | `memset_word` fn ptr, dlsym, `sparkle_jit_memset_word` LEAN_EXPORT |
| **memsetWord binding** | `Sparkle/Core/JIT.lean` | `JIT.memsetWord` opaque extern |
| **Refactored oracle** | `Sparkle/Core/JITLoop.lean` | Oracle signature: `JITHandle → Nat → Array UInt64 → IO (Option Nat)` |
| **Self-contained oracle** | `Sparkle/Core/Oracle.lean` | `mkSelfLoopOracle` no longer takes `handle` — oracle receives it per-call, handles setReg internally |
| **Dynamic warp test** | `Tests/RV32/JITDynamicWarpTest.lean` | memsetWord roundtrip + hand-written dynamic oracle — PASS |

### Key Design Changes

- **Oracle receives JITHandle per-call**: enables dynamic register reads (`JIT.getReg handle`), bulk memory ops (`JIT.memsetWord handle`), and direct state mutation (`JIT.setReg handle`) — all self-contained
- **Simplified return type**: `IO (Option Nat)` instead of `IO (Option (Nat × Array (UInt32 × UInt64)))` — oracle handles all mutations internally
- **memsetWord**: fills memory range with bounds checking, generated per-memory bank (same pattern as `emitMemoryAccessSwitches`)

### Performance Results (firmware.hex, 10M cycles)

| Metric | Value |
|--------|-------|
| memsetWord roundtrip | PASS (10 words verified) |
| Dynamic oracle triggers | 9,998 |
| Effective cyc/s | ~500M–1.4B |
| UART words | 48 (0xCAFE0000 marker seen) |

---

### JIT Cycle-Skipping — Self-Loop Oracle (Phase 28) — DONE

Self-loop detection oracle that detects when the CPU is stuck in a tight halt loop and skips forward by advancing the cycle counter + CLINT timer registers. Achieves **706x speedup** on post-halt simulation.

### What Was Built

| Component | File | Description |
|-----------|------|-------------|
| **Oracle module** | `Sparkle/Core/Oracle.lean` | `SelfLoopConfig`, `SelfLoopState`, `mkSelfLoopOracle` factory (Phase 29: oracle receives JITHandle per-call) |
| **Skip-count API** | `Sparkle/Core/JITLoop.lean` | `runOptimized` with oracle callback (Phase 29: `JITHandle → Nat → Array UInt64 → IO (Option Nat)`) |
| **End-to-end test** | `Tests/RV32/JITOracleTest.lean` | 10M-cycle firmware test with oracle — PASS |

### Self-Loop Detection Algorithm

- Monitors PC wire each cycle; tracks an **anchor PC** and counts consecutive cycles where the PC stays within `pcTolerance` bytes (default 12)
- When count exceeds `threshold` (default 50, safely above 34-cycle divider stall), triggers a skip
- On trigger: advances CLINT timer (mtimeLo/mtimeHi) by `skipAmount` (default 1000), skips `tick()`, advances cycle counter
- Handles multi-instruction halt loops (e.g., 4-instruction loop at 0x48–0x54) via tolerance-based matching

### Performance Results (firmware.hex, 10M cycles)

| Metric | Without Oracle | With Oracle |
|--------|---------------|-------------|
| Wall-clock time | ~5,500 ms | **8 ms** |
| Effective cyc/s | 1.8M | **1.25 billion** |
| Oracle triggers | — | 9,998 |
| Cycles skipped | — | 9,998,000 |
| UART output | 48 words + 0xCAFE0000 | identical |

---

## JIT Cycle-Skipping Infrastructure — Phase 1 (Phase 27) — DONE

Register read/write API at every layer (C++ codegen → C FFI → Lean bindings → optimized run loop) enabling snapshot/restore of simulation state. This is the foundation for oracle-driven cycle-skipping, where an external function detects steady-state patterns (e.g., busy-wait loops) and jumps the simulation forward.

### What Was Built

| Component | File | Description |
|-----------|------|-------------|
| **C++ codegen** | `Sparkle/Backend/CppSim.lean` | `collectRegisters`, `emitSetRegSwitch`, `emitGetRegSwitch`, `emitRegNameSwitch`; 4 new extern "C" functions in JIT wrapper |
| **C FFI** | `c_src/sparkle_jit.c` | 4 function pointers in `JITHandle`, 4 `dlsym` calls, 4 Lean export wrappers |
| **Lean bindings** | `Sparkle/Core/JIT.lean` | `setReg`, `getReg`, `regName`, `numRegs` opaque bindings + `findReg` helper |
| **Optimized run loop** | `Sparkle/Core/JITLoop.lean` | `JIT.runOptimized` (oracle callback for cycle-skipping) + `JIT.resolveRegs` |
| **Roundtrip test** | `Tests/RV32/JITCycleSkipTest.lean` | Snapshot/restore roundtrip — PASS |

### Register API

```cpp
// Auto-generated in JIT wrapper (130 registers for RV32 SoC)
void     jit_set_reg(void* ctx, uint32_t reg_idx, uint64_t val);
uint64_t jit_get_reg(void* ctx, uint32_t reg_idx);
const char* jit_reg_name(uint32_t idx);
uint32_t jit_num_regs();  // returns 130
```

```lean
-- Lean bindings
JIT.setReg   : JITHandle → UInt32 → UInt64 → IO Unit
JIT.getReg   : JITHandle → UInt32 → IO UInt64
JIT.regName  : JITHandle → UInt32 → IO String
JIT.numRegs  : JITHandle → IO UInt32
JIT.findReg  : JITHandle → String → IO (Option UInt32)

-- Oracle-driven run loop (Phase 29: oracle receives JITHandle directly)
JIT.runOptimized : JITHandle → Nat → Array UInt32
    → (JITHandle → Nat → Array UInt64 → IO (Option Nat))  -- oracle (self-contained)
    → (Nat → Array UInt64 → IO Bool)                       -- callback
    → IO Nat
JIT.memsetWord : JITHandle → UInt32 → UInt32 → UInt32 → UInt32 → IO Unit
```

### Snapshot/Restore Test

```
CycleSkip: 130 registers found
CycleSkip: Running 100 cycles...
CycleSkip: PC at cycle 100 = 0x80000fc
CycleSkip: Snapshotting 130 registers...
CycleSkip: PC at cycle 101 (reference) = 0x8000100
CycleSkip: Resetting simulation...
CycleSkip: Restoring registers...
CycleSkip: PC after restore+eval+tick+eval (actual) = 0x8000100

*** PASS: Register snapshot/restore roundtrip works ***
```

**Key insight**: After restoring registers, must call `eval` before `tick` to recompute `_next` values (reset doesn't clear `_next` state).

### Updated Benchmark (10M cycles, firmware.hex, Apple Silicon)

| Backend | Speed | CPU instrs/sim-cycle | vs Verilator |
|---------|-------|---------------------|-------------|
| **JIT (-O2 dylib)** | **13.3M cyc/s** | 2,077 | **1.27x faster** |
| Verilator 5.044 | 10.4M cyc/s | 2,714 | 1.00x |
| CppSim (-O3 AOT) | 6.0M cyc/s | — | 0.58x |

**Profile (sampling profiler, 10s):**

| Component | JIT | Verilator |
|-----------|-----|-----------|
| Combinational (eval/comb) | 74.1% | 23.0% |
| Register update (tick/seq) | 23.5% | 44.7% |
| Eval overhead | 2.4% | 14.9% |
| Mutex/thread overhead | 0% | **17.4%** |

**Why JIT is faster than Verilator:**
1. No mutex overhead — Verilator 5.x wastes 17.4% on `VlDeleter::deleteAll`, `VerilatedMutex`
2. Fewer instructions — 2,077 vs 2,714 per sim-cycle (Verilator does 2 evals/cycle)
3. Observable wire optimization — 33 class members + 321 locals (L1-friendly)

### Note on Sub-Module Registers

Sub-module registers (e.g., divider's 8 internal registers) are already flattened into the single JIT class. All 130 registers (8 divider + 122 SoCState) are accessible via `JIT.setReg/getReg`. No hierarchical register work was needed for the Phase 28 oracle.

### Verification

- `lake build` — compiles
- `lake exe rv32-jit-cycle-skip-test` — PASS (snapshot/restore roundtrip)
- Generated `verilator/generated_soc_jit.cpp` contains all 4 register functions with 130 register entries

---

## Verified Standard IP Library — SyncFIFO (Phase 26) — DONE

First component of the **Verified Standard IP Library**: a Synchronous FIFO with Valid/Ready (Decoupled) interface. Establishes the pattern for future verified IP (arbiter, crossbar, cache, AXI4, etc.).

### What Was Built

| Component | File | Description |
|-----------|------|-------------|
| **Pure formal model** | `Sparkle/Library/Queue/QueueProps.lean` | 7 theorems (no `sorry`) — no overflow, no underflow, full/empty guards, idle/simultaneous preserves, inductive invariant |
| **Synthesizable hardware** | `Sparkle/Library/Queue/SyncFIFO.lean` | Depth-4 FIFO using `declare_signal_state`, `Signal.loop`, `Signal.memoryComboRead`, `hw_cond` |
| **LSpec tests** | `Tests/Library/TestSyncFIFO.lean` | 16 tests — fill, drain, FIFO ordering, full/empty conditions, simultaneous enq+deq |
| **Test integration** | `Tests/AllTests.lean` | Import + invocation wired up |

### Architecture

- **Parameters**: depth=4 (addrWidth=2), dataWidth=32
- **State**: `SyncFIFOState` = `BitVec 2 × BitVec 2 × BitVec 3` (wrPtr, rdPtr, count)
- **Data buffer**: `Signal.memoryComboRead` (same-cycle read for dequeue data)
- **Output**: `BitVec 32 × BitVec 32 × BitVec 32` (enqReady, deqValid, deqData)

### Design Pattern (reusable for future IP)

1. **Extract loop body** into standalone `def` — enables sharing between synthesis and simulation
2. **Synthesis path**: `Signal.loop body` — generates valid SystemVerilog via `#synthesizeVerilog`
3. **Simulation path**: `Signal.loopMemo body` — avoids stack overflow for functional tests
4. **Pure model** (`QueueProps.lean`) — proven properties in a separate file, no hardware dependencies

### Formal Properties (all proven)

| Theorem | Statement |
|---------|-----------|
| `no_overflow` | `count ≤ depth → nextCount ≤ depth` |
| `no_underflow` | `0 ≤ nextCount` (trivial for Nat) |
| `full_blocks_enqueue` | `¬ canEnqueue depth depth` |
| `empty_blocks_dequeue` | `¬ canDequeue 0` |
| `idle_preserves` | `nextCount c d false false = c` |
| `simultaneous_preserves` | `canEnqueue ∧ canDequeue → nextCount c d true true = c` |
| `count_bounded_inductive` | Same as `no_overflow` (inductive invariant) |

### Generated SystemVerilog (excerpt)

```systemverilog
module Sparkle_Library_Queue_SyncFIFO_syncFIFO (
    input logic _gen_enqValid,
    input logic [31:0] _gen_enqData,
    input logic _gen_deqReady,
    input logic clk, input logic rst,
    output logic [95:0] out
);
    // 3 registers: wrPtr (2-bit), rdPtr (2-bit), count (3-bit)
    // 4-entry memory: _gen_deqData [0:3]
    // Priority mux for count update (enq-only / deq-only / simultaneous)
    // Combo read for dequeue data
endmodule
```

### Test Results (all 16 pass)

```
SyncFIFO:
  Initial State:
    ✓ enqReady=1 at t=0 (empty FIFO)
    ✓ deqValid=0 at t=0 (empty FIFO)
  Enqueue Phase:
    ✓ enqReady=1 at t=1..3
  Full Condition:
    ✓ enqReady=0 at t=4 (full)
    ✓ deqValid=1 at t=4
  Dequeue Phase — FIFO Order:
    ✓ deqData=0xA0..0xA3 at t=4..7
  Empty After Drain:
    ✓ deqValid=0 at t=8 (empty)
    ✓ enqReady=1 at t=8
  Simultaneous Enq+Deq:
    ✓ enqReady=1, deqValid=1 at t=3
```

### Verification

- `lake build` — all 103 modules compile
- `lake test` — all 16 SyncFIFO tests pass (only pre-existing CppSim bit-accuracy failure)
- `#synthesizeVerilog syncFIFO` — valid SystemVerilog with memory, registers, combinational logic
- QueueProps theorems — all 7 compile without `sorry`

---

## Next Phases (TODO)

### JIT Cycle-Skipping — Completed

| Task | Status | Description |
|------|--------|-------------|
| **Cycle-skip oracle** | DONE (Phase 28) | Self-loop detection: tolerance-based PC tracking, CLINT timer advancement |
| **Sub-module registers** | DONE (Phase 27) | All 130 registers (8 divider + 122 SoCState) flattened and accessible |
| **Bulk memory API** | DONE (Phase 29) | `JIT.memsetWord` for fast memory fills with bounds checking |
| **Dynamic oracle API** | DONE (Phase 29) | Oracle receives `JITHandle` directly for dynamic register/memory access |
| **Linux boot cycle-skip** | TODO | Oracle for OpenSBI/Linux idle loops (WFI, busy-wait, larger tolerance) |

### Performance Optimization

| Phase | Status | Est. Speedup | Description |
|-------|--------|-------------|-------------|
| **eval()+tick() fusion** | TODO | ~1.3x → 17M cyc/s | Eliminate 260 `_next` memory ops/cycle (130 stores in eval + 130 load/store in tick). Requires topological ordering for circular register dependencies |
| **Multi-cycle batching** | TODO | ~1.1-1.2x | Unroll 2-4 sim-cycles, keep registers in CPU registers across cycles |
| **Cycle-skipping** | DONE | unbounded | Self-loop oracle: 10M cycles in 9ms (706x). Dynamic oracle API with direct JITHandle access (Phase 29) |

### Verified Standard IP Library — Remaining Components

| Component | Status | Description |
|-----------|--------|-------------|
| **SyncFIFO** | DONE | Depth-4 FIFO with Valid/Ready interface |
| **Parameterized FIFO** | TODO | Generic depth/width FIFO (power-of-2 depth) |
| **Credit-based flow control** | TODO | Backpressure via credits instead of ready/valid |
| **Arbiter (N-way)** | TODO | Generalize 2-client arbiter to N clients |
| **Crossbar** | TODO | N×M crossbar switch with arbitration |
| **AXI4-Lite** | TODO | AXI4-Lite master/slave interfaces |
| **Cache** | TODO | Direct-mapped / set-associative cache with write-back |
| **TileLink** | TODO | TileLink Uncached Lightweight (TL-UL) |

### Hardware Targets

| Phase | Status | Description |
|-------|--------|-------------|
| **FPGA Tape-out** | TODO | End-to-end Sparkle → FPGA flow |
| **GPGPU / Vector Core** | TODO | VDD framework applied to concurrent architectures |

---

## CppSim Phase 3 — Store Reduction via Observable Wire Threading (Phase 25) — DONE

Threaded `observableWires` through the IR optimizer, CppSim backend, and `#writeDesign` command. This unblocks `_gen_` wire inlining (previously deferred in Phase 24) by passing the 6 JIT-observable wire names explicitly from the application layer (`SoCOutput.wireNames`), rather than using the blanket `_gen_` prefix guard.

### Results

| Metric | Before (Phase 24) | After (Phase 25) | Change |
|--------|-------------------|-------------------|--------|
| **JIT class members** | 1,242 | **295** | **-76%** |
| **JIT `_gen_` members** | 980 | **33** | **-97%** (947 demoted to locals) |
| **JIT `eval()` locals** | 0 | **321** | Stack-allocated, register-friendly |
| **`jit_num_wires`** | ~976 | **6** | Only observable wires exposed |
| **JIT pure eval+tick** | ~6.3M cyc/s | **12.6M cyc/s** | **2.0x speedup** |

### How It Works

1. **Optimizer** (`Optimize.lean`): `inlineSingleUseWires` now accepts `observableWires : Option (List String)`. When `some ws`, only wires in `ws` are protected from inlining (instead of ALL `_gen_` wires). When `none`, backwards-compatible `_gen_` guard.

2. **CppSim backend** (`CppSim.lean`): Wire partitioning uses `observableWires` to decide member vs local. Wires referenced in `tick()` bodies (memory writes, non-combo reads) are always kept as members via `collectTickRefWires`.

3. **`#writeDesign` command** (`Elab.lean`): Split into 3-arg (backwards-compatible) and 4-arg variant. The 4th arg is a constant name resolving to `Array String`. Header file (`_cppsim.h`) keeps all `_gen_` as members (no `observableWires`), JIT file (`_jit.cpp`) uses `observableWires` for aggressive optimization.

4. **SoCVerilog.lean**: `#writeDesign rv32iSoCSynth "..." "..." SoCOutput.wireNames` — passes the 6 observable wire names.

### Key Fix: Tick-Referenced Wires

Initial implementation failed because memory `tick()` bodies reference wires via expressions (e.g., `if (_gen_wb_en) mem[_gen_exwb_rd] = _gen_wb_result`). These wires were demoted to `eval()` locals, making them inaccessible from `tick()`. Fixed by adding `collectTickRefWires` which scans memory statements for expression references and keeps those wires as class members.

### Files Modified

| File | Changes |
|------|---------|
| `Sparkle/IR/Optimize.lean` | Added `observableWires` param to `inlineSingleUseWires`, `optimizeModule`, `optimizeDesign` |
| `Sparkle/Backend/CppSim.lean` | Added `collectExprRefs`, `collectTickRefWires`; added `observableWires` param to 6 functions; tick-ref wires stay as members |
| `Sparkle/Compiler/Elab.lean` | Split `#writeDesign` into 3-arg + 4-arg syntax; added `evalStringArray` helper; `writeDesignCore` shared implementation |
| `Examples/RV32/SoCVerilog.lean` | Added `SoCOutput.wireNames` as 4th argument |

### Verification

- `lake build` — compiles
- `lake test` — all pass (only pre-existing YOLOv8 float test fails)
- `lake exe rv32-jit-test` — 47 UART words, 0xCAFE0000, ALL TESTS PASSED
- `lake exe rv32-jit-loop-test` — both APIs pass
- `./cppsim_soc ../firmware/firmware.hex 5000` — ALL TESTS PASSED (uses header, not JIT)

### Updated Bottleneck Analysis

| Component | Status | Impact |
|-----------|--------|--------|
| Store count (`_gen_` members) | **DONE** — 980 → 33 JIT members | **2.0x speedup** |
| Mask operations | DONE (Phase 24) — 312 eliminated | Marginal |
| tick() overhead | Deferred — eval()+tick() merge | ~4.2x vs Verilator |

---

## CppSim Phase 2 — Mask Elimination (Phase 24) — DONE

Extended the `exprIsMasked` analysis in the CppSim backend to eliminate redundant `& mask` operations at runtime.

### Results

| Metric | Before (Phase 23) | After (Phase 24) | Change |
|--------|-------------------|-------------------|--------|
| **Mask operations** | 449 | **137** | **-69.5% (312 eliminated)** |
| **CppSim speed** | 6.3M cyc/s | ~6.4M cyc/s | Marginal (masks are cheap on ARM64) |

### New `exprIsMasked` Cases

| Pattern | Rule | Reasoning |
|---------|------|-----------|
| `.ref _` | always masked | Invariant: every wire is masked at its assignment site |
| `.op .and [a, b]` | `a \|\| b` | AND with a masked operand constrains the result (NOT unconditional — `AND(~x, ~y)` preserves garbage) |
| `.op .or [a, b]` | `a && b` | OR of two masked values stays within width |
| `.op .xor [a, b]` | `a && b` | XOR of two masked values stays within width |
| `.op .shr _` | always masked | Right-shift moves bits toward LSB, no new upper bits |
| `.op .asr _` | always masked | Masked input is positive in signed cast, no sign extension above `w` |

Also applied `exprIsMasked` to register inputs (previously always masked unconditionally).

### `_gen_` Wire Inlining — Deferred

The plan's Step 1 (inline single-use `_gen_` wires with output-feeding protection) was investigated and found unsafe:
- `_gen_` wires are accessed by name at runtime via `jit_get_wire()` and `loopMemoJIT`
- Naming collisions (e.g., `_gen_ptwPteReg` vs `_gen_ptwPteReg_1`) mean the output-feeding set cannot reliably identify all JIT-observable wires
- The `_gen_` prefix serves as a JIT observability contract — breaking it causes runtime lookup failures

**Resolved in Phase 25**: Observable wire threading passes `SoCOutput.wireNames` explicitly, avoiding the naming collision problem entirely.

### Key Bug Fix: AND Mask Rule

The original plan specified `.op .and _ => true` (AND always masked). This is **incorrect**:
- `AND(~a, ~b)` where both operands are bitwise-NOT of 1-bit values: `AND(0xFE, 0xFE) = 0xFE` — not 1-bit
- Fix: `AND(a, b)` is masked if **either** `a` or `b` is masked (the masked one constrains the result)

### Files Modified

| File | Changes |
|------|---------|
| `Sparkle/Backend/CppSim.lean` | Extended `exprIsMasked` (6 new cases), applied to register inputs |

### Remaining 1.3x Gap — Updated Bottleneck Analysis (resolved in Phase 25)

| Component | Status | Impact |
|-----------|--------|--------|
| Store count (`_gen_` members) | **DONE** (Phase 25) — 980 → 33 JIT members | **2.0x speedup**, JIT now faster than Verilator |
| Mask operations | **DONE** — 312 eliminated (69.5%) | Marginal perf impact |
| tick() overhead | Deferred — eval()+tick() merge | ~4.2x vs Verilator |

---

## CppSim Backend Optimization (Phase 23) — DONE

Implemented IR-level optimizations and CppSim backend improvements to close the 2.7x performance gap with Verilator identified in Phase 22.

### Results

| Metric | Before (Phase 22) | After (Phase 23) | Change |
|--------|-------------------|-------------------|--------|
| **CppSim speed** | 3.6M cyc/s | **6.3M cyc/s** | **+75%** |
| **vs Verilator** | 2.7x slower | **1.3x slower** | Gap closed by 2.1x |
| Assignments in eval() | 2,242 | 1,375 | -39% |
| Member variables | 3,009 | 1,254 | -58% |
| Generated C++ lines | ~6,000 | 2,669 | -56% |

### Benchmark (10M cycles, boot.hex stub, Apple Silicon)

| Backend | Speed | vs Verilator |
|---------|-------|-------------|
| **Verilator** | **8.13M cyc/s** | 1.0x |
| **CppSim (AOT, -O3)** | 6.31M cyc/s | 1.29x |
| **JIT (dlopen, -O2)** | 6.27M cyc/s | 1.30x |

### Optimizations Applied

1. **Single-use wire inlining** (IR level, `Optimize.lean`): Replaces references to wires used exactly once with their defining expression, removing ~900 intermediate assignments. Preserves `_gen_` wires (JIT-observable), register outputs, memory read-data, and module outputs.

2. **Constant folding** (IR level, `Optimize.lean`): Simplifies `mux(true,t,e)→t`, `mux(false,t,e)→e`, `eq(const,const)`, `add(0,x)→x`, `or(0,x)→x`, `and(0,x)→0`, `slice(const)→const`.

3. **Local variable promotion** (CppSim, `CppSim.lean`): Partitions internal wires — `_gen_` prefix wires remain class members (JIT-observable via `jit_get_wire`), all `_tmp_` wires become local variables in `eval()`, enabling CPU register allocation.

4. **Redundant mask elimination** (CppSim, `CppSim.lean`): Skips `& mask` for constants, comparison results (already 0/1), exact-width slices, and mux of already-masked operands.

### Files Modified

| File | Description |
|------|-------------|
| `Sparkle/IR/Optimize.lean` | Added `foldConstants`, `inlineSingleUseWires`, `substituteExpr`; integrated as Phase 3-4 in `optimizeModule` |
| `Sparkle/Backend/CppSim.lean` | Local variable promotion in `emitModule`, `exprIsMasked` for redundant mask elimination |

### Remaining 1.3x Gap — Assembly-Level Analysis

Profiled JIT vs Verilator at the ARM64 instruction level:

| Component | Verilator | JIT | Ratio | Root Cause |
|-----------|-----------|-----|-------|------------|
| Stores (str/strb) | 283 | 1,115 | 3.9x | JIT writes every `_gen_` wire to memory; Verilator uses locals |
| Loads (ldr/ldrb) | 256 | 691 | 2.7x | Corresponding read traffic |
| Masks (and) | 80 | 292 | 3.7x | JIT applies runtime masks; Verilator uses sized types |
| Conditionals (cmp/csel) | 181 | 484 | 2.7x | JIT evaluates all muxes; Verilator may skip unchanged |
| tick() instructions | 89 | 373 | 4.2x | JIT copies all registers unconditionally |

**Next optimization targets:**
- Promote `_gen_` wires that aren't read by `jit_get_wire` to locals (biggest impact)
- Extend mask elimination to more expression patterns
- Merge eval()+tick() into single pass (eliminate register copy overhead)

---

## Simulation Performance Analysis (Phase 22) — DONE

Benchmarked all simulation backends at 10M cycles (Linux boot) and identified the root cause of the CppSim/JIT vs Verilator performance gap.

### Benchmark Results (10M cycles, Linux boot, Apple Silicon)

| Backend | Time | Speed | Instructions | CPU Cycles | IPC |
|---------|------|-------|-------------|-----------|-----|
| **Verilator** | 1.03s | **9.7M cyc/s** | 27.65B | 4.13B | 6.69 |
| **CppSim (AOT)** | 2.78s | 3.6M cyc/s | 54.94B | 11.38B | 4.83 |
| **JIT (dlopen)** | 2.77s | 3.6M cyc/s | — | — | — |
| **Lean loopMemo** | ~2000s | ~5K cyc/s | — | — | — |

### Root Cause: CppSim generates 2x more instructions per cycle

| Factor | Verilator | CppSim | Impact |
|--------|-----------|--------|--------|
| **Assignments/cycle** | 831 | 2,242 | **2.7x more work** |
| **Member variables** | 375 | 3,009 | **8x more memory traffic** |
| **Local variables** | 145 (stack) | 0 | Verilator benefits from register allocation |
| **Expression inlining** | 20+ level nested | 1 per assignment | Verilator eliminates intermediate stores |
| **Constant handling** | Inline literals | `_tmp = 0` in member | CppSim wastes stores on constants |
| **Memory arrays** | 6 (35 MB) | 12 (68 MB) | CppSim duplicates regfile + DRAM |
| **If-else usage** | 35 (reset/WE) | 0 | Verilator skips code via branch prediction |
| **Bit masking** | Sized types (CData) | Runtime `& ((1<<N)-1)` | CppSim wastes instructions on masking |

The 2.75x gap decomposes into: **2.0x instruction count** (CppSim executes 5494 vs 2765 instructions per sim-cycle) × **1.38x IPC penalty** (4.83 vs 6.69 IPC).

### Key Insight

CppSim's `_tmp_*` temporaries account for ~70% of all member variables (~2100 of 3009). These are single-use intermediate values that Verilator inlines into consumer expressions. Eliminating them is the single highest-impact optimization for closing the performance gap.

### Disproved Hypotheses

- **L1 cache miss theory**: Wrong — CppSim struct is ~12KB, fits in 128KB L1 cache
- **Local variable promotion**: Only 6% improvement at -O3 — not the bottleneck
- **Ternary → bitwise conversion**: Verilator does NOT use bitwise mux patterns

---

## Transparent JIT — `loopMemoJIT` (Phase 21) — DONE

Implemented `Signal.loopMemoJIT` — a transparent JIT replacement for `Signal.loopMemo` that provides the same `IO (Signal dom α)` API but uses JIT-compiled C++ under the hood for ~200x speedup over interpreted simulation.

### API

```lean
-- Signal API (cached, same interface as loopMemo)
let soc ← rv32iSoCJITSimulate (jitCppPath := "verilator/generated_soc_jit.cpp") (firmware := fw)
let out := soc.atTime 1000   -- SoCOutput: pc, uartValid, uartData, satp, ptwPte, ptwVaddr

-- Streaming API (O(1) memory, for long runs)
rv32iSoCJITRun (jitCppPath := cppPath) (firmware := fw) (cycles := 10000000)
  (callback := fun cycle vals => do ...)
```

### Design Decisions

- Uses **named output wires** (`_gen_pcReg`, `_gen_uartValidBV`, etc.) instead of internal state wires — immune to DCE and name collisions
- `SoCOutput` struct (6 fields) instead of full `SoCState` (122 fields) — only output-port-observable values
- `JIT.resolveWires` maps wire names → indices at init time
- Wire read overhead: ~0.5% (negligible)

### Files Created/Modified

| File | Action | Description |
|------|--------|-------------|
| `Sparkle/Core/JITLoop.lean` | **Created** | `loopMemoJIT` + `JIT.run` + `JIT.resolveWires` |
| `Sparkle/Core/StateMacro.lean` | Modified | Added `wireNames` + `fromWires` generation |
| `Examples/RV32/SoC.lean` | Modified | `SoCOutput`, `rv32iSoCJITSimulate`, `rv32iSoCJITRun` |
| `Tests/RV32/JITLoopTest.lean` | **Created** | Two-part test (Signal API + Streaming API) |
| `Sparkle.lean` | Modified | Added `import Sparkle.Core.JITLoop` |
| `lakefile.lean` | Modified | Added `rv32-jit-loop-test` executable |

### Test Results

Both Part 1 (Signal API via `loopMemoJIT`) and Part 2 (Streaming API via `rv32iSoCJITRun`) pass — 47 UART words, `0xCAFE0000` marker at cycle 2904.

---

## Linux Boot Verified on Generated SoC (Phase 20) — DONE

Verified that the holdEX/divStall fix (Phase 13) resolves the Linux boot hang. The generated SoC now boots Linux 6.6.0 via OpenSBI v0.9, matching the hand-written SV reference behavior.

### Test Results

| Metric | Previous (broken holdEX) | Generated SV (fixed) | Hand-written SV (reference) |
|--------|-------------------------|----------------------|----------------------------|
| UART bytes | 1906 | **5250** | 3944 |
| Hang point | ~3.3M cycles (recursive page fault) | Still running at 10M | Still running at 10M |
| Final PC region | 0xC0001C88 (recursive page fault) | 0xC013A9xx (kernel init) | 0xC013A9xx (kernel init) |
| Page faults | Recursive (infinite loop) | 3 total (normal) | Normal |

### Key Findings

1. **holdEX/divStall fix works**: Kernel no longer hangs at recursive page fault (0xC0001C88). Page tables populated correctly, kernel proceeds through memory initialization.
2. **Generated SV matches hand-written SV behavior**: Both reach the same kernel PC region (0xC013A9xx–0xC013B5xx) — the calibrating delay loop / kernel init busy-wait. Neither is hung; both show different PCs at each 100K-cycle sample.
3. **Generated SV produces more UART output (5250 vs 3944)**: Multi-cycle divider (34 cycles) changes timing vs combinational divider in hand-written SV, causing SBI console to output at different intervals.
4. **OpenSBI boots normally**: Full platform info printed (Sparkle RV32IMA SoC, rv32imasu ISA).
5. **Kernel boot progresses**: "Linux version 6.6.0" printed, memory regions detected correctly (`base=0x80400000, size=0x01c00000`), kernel well into init.

### Build Fix

`tb_soc.cpp` referenced `_gen_dTLBMiss` which Verilator optimizes away. Replaced two references with `0` (debug tracing only).

### Verification

```bash
$ lake build Examples.RV32.SoCVerilog   # Regenerate SV from latest Lean source
$ cd verilator && make build            # Build Verilator simulation
$ ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
# === OpenSBI simulation ended (5250 UART bytes) ===
# Both generated and hand-written SV reach same kernel init region at 10M cycles
```

---

## DRC/Linter Pass — Registered Output Check (Phase 19) — DONE

Added an automated Design Rule Check (DRC) pass that warns when output ports are driven by combinational logic rather than registers. Similar to commercial linters like SpyGlass, this catches backend-unfriendly RTL patterns (synthesis + STA issues) at compile time.

### Implementation

Pure function `checkRegisteredOutputs` analyzes `Module` IR before Verilog emission:
1. For each output port (skipping `clk`/`rst`), traces the driving statement
2. If driven by `Stmt.register` or synchronous `Stmt.memory` → pass
3. Otherwise → emit Lean warning (combinational path to output)

Integrated into all 4 synthesis commands: `#synthesizeVerilog`, `#synthesizeVerilogDesign`, `#writeVerilogDesign`, `#writeDesign`.

### Example Output

```
Tests/TestDRC.lean:17:0: warning: [DRC] Module 'drc_combo_output': output 'out' is not driven by a register (driven by wire '_tmp_result_0')
```

Registered outputs produce no warnings.

### Files

| File | Action | Description |
|------|--------|-------------|
| `Sparkle/Compiler/DRC.lean` | Created | `findDriver`, `checkRegisteredOutputs` — pure functions on `Module` IR |
| `Sparkle/Compiler/Elab.lean` | Modified | Import DRC, add `runDesignDRC`, call in 4 synthesis commands |
| `Sparkle.lean` | Modified | Added `import Sparkle.Compiler.DRC` |
| `Tests/TestDRC.lean` | Created | Combinational (warns) + registered (clean) test circuits |

### Verification

```bash
$ lake build                        # Full build — ✓
$ lake env lean Tests/TestDRC.lean  # Combo warns, registered clean — ✓
```

---

## Verification-Driven Design Framework + Round-Robin Arbiter (Phase 18) — DONE

Created a formal Verification-Driven Design (VDD) framework document and a worked example demonstrating the full workflow: pure state-machine spec with 10 formal proofs, then synthesizable Signal DSL implementation.

### Framework Document (`docs/Verification_Framework.md`)

Professional ~200-line guide covering:
1. **Bug Classification**: Safety vs Liveness with hardware examples (bus contention, starvation, deadlock)
2. **Four Proof Patterns**: Invariant, Round-trip, Responsiveness, Refinement — each with tactic recipes
3. **Worked example**: 2-client Round-Robin Arbiter (referencing the implementation files)
4. **Tactic quick-reference** for hardware engineers

### Formal Proofs (`Sparkle/Verification/ArbiterProps.lean`)

Self-contained file (follows ISAProps.lean pattern) with:
- **State machine**: `ArbiterState` (Idle/GrantA/GrantB), 12-entry `nextState` truth table
- **Output functions**: `grantA`, `grantB`
- **10 theorems**, all closing via `cases s <;> cases reqA <;> cases reqB <;> simp [...]` — zero `sorry`

| # | Theorem | Category | Statement |
|---|---------|----------|-----------|
| 1 | `mutual_exclusion` | Safety | Never both granted after transition |
| 2 | `mutual_exclusion_current` | Safety | Never both granted in any state |
| 3 | `no_spurious_grant` | Safety | No grant without request |
| 4 | `progress_A` | Liveness | A requesting → A granted or B holds |
| 5 | `progress_B` | Liveness | B requesting → B granted or A holds |
| 6 | `starvation_free_A` | Liveness | A granted within 2 cycles |
| 7 | `starvation_free_B` | Liveness | B granted within 2 cycles |
| 8 | `round_robin_A_to_B` | Fairness | GrantA + contention → GrantB |
| 9 | `round_robin_B_to_A` | Fairness | GrantB + contention → GrantA |
| 10 | `idle_tiebreak` | Fairness | Idle + contention → GrantA |

### Signal DSL Implementation (`Examples/Arbiter/RoundRobin.lean`)

Synthesizable arbiter mirroring the proven spec:
- State encoded as `BitVec 2` (0=Idle, 1=GrantA, 2=GrantB)
- `Signal.loop` + `Signal.register` for state feedback
- `===` for state comparison, `&&&`/`|||` for Bool combinators
- `hw_cond` for priority mux next-state logic
- `#synthesizeVerilog arbiterSignal` — generates clean SystemVerilog
- `#eval simTest` — simulation confirms round-robin alternation

### Generated Verilog (excerpt)

```systemverilog
module Sparkle_Examples_Arbiter_RoundRobin_arbiterSignal (
    input logic _gen_reqA,
    input logic _gen_reqB,
    input logic clk,
    input logic rst,
    output logic [1:0] out
);
    // ... combinational next-state logic (priority mux) ...
    assign _gen_nextState = (_gen_goGrantA ? 2'd1 : (_gen_goGrantB ? 2'd2 : 2'd0));

    always_ff @(posedge clk or posedge rst) begin
        if (rst) _tmp_loop_body_12 <= 2'd0;
        else     _tmp_loop_body_12 <= _gen_nextState;
    end
    assign out = _tmp_loop_body_12;
endmodule
```

### Simulation Output

```
Cycle | reqA reqB | state | grantA grantB
------+----------+-------+--------------
  0   |  false  false  | Idle   |  false    false
  1   |  true   false  | GrantA |  true     false
  2   |  true   true   | GrantB |  false    true     ← round-robin
  3   |  true   true   | GrantA |  true     false     ← alternates
  4   |  true   true   | GrantB |  false    true
  7   |  true   true   | GrantA |  true     false     ← tie-break from Idle
```

### Files

| File | Action | Description |
|------|--------|-------------|
| `Sparkle/Verification/ArbiterProps.lean` | Created | Pure state machine + 10 formal proofs |
| `Examples/Arbiter/RoundRobin.lean` | Created | Signal DSL implementation + synthesis + sim test |
| `docs/Verification_Framework.md` | Created | VDD framework document |
| `lakefile.lean` | Modified | Added `lean_lib «Examples.Arbiter»` |

### Verification

```bash
$ lake build Sparkle.Verification.ArbiterProps  # 10 proofs, zero sorry ✓
$ lake build Examples.Arbiter.RoundRobin        # Synthesis + simulation ✓
$ lake test                                      # No regressions ✓
```

---

## Compiler Tracing & Handler Extraction (Phase 17) — DONE

Refactored `Sparkle/Compiler/Elab.lean` — added Lean tracing infrastructure and broke the monolithic `translateExprToWireApp` function (~393 lines, ~20 sequential `if name == ...` arms) into 9 categorized handler functions with a clean ~25-line dispatcher. No synthesis behavior changes.

### Tracing Infrastructure

Added `initialize registerTraceClass `sparkle.compiler`` — enables structured trace output for debugging the synthesis compiler.

**Usage:**
```lean
set_option trace.sparkle.compiler true
#synthesizeVerilog myDesign
```

Trace points at:
- `translateExprToWire` entry (hint, isTopLevel)
- `translateExprToWireApp` entry (name, args.size)
- Each handler match (e.g., `→ tuple projection (fst)`, `→ register`, `→ loop`, `→ definition unfold {name}`)

### Handler Extraction

| # | Handler | Handles | ~Lines |
|---|---------|---------|--------|
| 1 | `handleErrorPatterns` | `ite`/`dite`, `Decidable.rec`/`casesOn` — throws on match | 20 |
| 2 | `handleTupleProjections` | `Signal.fst`, `Signal.snd`, `Signal.map`+`Prod.fst`/`Prod.snd` | 50 |
| 3 | `handleApplicative` | `Signal.ap` — binary op lifting, concat/sshiftRight special cases | 45 |
| 4 | `handleBitVecOps` | `extractLsb'`, shifts, concat, `isPrimitive` dispatch | 55 |
| 5 | `handleRegister` | `Signal.register`, `Signal.registerWithEnable` | 30 |
| 6 | `handleMux` | `Signal.mux`, `lutMuxTree` | 40 |
| 7 | `handleMemory` | `Signal.memory`, `Signal.memoryComboRead` | 35 |
| 8 | `handleLoop` | `Signal.loop`, `HWVector.get` | 35 |
| 9 | `handleDefinitionUnfold` | `unfoldDefinition?` → inline, fallback → sub-module synthesis | 50 |

Each handler is a `partial def` returning `CompilerM (Option String)`:
- `some wireName` → handled
- `none` → not my pattern, try next handler
- Throw → error detected

The main dispatcher chains handlers in order:
```lean
handleErrorPatterns e name args hint isNamed  -- throws or returns ()
if let some w ← handleTupleProjections e name args hint isNamed then return w
if let some w ← handleApplicative e name args hint isNamed then return w
-- ... 6 more handlers ...
if let some w ← handleDefinitionUnfold e name args hint isNamed then return w
```

### Files Changed

| File | Action | Description |
|------|--------|-------------|
| `Sparkle/Compiler/Elab.lean` | Modified | Added `registerTraceClass`, extracted 9 handlers, added trace points |

### Verification

```bash
$ lake build                          # Full build — ✓
$ lake test                           # Test suite — ✓ (all pass)
$ lake build Examples.YOLOv8.Blocks.Bottleneck  # Bottleneck synthesis — ✓
$ lake build Examples.RV32.SoCVerilog # SoC synthesis + CppSim + JIT — ✓
```

All produce identical output to pre-refactoring.

---

## `declare_signal_state` Macro (Phase 16) — DONE

Replaced error-prone manual `projN!` state indexing with a `declare_signal_state` command macro that generates synthesis-compatible accessor defs. Eliminates magic-number indices for the 122-register SoC and all smaller state tuples.

### Problem

Hardware state in the Signal DSL uses right-nested tuples (`BitVec 32 × Bool × BitVec 8 × ...`). Accessing fields requires `projN! state N i` with numeric indices:

```lean
-- 122 lines of this — one typo silently breaks the design
let pcReg := projN! state 122 0
let fetchPC := projN! state 122 1
...
let dMissIsStore := projN! state 122 121
```

Adding/removing a field requires updating ALL subsequent indices manually. A previous attempt using Lean 4 structures failed because struct constructors (`.mk`) are not `.defnInfo` — the synthesis compiler's `unfoldDefinition?` can't inline them.

### Solution

The `declare_signal_state` command macro generates synthesis-compatible `def`s (which ARE `.defnInfo`):

```lean
declare_signal_state BottleneckState
  | fsmReg      : BitVec 2   := 0#2
  | residualReg : BitVec 8   := 0#8
  | resultReg   : BitVec 8   := 0#8
  | doneReg     : Bool        := false
```

Generates:
1. **Type alias**: `abbrev BottleneckState := BitVec 2 × BitVec 8 × BitVec 8 × Bool`
2. **Accessor defs**: `BottleneckState.fsmReg`, `.residualReg`, etc. (each expands to `projN!`)
3. **Default value**: `BottleneckState.default : BottleneckState`
4. **Inhabited instance**: `instance : Inhabited BottleneckState`

Each accessor is a regular `def` → `.defnInfo` → `unfoldDefinition?` inlines it → synthesis works.

### Usage

```lean
-- Before: magic numbers everywhere
let pcReg := projN! state 122 0
let fetchPC := projN! state 122 1

-- After: named accessors, no indices
let pcReg := SoCState.pcReg state
let fetchPC := SoCState.fetchPC state
```

### Files

| File | Action | Description |
|------|--------|-------------|
| `Sparkle/Core/StateMacro.lean` | Created | `declare_signal_state` command macro |
| `Sparkle.lean` | Modified | Added `import Sparkle.Core.StateMacro` |
| `Examples/YOLOv8/Blocks/Bottleneck.lean` | Modified | Replaced Record Wrapper with macro (4 fields) |
| `Examples/RV32/SoC.lean` | Modified | Replaced 122-field `projN!` block with accessor calls |

### Verification

```bash
$ lake build Examples.YOLOv8.Blocks.Bottleneck
# Verilog successfully generated! (synthesis works through accessor defs)

$ lake build Examples.RV32.SoCVerilog
# Written 1 modules to verilator/generated_soc.sv
# Written C++ simulation to verilator/generated_soc_cppsim.h
# Written JIT wrapper to verilator/generated_soc_jit.cpp

$ lake exe rv32-flow-test
# CppSim JIT: ✓ ALL TESTS PASSED
```

---

## Signal DSL Ergonomics (Phase 15) — DONE

Improved Signal DSL readability with new operators, implicit coercions, and a hardware conditional macro. Refactored YOLOv8 Backbone to demonstrate the improvements — FSM transition logic reduced from 18 lines of nested `Signal.mux` to 9 lines of flat `hw_cond`.

### New Features (Sparkle/Core/Signal.lean)

| Feature | Syntax | Expansion | Status |
|---------|--------|-----------|--------|
| Hardware equality | `a === b` | `(· == ·) <$> a <*> b` | Synthesizes |
| Implicit BitVec lift | `(1#4 : Signal dom _)` | `Signal.pure 1#4` via `Coe` | Synthesizes |
| Implicit Bool lift | `(true : Signal dom _)` | `Signal.pure true` via `Coe` | Synthesizes |
| Hardware conditional | `hw_cond default \| cond => val` | Nested `Signal.mux` | Synthesizes |
| Bool AND | `a &&& b` | `(· && ·) <$> a <*> b` | Synthesizes (Phase 13) |
| Bool OR | `a \|\|\| b` | `(· \|\| ·) <$> a <*> b` | Synthesizes |
| Bool NOT | `~~~a` | `(fun x => !x) <$> a` | **Does NOT synthesize** |

### `hw_cond` Macro Design

Default-first syntax avoids PEG parser greedy-`|` ambiguity:

```lean
-- Syntax: hw_cond <default> | <cond₁> => <val₁> | <cond₂> => <val₂> | ...
let fsmNext := hw_cond fsmReg
  | startAndIdle  => (1#4 : Signal dom _)  -- IDLE → STEM
  | stemDone      => (2#4 : Signal dom _)  -- STEM → STAGE_CONV
  | stageConvDone => (3#4 : Signal dom _)  -- STAGE_CONV → STAGE_C2F
  | isDone        => (0#4 : Signal dom _)  -- DONE → IDLE
```

**Implementation notes:**
- Defined after `end Signal` namespace (line 649) so ``Signal.mux`` resolves correctly via double-backtick
- Uses `Lean.mkIdent ``Signal.mux` to bypass macro hygiene — prevents `_hyg.N` suffixes that would break the synthesis compiler's `name.endsWith ".mux"` check
- PEG issue: `| else =>` fails because greedy `*` repetition consumes `|` before the default branch; default-first syntax avoids this entirely

### Refactoring Demonstration (Backbone.lean)

Before (verbose):
```lean
let isIdle := (· == ·) <$> fsmReg <*> Signal.pure 0#4
let startAndIdle := (· && ·) <$> start <*> isIdle
let fsmNext :=
  Signal.mux startAndIdle (Signal.pure 1#4)
    (Signal.mux stemDone (Signal.pure 2#4)
      (Signal.mux stageConvDone (Signal.pure 3#4)
        (...10+ levels of nesting...)))
```

After (clean):
```lean
let isIdle := fsmReg === (0#4)
let startAndIdle := start &&& isIdle
let fsmNext := hw_cond fsmReg
  | startAndIdle  => (1#4 : Signal dom _)
  | stemDone      => (2#4 : Signal dom _)
  | stageConvDone => (3#4 : Signal dom _)
  | ...9 flat lines...
```

### Known Limitation: `~~~` (Complement) Does Not Synthesize

The `Complement` instance for `Signal dom Bool` (`~~~a` → `(fun x => !x) <$> a`) causes the synthesis compiler to see `Complement.mk` as a module instantiation attempt. The `unfoldDefinition?` mechanism doesn't fully reduce the typeclass instance before the compiler's expression walker encounters it.

**Workaround:** Use `(fun x => !x) <$> signal` directly (which the compiler recognizes).

**Future fix:** Add `Complement.complement` / `Complement.mk` to the synthesis compiler's unfolding list in Elab.lean.

### Files Modified

| File | Change |
|------|--------|
| `Sparkle/Core/Signal.lean` | Added `===`, `Coe` instances, `hw_cond` macro |
| `Examples/YOLOv8/Backbone.lean` | Refactored using new ergonomic features |

### Verification

```bash
$ lake build Examples.YOLOv8.Backbone
# Build completed successfully (23 jobs).
# Generated Verilog for all 3 sub-modules: c2fController, sppfController, backboneController

$ lake exe rv32-flow-test
# CppSim JIT: ✓ ALL TESTS PASSED (no regressions)
```

---

## JIT FFI Implementation (Phase 14) — DONE

Implemented JIT-accelerated simulation via dynamic compilation. The CppSim backend now generates self-contained `.cpp` files with `extern "C"` wrappers, compiled to shared libraries (`.dylib`) at runtime, and loaded from Lean via `dlopen`/`dlsym` FFI.

### Architecture

```
┌─────────────┐    #writeDesign     ┌──────────────────┐
│  Lean DSL   │ ──────────────────► │  *_jit.cpp       │
│  (Signal)   │                     │  (CppSim class + │
└─────────────┘                     │   extern "C" API)│
                                    └────────┬─────────┘
                                             │ c++ -shared
                                             ▼
                                    ┌──────────────────┐
                                    │  *.dylib          │
                                    │  (shared library) │
                                    └────────┬─────────┘
                                             │ dlopen/dlsym
                                             ▼
                                    ┌──────────────────┐
                                    │  Lean JIT.lean   │
                                    │  (eval/tick/reset │
                                    │   setMem/getWire) │
                                    └──────────────────┘
```

### Performance

- **JIT simulation**: ~1M+ cycles/sec (firmware test: 2904 cycles)
- **Interpreted loopMemo**: ~5K cycles/sec
- **Speedup**: ~200x over Lean-native simulation

### API (Sparkle.Core.JIT)

| Function | Description |
|----------|-------------|
| `JIT.compileAndLoad cppPath` | Compile `.cpp` → `.dylib` (hash-cached) and load |
| `JIT.eval handle` | Evaluate combinational logic |
| `JIT.tick handle` | Advance clock (register update) |
| `JIT.reset handle` | Reset all registers |
| `JIT.setInput handle idx val` | Set input port by index |
| `JIT.getOutput handle idx` | Get output port by index |
| `JIT.getWire handle idx` | Get named internal wire by index |
| `JIT.wireName handle idx` | Get wire name by index (for discovery) |
| `JIT.findWire handle name` | Find wire index by name |
| `JIT.setMem handle memIdx addr data` | Write to memory array |
| `JIT.getMem handle memIdx addr` | Read from memory array |
| `JIT.destroy handle` | Destroy instance (also runs on finalize) |

### Generated Wrapper (extern "C")

The `toCppSimJIT` function generates a self-contained `.cpp` with:
- Full CppSim class inlined (no header dependency)
- `jit_create/destroy/eval/tick/reset` — lifecycle management
- `jit_set_input/get_output` — port access by index
- `jit_get_wire/jit_wire_name` — named wire observation (980 wires for SoC)
- `jit_set_mem/get_mem` — direct memory access (11 memories for SoC)
- `jit_num_inputs/outputs/wires/memories` — metadata queries

### Files

| File | Action | Description |
|------|--------|-------------|
| `Sparkle/Backend/CppSim.lean` | Modified | Added `toCppSimJIT` + helpers |
| `c_src/sparkle_jit.c` | Created | dlopen/dlsym FFI with `lean_external_class` |
| `Sparkle/Core/JIT.lean` | Created | `@[extern]` opaque declarations + compile/load helpers |
| `Sparkle.lean` | Modified | Added `import Sparkle.Core.JIT` |
| `Sparkle/Compiler/Elab.lean` | Modified | `#writeDesign` now auto-emits JIT wrapper |
| `lakefile.lean` | Modified | Added `extern_lib sparkle_jit` + `rv32-jit-test` exe |
| `Tests/RV32/JITTest.lean` | Created | End-to-end JIT test with firmware |
| `verilator/Makefile` | Modified | Added `build-jit` and `run-jit` targets |

### Verification

```
$ lake exe rv32-jit-test verilator/generated_soc_jit.cpp firmware/firmware.hex 5000
JIT: Compiling verilator/generated_soc_jit.cpp...
JIT: Loaded shared library
JIT: Wire indices — pcReg=8, uartValid=979, uartData=50
JIT: Loading firmware from firmware/firmware.hex...
JIT: Running for 5000 cycles...
  UART[1]: 0xdead0001
  ...
  UART[47]: 0xcafe0000

*** ALL TESTS PASSED (cycle 2904) ***
```

### Build & Run

```bash
# Generate all outputs (SV + CppSim + JIT wrapper)
lake build Examples.RV32.SoCVerilog

# Run JIT test from Lean
lake exe rv32-jit-test verilator/generated_soc_jit.cpp firmware/firmware.hex 5000

# Build JIT shared library manually
cd verilator && make build-jit

# Run JIT test via Makefile
cd verilator && make run-jit
```

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
- [x] JIT FFI implementation (Phase 14 — done)
- [x] Signal DSL ergonomics: `===`, `Coe`, `hw_cond` macro (Phase 15 — done)
- [x] `declare_signal_state` macro — named state accessors, no magic indices (Phase 16 — done)
- [x] Compiler tracing & handler extraction — `registerTraceClass`, 9 handler functions (Phase 17 — done)
- [x] Verification-Driven Design framework + Round-Robin Arbiter — 10 formal proofs, Signal DSL implementation (Phase 18 — done)
- [x] DRC/Linter Pass — registered output check, warns on combinational outputs (Phase 19 — done)
- [ ] Fix `~~~` (Complement) synthesis — add unfolding for `Complement.mk` in Elab.lean
- [x] `loopMemoJIT` integration — transparent JIT behind Signal.loopMemo (Phase 21 — done)
- [x] Simulation performance analysis — root cause of 2.7x Verilator gap identified (Phase 22 — done)
- [ ] CppSim expression inlining — eliminate single-use `_tmp_*` wires (biggest optimization opportunity)
- [ ] CppSim constant folding — inline literal constants instead of storing as member variables
- [ ] Fix Lean simulation stack overflow on macOS (reduce tuple nesting depth or use worker thread with larger stack)
- [x] Fix Verilator testbench internal signal access — `_gen_dTLBMiss` replaced with `0` (Verilator optimizes it away)

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

### Phase 9: Verilator Testing — DONE

| # | Task | Status |
|---|------|--------|
| 1 | `#writeVerilogDesign` command in Elab.lean | Done |
| 2 | `lake build Examples.RV32.SoCVerilog` — writes `verilator/generated_soc.sv` | Done |
| 3 | `verilator/rv32i_soc_wrapper.sv` — unpack packed output | Done |
| 4 | `verilator/Makefile` — generated SV + wrapper, `make build` | Done |
| 5 | Verilator compiles generated SV successfully | Done |
| 6 | Firmware test: sections 1-9 match hand-written reference exactly (45 UART words) | Done |
| 7 | Firmware test: section 10 + pass marker (`0xcafe0000`) — ALL 48 UART words, cycle 2904 | Done |
| 8 | Linux boot test (OpenSBI → kernel → UART output) | Done (Phase 20) |

### Compiler Bugs Fixed During Phase 9

| Bug | Fix |
|-----|-----|
| `bundle2` hardcoded wire width to 16 bits | Infer from expression type via `inferHWTypeFromSignal` |
| `Prod.fst` slice assumed equal-width halves (`width * 2 - 1`) | Use `getWireWidth` for actual source wire width |
| Verilog backend: duplicate wire/port declarations | Filter port names from internal wire list |
| Core.lean: complex lambda `(fun f7 => extractLsb' 5 1 f7 == 1#1)` | Split into extract + compare steps |

---

## Linux Boot Hang Debugging — RESOLVED

### Symptoms (before fix)

- **Hand-written SV**: Boots Linux 6.6.0 successfully (3944 UART bytes in ~7M cycles)
- **Generated SV**: Hung at ~1906 UART bytes, PC stuck at 0xC0001C88 (recursive page fault)
- OpenSBI phase worked correctly (same output as hand-written)
- Kernel started, printed banner and initial messages, then hung

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

### Resolution Timeline

- [x] ~~**Fix holdEX in SoC.lean**~~ — Done (Phase 13)
- [x] ~~**Verify Linux boots on fixed generated SoC**~~ — Done (Phase 20): 5250 UART bytes, matches hand-written SV behavior
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

### Next Phases

1. **CppSim Backend Optimization** — Close the 2.7x gap with Verilator by optimizing the generated C++:
   - **Expression inlining**: Eliminate single-use `_tmp_*` wires by folding them into consumer expressions (biggest impact — would cut assignments from 2242 to ~800)
   - **Constant folding**: Inline literal constants (`0`, `1`, bit masks) instead of storing as member variables
   - **Sized types**: Use `uint8_t`/`uint32_t` instead of `uint64_t` + runtime masking
   - **Memory deduplication**: Eliminate duplicate register file and DRAM arrays for multi-port reads
   - **If-else for reset/WE**: Use `if` blocks instead of ternary for reset paths (enables branch prediction skip)

2. **Verified Standard IP Library** — Formally proven, synthesizable components:
   - FIFO buffers (overflow/underflow safety proofs)
   - Cache controllers (coherence proofs)
   - AXI4/TileLink bus protocol wrappers (deadlock-free proofs)

3. **GPGPU / Vector Core** — Apply VDD framework to highly concurrent, memory-bound accelerator architectures. Thread-level parallelism + shared memory = ideal target for safety/liveness proofs.

4. **FPGA Tape-out Flow** — Deploy Sparkle-generated Linux SoCs to physical FPGAs (Gowin Tang Nano, Xilinx PYNQ, etc.).

### Completed
- [x] ~~Transparent JIT (`loopMemoJIT`)~~ — Done (Phase 21): Signal API + Streaming API, 47 UART words pass
- [x] ~~Simulation performance analysis~~ — Done (Phase 22): Root cause identified (2x instruction count + 1.38x IPC)
- [x] ~~Verify Linux boots on fixed generated SV~~ — Done (Phase 20): 5250 UART bytes, kernel init progressing
- [x] ~~Fix Verilator testbench internal signal references~~ — `_gen_dTLBMiss` replaced with `0`

### Backlog (lower priority)
- [ ] Fix `~~~` (Complement) synthesis — add typeclass unfolding for `Complement.mk` in Elab.lean
- [ ] More DRC rules — clock domain crossing, combinational loop detection, undriven wire detection
- [ ] Apply `declare_signal_state` to remaining state tuples (Divider, Backbone, C2f, SPPF, Neck, Head)
- [ ] Fix Lean simulation stack overflow on macOS (reduce tuple nesting depth or use worker thread)
- [ ] Run Linux boot for more cycles (both generated and hand-written need >10M cycles to reach shell)
- [ ] Fix CppSim >64-bit output port assignment (currently skipped, `getOutput` returns 0 for packed outputs)

---

## Build & Test Commands

```bash
# Lean build (SoC simulation)
lake build Examples.RV32.SoC

# Lean build (Verilog synthesis → writes SV + CppSim + JIT wrapper)
lake build Examples.RV32.SoCVerilog

# JIT test (compile, load, run firmware from Lean)
lake exe rv32-jit-test verilator/generated_soc_jit.cpp firmware/firmware.hex 5000

# JIT loop test (loopMemoJIT Signal API + Streaming API)
lake exe rv32-jit-loop-test verilator/generated_soc_jit.cpp firmware/firmware.hex 5000

# CppSim test (standalone C++)
cd verilator && make build-cppsim && make run-cppsim CYCLES=5000

# Verilator build (generated SV + wrapper)
cd verilator && make build

# Verilator build (hand-written SV, reference)
cd verilator && make build-handwritten

# Firmware test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000

# JIT shared library build (manual)
cd verilator && make build-jit

# Linux boot test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
```
