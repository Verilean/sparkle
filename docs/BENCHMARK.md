# Sparkle RV32I SoC — Benchmark Results

Benchmark comparison of Verilator, CppSim, and JIT simulation backends.

## Quick Start

```bash
# Run all benchmarks (Verilator + JIT side-by-side)
cd verilator && ./bench.sh

# Custom cycle count
cd verilator && ./bench.sh 50000000

# Individual benchmarks
cd verilator && ./verilator_bench ../firmware/firmware.hex 10000000
cd verilator && ./jit_bench ../firmware/firmware.hex 10000000 generated_soc_jit.dylib

# Build benchmarks from scratch
cd verilator && make bench CYCLES=10000000
```

## Results — RV32I SoC (10M cycles, Sparkle-native design)

| Backend | Speed (cyc/s) | vs Verilator |
|---------|--------------|-------------|
| **Sparkle JIT evalTick** | **14.0M** | **1.60x** |
| Verilator 5.040 (no trace) | 8.76M | 1.00x |
| Verilator 5.040 (with trace) | 7.06M | 0.81x |

## Results — LiteX PicoRV32 SoC (10M cycles, 1730-line real-world design)

| Backend | Speed (cyc/s) | vs Verilator |
|---------|--------------|-------------|
| **Sparkle JIT evalTick** | **9.76M** | **0.91x** |
| Verilator 5.040 (-O2) | 10.70M | 1.00x |
| **Sparkle + Timer Oracle** | **48.9 GHz** | **~4,600x** |

Note: Previous 11.5M figure was from incomplete SSA (missing case default
branch changes). The 9.76M figure uses correct SSA with full CSR write support,
verified by LiteX firmware execution (timer countdown).

### Optimization Impact (LiteX SoC, cumulative, correct SSA)

| Phase | Optimization | cyc/s | vs Verilator |
|-------|-------------|-------|-------------|
| Baseline (correct SSA) | Full case SSA merge | 8.17M | 0.79x |
| +Debug wire elimination | Remove PicoRV32 debug/trace from IR | 8.49M | 0.82x |
| +Extended decoder guard | instr_, alu_, is_compare keywords | **9.76M** | **0.91x** |

### Timer Oracle (Proof-Driven Temporal Skip)

| Mode | Effective Speed | Speedup |
|------|----------------|---------|
| Normal simulation | 5.04M cyc/s | 1x |
| Timer oracle (countdown skip) | **48.9 GHz** | **9,707x** |

Timer oracle detects countdown timer (timer_value) and skips ahead by
timer_value cycles when CPU is idle. Verified with LiteX firmware that
sets TIMER_LOAD=100000, TIMER_EN=1 via CSR bus.

### Multi-Core Scaling (LiteX N-core, hierarchical instantiation)

| Cores | Sparkle Hierarchical | Sparkle Flat | Verilator (wrapper) |
|-------|---------------------|-------------|---------------------|
| 1 | 11.6M | 10.8M | 32.9M |
| 2 | 11.9M | 10.7M | 35.3M |
| 4 | 12.0M | 10.7M | 35.2M |
| 8 | 11.8M | 10.8M | 35.3M |

With proper module hierarchy (10 C++ classes) and shared bus
(all cores active, no dead code elimination possible):

| Cores | Verilator | Sparkle | Ratio |
|-------|-----------|---------|-------|
| 1 | 10.34M | **11.65M** | **1.13x** |
| 2 | 6.05M | 5.66M | 0.94x |
| 4 | 2.74M | **2.85M** | **1.04x** |
| 8 | 1.06M | **1.45M** | **1.37x** |

Both simulators degrade with core count (D-cache pressure from instance data).
Sparkle degrades more slowly due to instruction sharing via function calls.

### Why Sparkle Beats Verilator

1. **Wire localization**: All combinational wires as stack-local variables (L1 cache)
2. **Conditional subgraph guards**: decoder_trigger and pcpi_valid skip inactive logic
3. **Self-referencing register optimization**: 156/303 registers use if-else instead of ternary
4. **Aggressive constant propagation**: IR-level const/alias elimination before codegen
5. **Fused evalTick**: Single function with all wire+register locals on stack

## Profile Analysis (macOS `sample` profiler, 50M cycles)

### JIT Profile

| Component | Samples | % | Notes |
|-----------|---------|---|-------|
| `eval()` | 1906 | 74.7% | Combinational logic |
| `tick()` | 608 | 23.8% | Register updates |
| `jit_get_wire` | 3 | 0.1% | Wire reads (negligible) |
| `main` loop overhead | 33 | 1.3% | Loop, dlsym calls |

**Takeaway**: `eval()` dominates at 74.7%. This is the combinational logic
computation (ALU, decoder, hazard logic, TLB, page table walker, etc.).
Optimization should focus on reducing the instruction count of `eval()`.

### Verilator Profile

| Component | Samples | % | Notes |
|-----------|---------|---|-------|
| `nba_sequent__TOP__1` | 1033 | 41.1% | Sequential (register updates) |
| `nba_comb__TOP__0` | 530 | 21.1% | Combinational logic |
| `eval()` overhead | 151 | 6.0% | Eval dispatch |
| `nba_sequent__TOP__0` | 79 | 3.1% | Secondary sequential |
| `ico_sequent__TOP__0` | 40 | 1.6% | Initial-cycle only |
| `VlDeleter/mutex` | 187 | 7.4% | **Thread sync overhead** |
| `__psynch_cvwait` | — | — | Idle thread wait (excluded) |

**Takeaway**: Verilator wastes ~7.4% on mutex/thread synchronization
overhead (even in single-threaded mode). The JIT has zero thread overhead,
contributing to its 1.2x advantage.

## Why JIT is Faster Than Verilator

1. **No thread synchronization** — JIT is single-threaded with no mutex/lock overhead.
   Verilator 5.x uses a thread pool even for single-threaded workloads, wasting 7.4%
   on `VlDeleter::deleteAll()` → `std::mutex::try_lock()`.

2. **Observable wire optimization** — JIT has only 33 class member variables + 321
   `eval()`-local variables (L1-cache friendly). Verilator keeps all signals as
   class members (~1000+).

3. **Fewer CPU instructions per cycle** — The CppSim IR optimizer inlines single-use
   wires, folds constants, and eliminates dead code. Result: fewer memory operations
   per simulation cycle.

4. **Fused evalTick** — Register `_next` values stay on the stack instead of being
   written to class members then read back.

## Bottleneck Analysis

### Current Bottleneck: `eval()` (74.7%)

The `eval()` function computes all combinational logic per cycle. At 13M cyc/s
this means ~77ns per cycle, of which ~57ns is spent in `eval()`.

**Optimization opportunities**:

| Optimization | Expected Impact | Difficulty |
|-------------|----------------|------------|
| Expression inlining in `eval()` | 10-20% | Medium |
| Memory access pattern optimization | 5-10% | Low |
| SIMD for parallel ALU ops | 5-15% | High |
| Partial evaluation (skip unused paths) | 10-30% | High |

### tick() Overhead (23.8%)

`tick()` copies `_next` register values to current state. With 130 registers,
this is ~130 memory copies per cycle. The fused `evalTick()` partially
mitigates this by keeping `_next` values on the stack.

## Cycle-Skipping Oracle Performance

When idle-loop detection is enabled via `mkSelfLoopOracle`:

| Mode | Effective Speed | Real Cycles | Skipped |
|------|----------------|-------------|---------|
| No oracle | 13.0M cyc/s | 10M | 0 |
| Fixed skip (1000) | ~1.25B eff cyc/s | 10M | 9,998K |
| Timer-compare skip | ~5.0B eff cyc/s | 10M | 10M |

The timer-compare-aware oracle (`skipToTimerCompare := true`) computes
`min(mtimecmp - mtime, maxSkip)` to advance time precisely, enabling
Linux boot where the CPU wakes via timer interrupt.

## Reproducing

### Prerequisites

```bash
# macOS
brew install verilator

# Build all simulation backends
cd verilator
make build          # Verilator
make build-cppsim   # CppSim
make build-jit      # JIT shared library
```

### Running Benchmarks

```bash
# Unified benchmark (recommended)
cd verilator && ./bench.sh 10000000

# Rebuild and run
cd verilator && make bench CYCLES=10000000

# JIT bench with detailed profiling
cd verilator && make build-jit && \
  clang++ -O2 -std=c++17 -o jit_bench tb_jit_bench.cpp -ldl && \
  ./jit_bench ../firmware/firmware.hex 10000000 generated_soc_jit.dylib

# Verilator minimal bench
cd verilator && ./verilator_bench ../firmware/firmware.hex 10000000

# macOS profiling (run in separate terminal)
./jit_bench ../firmware/firmware.hex 50000000 generated_soc_jit.dylib &
sample $! 3 -file /tmp/jit_profile.txt
```

### Linux Boot Benchmark

Requires external builds of OpenSBI and Linux kernel:

```bash
# Verilator Linux boot
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image

# JIT with boot oracle (timer-compare-aware idle-loop skipping)
lake exe rv32-jit-boot-oracle-test
```
