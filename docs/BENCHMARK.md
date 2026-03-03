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

## Results (10M cycles, firmware.hex, Apple M4 Max)

| Backend | Speed (cyc/s) | vs Verilator |
|---------|--------------|-------------|
| **JIT evalTick (fused)** | **13.0M** | **1.22x** |
| JIT eval+tick (pure) | 13.0M | 1.22x |
| JIT eval+tick + 6 wire reads | 12.2M | 1.15x |
| JIT evalTick + 6 wire reads | 12.7M | 1.19x |
| Verilator 5.044 | 10.6M | 1.00x |

### JIT Wire Read Overhead

| Wires read/cycle | Speed (cyc/s) | Overhead |
|-----------------|--------------|----------|
| 0 (pure) | 13.0M | — |
| 1 (PC only) | 12.9M | 0.7% |
| 6 (SoCOutput) | 12.2M | 6.3% |

### JIT Fused evalTick Speedup

| Mode | eval+tick | evalTick | Speedup |
|------|-----------|----------|---------|
| Pure (no wires) | 768 ms | 771 ms | ~1.00x |
| With 6 wires | 816 ms | 788 ms | 1.04x |

Fused `evalTick()` keeps register `_next` values as stack-local variables,
eliminating ~260 intermediate memory operations per cycle. The speedup is
modest (1-4%) because Clang -O2 already promotes class members to registers
for simple workloads. Larger gains expected on Linux boot (higher register pressure).

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
