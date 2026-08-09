# Systolic-array SIM PoC — does PE-per-thread on the GPU scale?

## The question

PR #115 added a CUDA **batch** backend: N independent instances, 1 instance per
thread. That is a Monte-Carlo / fuzzing engine — you can always get the same
throughput by adding machines, and a *single* instance is slower than on the
CPU. Not the interesting case.

The interesting case is a **single large accelerator** (a TPU-like systolic
array + a bank of RISC-V cores, ~1000 PEs, wired together) whose *one* instance
you want to simulate faster. That needs a different scheduler: **1 PE = 1
thread**, with a barrier between the read and latch phases of each clock cycle
(#33's "Strategy 4"). Adding machines does *not* replace this — it makes one
array faster by running its PEs concurrently.

This PoC measures whether that scheduler actually scales, on the cleanest
possible DUT, **before** committing to emitter work.

## DUT

Weight-stationary int8 MAC systolic array, `N x N` PEs (`systolic_common.h` is
the golden cycle model shared by both implementations):

- `PE[i][j]` holds a fixed int8 weight; each cycle it reads an activation from
  the left and a partial sum from above, computes `p_out = p_in + a_in*w`,
  passes the activation right and the partial sum down.
- Two-phase per cycle: read all neighbours' *previous* registered outputs, then
  latch. That read-then-latch structure is exactly what forces a
  `__syncthreads()` between phases on the GPU.

## Implementations (same circuit, two schedulers)

| file | scheduler |
|---|---|
| `systolic_cpu.cpp` | serial — one thread walks every PE each cycle (CSim-equivalent) |
| `systolic_gpu.cu` | persistent kernel — 1 PE = 1 thread, one block per array, `__syncthreads()` per phase; state in shared memory, two barriers/cycle, no global traffic |

Block-size limit: one block owns the whole array so the barrier covers all PEs,
and a block caps at 1024 threads → `N ≤ 32` (16×16=256, 32×32=1024). `N=64`
(4096 PEs) needs a grid-wide barrier (cooperative groups) or multi-block
tiling — deliberately the *next* step; this PoC answers the 16→32 scaling
question.

## Run

```
./run.sh                 # builds what it can; CPU always, GPU if nvcc present
CYCLES=200000 ./run.sh
ARCH=sm_80 ./run.sh      # override the GPU arch (default sm_89 = RTX 40xx)
```

`run.sh` puts `/run/opengl-driver/lib` on `LD_LIBRARY_PATH` — on NixOS the
real `libcuda.so.1` lives there, and `cudart_static` dlopens it at run time,
so without it a CUDA binary fails with "driver version insufficient" even
though the GPU is fine. Also make sure the `nvcc` toolkit version is ≤ the
driver's CUDA version (`nvidia-smi` top-right); a newer toolkit's runtime is
rejected by an older driver.

## Correctness

Verified without a GPU: a host emulation of the exact per-thread kernel logic
(two-phase barrier over all tids) produces the **same** output checksum as the
serial golden model for N = 16, 32, 64. So on a real GPU the benchmark compares
correct-against-correct; `run.sh` re-checks the `checksum=` fields match at run
time. The `.cu` also passes a host `g++ -fsyntax-only` (nvcc-free).

## Reading the result

`PE-upd/s = cyc/s × N²` is the fair "work done" metric across sizes.

- **CPU**: PE-upd/s stays ~flat as N grows (serial — bigger array, proportionally
  slower per cycle). Measured: ~1.6–2.2e9 PE-upd/s across N=16/32/64.
- **GPU**: PE-upd/s *rises* with N as more PEs run concurrently — that rise is
  the justification for the emitter work. **Confirmed** below (2.85e9 → 4.95e9
  from N=16 to N=32). Had it stayed flat or fallen, Strategy 4 would not be
  worth building and the batch backend would be the right stopping point.

## Results

RTX 4070 Ti (sm_89, 60 SMs), `nvcc 12.6 -O3 -std=c++17`, driver 565.77 /
CUDA 12.7, CPU `g++ -O3`, cycles = 200000. Every checksum matched the serial
golden model. Two GPU schedulers:

- **1-block** (`systolic_gpu.cu`): whole array in one block, `__syncthreads()`
  per phase. Cheap barrier, but N≤32 (1024 threads/block) and only 1 SM used.
- **grid-sync** (`systolic_gpu_grid.cu`): array spread over many blocks/SMs,
  cooperative-groups `grid.sync()` per phase, double-buffered global state.
  Scales past N=32 and uses the whole GPU, but the grid barrier is expensive.

| N | PEs | CPU PE/s | 1-block PE/s | grid PE/s | CPU cyc/s | grid cyc/s |
|---|----:|---:|---:|---:|---:|---:|
| 16 | 256 | 1.49e9 | **2.85e9** | 2.30e8 | 5.8e6 | 9.0e5 |
| 32 | 1024 | 2.11e9 | **5.44e9** | 9.18e8 | 2.1e6 | 9.0e5 |
| 64 | 4096 | 1.85e9 | — | 3.64e9 | 4.5e5 | 8.9e5 |
| 128 | 16384 | 1.67e9 | — | 1.45e10 | 1.0e5 | 8.9e5 |
| 256 | 65536 | 8.9e8 | — | **4.34e10** | 1.4e4 | 6.6e5 |

`PE/s = cyc/s × N²` (work done); `cyc/s` = simulated clocks per second (how
fast one run advances).

## Verdict — three regimes

1. **CPU**: PE/s flat (serial ceiling), `cyc/s` collapses as N² — N=256 does
   1.4e4 cyc/s, effectively unusable for a large array.
2. **1-block GPU (N≤32)**: `__syncthreads()` is cheap, so **`cyc/s` is
   highest** (5.4e6 at N=32, 2.6× CPU). Best when the array fits one block and
   you want a single run to finish fast.
3. **grid-sync GPU (N≥64)**: `cyc/s` is pinned ~9e5 by the grid-barrier
   latency, but **PE/s scales linearly with PE count** — N=256 hits 4.34e10
   PE/s, **49× the CPU**. Best for throughput on a large array.

So the answer to "can this speed up a real ~1000-PE accelerator?": **yes**, and
the bigger the design the more decisively GPU wins. A 1000-PE array is around
N=32 here — take the 1-block path (5.4e6 cyc/s, 2.6× CPU) if latency of a
single run matters, or grid-sync for raw PE throughput. Past a few thousand PEs
the CPU is simply not in the race (N=256: GPU 4.34e10 vs CPU 8.9e8 PE/s).

The grid `cyc/s` ceiling (~9e5) is the one thing to improve: it is dominated by
two `grid.sync()` per simulated cycle. Coarsening the barrier (multiple
sim-cycles between syncs where the dependency depth allows) or a persistent
megakernel with a lighter cross-SM barrier is the lever — noted for later, not
needed to justify the backend.

## Next step

**Emit these kernels from Sparkle IR.** Port the deferred `CudaDesignStateStruct`
hierarchical path (PR #33) onto CSim so the wire-copy between module boundaries
is *generated*, not hand-written — turning this PoC into a real backend for
single-large-design simulation (systolic array + RISC-V bank), picking the
1-block vs grid-sync scheduler by array size.
