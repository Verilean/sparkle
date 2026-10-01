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
```

## Correctness

Verified without a GPU: a host emulation of the exact per-thread kernel logic
(two-phase barrier over all tids) produces the **same** output checksum as the
serial golden model for N = 16, 32, 64. So on a real GPU the benchmark compares
correct-against-correct; `run.sh` re-checks the `checksum=` fields match at run
time. The `.cu` also passes a host `g++ -fsyntax-only` (nvcc-free).

## Reading the result

`PE-upd/s = cyc/s × N²` is the fair "work done" metric across sizes.

- **CPU**: PE-upd/s stays ~flat as N grows (serial — bigger array, proportionally
  slower per cycle). Measured here: ~1.8e9 PE-upd/s, flat across N=16/32/64.
- **GPU (hypothesis)**: PE-upd/s should *rise* with N as more PEs run
  concurrently — that rise is the whole justification for the emitter work. If
  it stays flat or falls (barrier/occupancy dominates), Strategy 4 is not worth
  building and the batch backend is the right stopping point.

## Results

RTX 4070 Ti, `nvcc -O3` (12.6), 3×10⁶ cycles, checksums equal:

| N | PEs | CPU PE-upd/s | GPU PE-upd/s | GPU/CPU |
|---|----:|---:|---:|---:|
| 16 | 256 | 2.1e9 | 2.9e9 | 1.3 |
| 32 | 1024 | 2.3e9 | 5.4e9 | 2.4 |
| 64 | 4096 | 1.9e9 | (needs grid-sync) | — |

GPU throughput rises 1.9× from N=16 to N=32 while the CPU stays flat: the
decision rule below is met. The kernel Sparkle now EMITS for the same kind
of array is measured in `docs/CudaIntraSim-design.md` §10.

**Decision rule**: if GPU PE-upd/s rises 16→32 and clears the CPU by a healthy
margin at N=32, proceed to (1) grid-sync for N≥64, then (2) emit this kernel
from Sparkle IR — porting the deferred `CudaDesignStateStruct` hierarchical path
onto CSim so the wire-copy between module boundaries is generated, not
hand-written.
