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

RTX 4070 Ti (sm_89), `nvcc -O3 -std=c++17`, driver 565.77 / CUDA 12.7,
CPU `g++ -O3`, cycles = 200000, checksums matched CPU exactly for every N:

| N | PEs | CPU PE-upd/s | GPU PE-upd/s | GPU/CPU |
|---|----:|---:|---:|---:|
| 16 | 256 | 1.64e9 | 2.85e9 | 1.7× |
| 32 | 1024 | 2.21e9 | 4.95e9 | 2.2× |
| 64 | 4096 | 1.89e9 | (needs grid-sync) | — |

**Verdict: proceed.** GPU PE-upd/s *rises* with the array (2.85e9 → 4.95e9)
while the CPU stays flat (~1.6–2.2e9, the serial ceiling), and GPU/CPU widens
1.7× → 2.2× from N=16 to N=32. That rise is the signature of genuine
within-instance parallelism — the thing you cannot buy by adding machines,
unlike the batch backend in #115.

Caveats (why 2.2× is a floor, not the ceiling):

- One block = one SM, so N≤32 uses a *single* SM of the 4070 Ti's 60. The
  win is real but the GPU is 98% idle. The payoff scales with array size, and
  the array that unlocks the *other* SMs is exactly the one a single block
  can't hold.
- **N=64 (4096 PEs) is the gate.** It exceeds 1024 threads/block, so it needs
  a grid-wide barrier (cooperative groups) or multi-block tiling — which is
  also what finally spreads the work across all SMs. That is the next step,
  and where the interesting speedup should appear.

## Next steps

1. **Grid-sync N≥64** (cooperative-groups `grid.sync()` or a multi-block tile
   with a global barrier), so one array spans many SMs. Re-measure the sweep
   out to N=128/256 — this is where GPU/CPU should jump well past 2×.
2. **Emit this kernel from Sparkle IR.** Port the deferred
   `CudaDesignStateStruct` hierarchical path (PR #33) onto CSim so the
   wire-copy between module boundaries is *generated*, not hand-written —
   turning this PoC into a real backend for single-large-design simulation
   (systolic array + RISC-V bank).
