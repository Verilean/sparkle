# Design: within-instance CUDA scheduling (`toCudaIntraDesign`)

Status: **v1 implemented** (`Sparkle/Backend/CudaIntra.lean`), co-simulated
cycle-exact against the CSim CPU reference on an RTX 4070 Ti (2×2 and 16×16
meshes, per-cycle and single-launch — `lake exe cuda-intra-cosim`). Builds on
the batch backend (#115), hierarchical emission (#117), and the measurements
in `bench/systolic/` (#116).

## 1. Goal

`toCudaSimDesign` parallelises *across* design instances: one GPU thread
simulates one whole design (batch / Monte-Carlo). This backend parallelises
*within* one instance: **each top-level `.inst` (a PE, a core) becomes one GPU
thread**, with barriers marking the phases of each simulated clock cycle —
#33's "Strategy 4". This is the axis that makes a *single large* accelerator
(systolic array + RISC-V bank, 1000+ PEs) simulate faster, which adding
machines cannot do.

`bench/systolic/` measured the ceiling with hand-written kernels:

- single block (`__syncthreads`, M ≤ 1024 PEs): 5.3×10⁶ cyc/s at 1024 PEs,
  2.4× CPU (re-measured, see `bench/systolic/README.md`);
- grid-sync (cooperative groups, any M): reported as cyc/s pinned ~9×10⁵ by
  the barrier and PE-throughput linear in M (49× CPU at 65536 PEs). That
  variant is not in `bench/systolic/` and was not re-measured; §10 has the
  grid numbers of the generated kernel.

## 2. The core problem: cross-instance timing

CSim's top `eval_tick` runs instances **sequentially in body order**,
interleaving input copies, `eval`, and output copies. An instance can
therefore observe *same-cycle* combinational outputs of instances that ran
before it. Any parallel schedule must reproduce this observable behaviour.

Two naive schedules fail:

- *"eval everything in parallel, then copy outputs to inputs, then tick"* —
  a consumer's eval at cycle *c* uses inputs copied at cycle *c−1*, i.e. the
  producer's output as of *c−1*. CSim gives it the producer's output as of
  *c*. **Off by one.**
- *"copy inputs, then eval in parallel"* — the copy reads the producer's
  output **field**, which still holds last cycle's value until the producer's
  eval runs. **Also off by one**, just moved.

Definitions:

- A producer output port is a **Moore output** if its value does not
  combinationally depend on any of the producer's input ports — it is a
  function of the producer's registers/memories/constants only.
- A design is **Moore-bounded** if every cross-instance connection taps a
  Moore output.

Systolic arrays are Moore-bounded by construction (PE outputs are registered);
so are typical core banks (registered interconnect). Mealy boundaries
(combinational paths *through* a module, e.g. a combinational ALU instance)
need level-ordered evaluation — deferred to v2, see §7.

## 3. The schedule: two phases, eval twice

Each instance's outputs are Moore — a function of its registers alone — so
they can be recomputed right after the clock edge, and consumers can fetch
them in a separate phase:

```
once per launch (prologue):
  [one thread per instance]  eval            — outputs of the current state
  barrier
  [spread over threads]      every connection, constant and top-input slice
  barrier

per simulated cycle:
  Phase 1 [one thread per instance, own struct only]:
      sparkle_<Mod>_eval_tick(&inst)   — clock edge, using the inputs pulled
                                         in the previous phase 2
      publish                          — the top outputs this instance drives
      sparkle_<Mod>_eval(&inst)        — output fields of the NEW state
  barrier
  Phase 2 [one thread per instance]:
      pull                             — own input fields ← producers' output
                                         fields
  barrier   (loop)
```

**Why eval twice is sound.** CSim's `eval` is idempotent and register-pure:
registers latch only in `tick` (`_next → current`), memory writes happen only
in `tickBody`, and sync-read address latches are last-write-wins (verified
against `CSim.lean`'s `.register`/`.memory` emission). Phase 1's second eval
runs with inputs that are one phase stale — its next-state results are
garbage, but they live in `_next`/locals and are **recomputed** by the next
cycle's `eval_tick` before anything latches. Only its Moore-output fields are
consumed (phase 2), and those depend only on the registers just latched.

**Cycle-exactness vs CSim (Moore-bounded case).** When instance B evals in
CSim at cycle *c*, its input holds the producer's output computed at cycle *c*
from registers latched at the end of *c−1*. Here, B's `eval_tick` at cycle *c*
reads the input it pulled in phase 2 of cycle *c−1*, which is the producer's
output field written by the producer's second eval of cycle *c−1* — computed
from the registers latched at the end of *c−1*. The prologue establishes the
same invariant for the first cycle of a launch. Top outputs are published
between `eval_tick` and the second eval, i.e. they hold the values CSim's
`eval_tick` leaves in the struct (the pre-edge evaluation).

**Race-freedom.** Phase 1: a thread writes only its own instance struct and
the top-output bytes it owns (each top output byte has one producer); it reads
nothing else. Phase 2: a thread writes only its own input fields (each has one
writer) and reads other instances' output fields, which nobody writes in
phase 2. Top inputs are read-only for the whole launch.

**What it costs, and what it saved.** Two barriers per cycle instead of the
first version's three (eval / copy / eval_tick), and the copies moved from one
table spread over all threads to per-instance lists. The second eval is ~12 %
of the cycle on the MAC mesh; splitting CSim's emission into `eval_outputs` /
`eval_state` would remove it (another `funcQual`-style parameter).

**Where the state lives.** The block kernel copies the whole top struct, and
the pull/publish tables, into shared memory when they fit (the device's
opt-in shared-memory limit), runs every cycle there, and copies the struct
back. Per-thread constants (instance offset, kind, list ranges) are read from
the tables once, before the cycle loop, and field copies are typed — a
variable-length `memcpy` is a byte loop on the GPU. The grid kernel (more than
1024 instances) runs on global memory.

**Rejected alternative** (for the record): Moore-alias resolution — copy
`consumer.a_in = producer.a_reg` directly by chasing `a_out := a_reg` chains
in the producer. One eval per cycle, but needs expression-inlining machinery
and restricts cross-boundary outputs to register *aliases* (a computed Moore
output like `a_reg + 1` fails).

## 4. Scaling: data-driven tables, not giant switches

A 16K-PE top must not emit a 16K-case `switch` in the kernel. Everything is
tables of `offsetof` expressions — compile-time constants, no layout math in
Lean:

```c
// one entry per top-level instance
static __device__ const size_t Top_inst_off[M] = {
  offsetof(struct Top, pe_0_0), offsetof(struct Top, pe_0_1), ... };
static __device__ const unsigned char Top_inst_kind[M] = { 0, 0, ... };
// kind → eval / eval_tick dispatch (one switch over MODULE TYPES, not instances)

// one entry per connection (Phase B)
typedef struct { size_t dst, src; unsigned bytes; } SparkleCopy;
static __device__ const SparkleCopy Top_copies[] = {
  { offsetof(struct Top, pe_0_1) + offsetof(struct PE, a_in),
    offsetof(struct Top, pe_0_0) + offsetof(struct PE, a_out), 4 },
  { offsetof(struct Top, pe_0_0) + offsetof(struct PE, a_in),
    offsetof(struct Top, ain_0),                               4 },  // top input
  ... };
typedef struct { size_t dst; unsigned bytes; unsigned long long v; } SparkleImm;
static __device__ const SparkleImm Top_imms[] = { ... };  // const-driven inputs
```

Kernel body (templated on the cooperative-groups group type so the same body
serves both barrier scopes):

```c
template <typename Group>
__device__ void Top_intra_cycles(Group g, struct Top* self,
                                 unsigned M, long cycles) {
  unsigned t = g.thread_rank();          // block: threadIdx; grid: global tid
  for (long c = 0; c < cycles; ++c) {
    if (t < M) intra_eval(self, t);      // Phase A (dispatch by kind)
    g.sync();
    for (i = t; i < nCopies; i += g.size()) do_copy(self, Top_copies[i]);
    for (i = t; i < nImms;   i += g.size()) do_imm (self, Top_imms[i]);
    g.sync();
    if (t < M) intra_eval_tick(self, t); // Phase C
    g.sync();
  }
}
__global__ void Top_intra_block_kernel(struct Top*, long);       // M ≤ 1024
__global__ void Top_intra_grid_kernel (struct Top*, long);       // cooperative
```

Copies are `memcpy(dst, src, bytes)` over `char*` offsets — uniform for
scalar and wide (word-array) fields, no per-width code.

## 5. Host API

Reuses the batch `CudaHandle` with N = 1 — `jit_cuda_alloc(1)`,
`jit_cuda_set_input` / `jit_cuda_get_output` (instance 0) work unchanged. One
new entry point:

```c
void jit_intra_run(void* handle, long numCycles);
```

H→D copy, then: if M ≤ 1024 and the state fits, launch the block kernel;
otherwise check cooperative-launch support + occupancy
(`cudaOccupancyMaxActiveBlocksPerMultiprocessor`) and use
`cudaLaunchCooperativeKernel`; D→H copy. Emitted `.cu` = the batch `.cu`
(device code + batch kernel + batch host API) **plus** the intra tables,
kernels, and `jit_intra_run` — one `.so` serves both axes. Compiling the
intra variant needs `-rdc=true` (cooperative groups).

Entry point: `toCudaIntraDesign (d : Design) : Except String String`, plus a
`String`-valued wrapper that renders an error as `#error "..."` in the `.cu`
so a build-time generation failure is loud. Lives in a new
`Sparkle/Backend/CudaIntra.lean`, importing `CudaSim`.

## 6. v1 restrictions — each detected with a named error

| restriction | error names | workaround / v2 |
|---|---|---|
| Moore-bounded boundaries only | the connection + the comb path (output ← inputs) | register the output; v2 = levelization (§7) |
| an instance input is a `.ref` (top wire/port, chased transitively), a `.const`, or a slice of a TOP INPUT (≤ 64 bits; applied once per launch) | the connection expr | materialize the expr in a top wire driven by a submodule; v2 = inline eval |
| a top output is one of those, or a (nested) concatenation of byte-aligned ones | the output and the element | pack it in a submodule |
| top module body: `.assign` (const/ref chains, the slices and concatenations above) + `.inst` only — no `.register`/`.memory`/other comb logic at top | the offending Stmt | push it into a submodule |
| combinational loop through connection chains | the cycle | — (always an error) |

Notes:
- `clk`/`rst` connections are copied uniformly like any input field —
  exactly what CSim's `.inst` lowering does; no special-casing.
- Nested hierarchies are fine: a top-level `.inst` whose module contains its
  own `.inst`s runs entirely inside its thread (CSim's eval recurses).
  Thread granularity = **top-level** instance; flatten the level you want
  parallel. A `flattenDepth` knob is possible later if a real design needs it.

## 7. v2: Mealy boundaries by relaxation

With the eval-twice structure, Mealy support does not need explicit
levelization: iterate (Phase A + Phase B) **K** times before Phase C, where
K = the depth of the longest cross-instance combinational chain (computed by
the same analysis that today rejects Mealy). Each round propagates
combinational values one instance further; after K rounds all inputs are
settled, and Phase C latches. Moore-bounded designs are the K = 1 case —
i.e. exactly v1. This makes v2 an analysis change (compute K instead of
erroring) plus a loop bound, not a new schedule.

## 8. Analysis required (Lean side)

1. `combDeps (m : Module) : outputPort → List inputPort` — walk the assign
   graph backwards from each output's driver; stop at registers, memories,
   constants; collect input-port refs; detect undriven wires and comb loops.
2. `resolveConn (top) (expr) : Except String Source` — chase `.ref` chains
   through top assigns to one of: instance output (inst, port), top input
   port, constant. Errors per §6.
3. Moore check: for every resolved (producer, port) source, assert
   `combDeps producer port = []`.
4. Table construction: instance offsets/kinds, copy entries, imm entries,
   top-output entries (assigned to thread 0's copy range).

All string-level; no new IR.

## 9. Test plan

- **Layer 1 (LSpec, `TestCudaSim`)**: table shape on the 2×2 mesh fixture
  (copy entries for `a_out→a_in` right and `p_out→p_in` down, imm for
  `zero32`, top-input copies); rejection messages: Mealy boundary (ALU-style
  instance), top-level register, non-ref connection, comb loop.
- **Layer 2 (`cuda-sim-test`)**: host `g++ -fsyntax-only` on the emitted
  intra `.cu`, with a `cooperative_groups.h` stub added next to the existing
  CUDA-token stub.
- **Layer 3 (opt-in, real GPU)**: co-simulation — the same mesh design
  through (a) CSim CPU (`toCJIT`, gcc) and (b) the intra kernel (nvcc,
  sm_89), same input vectors, compare outputs cycle-exactly; then a generated
  16×16 mesh for a first emitted-kernel performance number against
  `bench/systolic/`'s hand-written ceiling. Not in CI (needs nvcc + GPU);
  runs on the RTX 4070 Ti dev box, results recorded in the PR.

## 10. Measured results (RTX 4070 Ti, sm_89, nvcc 12.6 `-O2 -rdc=true`)

Correctness: **cycle-exact vs the CSim CPU reference** (`cuda-intra-cosim`,
`systolic-cosim`; COSIM PASS) — per-cycle comparison over 64 single-cycle
launches, then one 10⁶-cycle launch whose final outputs must match 10⁶
reference cycles.

Throughput, one launch of 10⁶ cycles; "CPU" is the serial CSim reference in
the same file (one core):

| design | instances | kernel | CPU cyc/s | GPU cyc/s | GPU/CPU |
|---|---:|---|---:|---:|---:|
| IR mesh 16×16 (32-bit MAC) | 256 | block | 4.8e6 | 2.3e6 | 0.48 |
| IR mesh 32×32 | 1024 | block | 8.3e5 | 1.08e6 | 1.30 |
| IR mesh 64×64 | 4096 | grid | 1.8e5 | 3.4e5 | 1.90 |
| `IP/Systolic` matVec16 (int8 MAC, DSL) | 256 | block | 9.5e5 | 1.12e6 | 1.18 |
| `IP/Systolic` matVec32 | 1024 | block | 2.4e5 | 3.6e5 | 1.48 |

The first version of the kernel (three barriers, state in global memory,
table reads inside the cycle loop) ran the 16×16 IR mesh at 2.9e5 cyc/s; the
current one is 7.7× that. The hand-written PoC (`bench/systolic/`, a PE
reduced to two loads, a multiply-add and two stores) does 1.1e7 cyc/s at
16×16 and 5.3e6 at 32×32: the generated code is ~5× below it because a CSim
PE reads and writes every field of its struct (clk/rst masks, wire fields,
`_next` copies) twice per cycle.

Reading the table: the GPU pays a fixed per-cycle cost (two barriers) and
wins by running instances concurrently, so the ratio grows with the instance
count and with the work per instance. Below a few hundred small instances
the serial CPU is faster.

Not done: `eval_outputs`/`eval_state` split, Mealy boundaries (§7), slices of
instance outputs and non-byte-aligned output concatenations at the top level,
wide (> 64-bit) arithmetic in device code (CSim's statement-expression
temporaries are not valid C++; wide concatenations and constants are
respelled, see `CudaSim.cxxWideLiterals`).

## 11. Implementation order

1. `combDeps` + `resolveConn` + Moore check, with LSpec rejection tests.
2. Table + kernel + `jit_intra_run` emission; Layer-1 shape tests.
3. `cooperative_groups.h` stub; Layer-2 wiring.
4. GPU co-sim (Layer 3) on 2×2, then 16×16; record numbers; PR.
