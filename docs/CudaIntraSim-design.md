# Design: within-instance CUDA scheduling (`toCudaIntraDesign`)

Status: **design, v1 not yet implemented.** Builds on the batch backend
(#115), hierarchical emission (#117), and the measurements in
`bench/systolic/` (#116).

## 1. Goal

`toCudaSimDesign` parallelises *across* design instances: one GPU thread
simulates one whole design (batch / Monte-Carlo). This backend parallelises
*within* one instance: **each top-level `.inst` (a PE, a core) becomes one GPU
thread**, with barriers marking the phases of each simulated clock cycle —
#33's "Strategy 4". This is the axis that makes a *single large* accelerator
(systolic array + RISC-V bank, 1000+ PEs) simulate faster, which adding
machines cannot do.

`bench/systolic/` measured the ceiling with hand-written kernels:

- single block (`__syncthreads`, M ≤ 1024 PEs): ~5×10⁶ cyc/s, 2.6× CPU;
- grid-sync (cooperative groups, any M): cyc/s pinned ~9×10⁵ by the barrier,
  PE-throughput linear in M — 49× CPU at 65536 PEs.

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

## 3. The schedule: three phases, eval twice

The rework's key move. Instead of resolving each Moore output back to the
register expression it aliases (which needs alias-chasing analysis and
restricts outputs to plain `.ref reg` forms), **run eval twice** and let
CSim's own output computation do the work:

```
per simulated cycle:
  Phase A [one thread per instance]:  sparkle_<Mod>_eval(&inst)
      — freshens every Moore output field from current register state.
  barrier
  Phase B [copies partitioned over threads]:  connection table
      — consumer.input_field ← producer.output_field  (plain field copy)
      — consumer.input_field ← top input field / constant
      — thread 0: top output-port fields ← producer output fields
  barrier
  Phase C [one thread per instance]:  sparkle_<Mod>_eval_tick(&inst)
      — re-evals with FRESH inputs (correct next-state), then latches.
  barrier   (loop)
```

**Why eval twice is sound.** CSim's `eval` is idempotent and register-pure:
registers latch only in `tick` (`_next → current`), memory writes happen only
in `tickBody`, and sync-read address latches are last-write-wins (verified
against `CSim.lean`'s `.register`/`.memory` emission). Phase A's eval runs
with stale inputs — its next-state results are garbage, but they live in
`_next`/locals and are **overwritten** by Phase C's eval before any latch.
Only its Moore-output fields are consumed (Phase B), and those depend only on
registers, which Phase A cannot change.

**Cycle-exactness vs CSim (Moore-bounded case).** When instance B evals in
CSim at cycle *c*, its input holds the producer's output computed at cycle *c*
from registers latched at end of *c−1*. In this schedule, Phase B copies the
producer's output field written by Phase A's eval — computed from the same
registers (nothing latches between A and B). Phase C's eval then sees the
identical input value. Top output ports are copied in Phase B from the same
fresh output fields, matching CSim's post-eval observation timing.

**Race-freedom.** Phase A: each thread writes only its own instance's fields.
Phase B: every copy writes a distinct destination field (one connection per
input port); reads touch output fields, which nothing writes in Phase B.
Phase C: per-instance state only. Barriers separate the phases.

**Cost.** One extra eval per cycle. In the barrier-dominated regime this is
noise: the PoC's grid barrier costs ~1.1 µs/cycle while a PE eval is tens of
ns. If a design ever becomes eval-dominated, the v2 fix is to split CSim's
emission into `eval_outputs` / `eval_state` (another `funcQual`-style
parameter), not to change this schedule.

**Rejected alternative** (for the record): 2-phase with Moore-alias
resolution — Phase 1 copies `consumer.a_in = producer.a_reg` directly by
chasing `a_out := a_reg` chains in the producer. One eval per cycle, one
fewer barrier, but needs expression-inlining machinery and restricts
cross-boundary outputs to register *aliases* (a computed Moore output like
`a_reg + 1` fails). The eval-twice schedule lifts both at negligible cost.

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
| instance connections are `.ref` (top wire/port, chased transitively) or `.const` | the connection expr | materialize the expr in a top wire driven by a submodule; v2 = inline eval |
| top module body: `.assign` (const/ref chains) + `.inst` only — no `.register`/`.memory`/comb logic at top | the offending Stmt | push it into a submodule |
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

## 10. Implementation order

1. `combDeps` + `resolveConn` + Moore check, with LSpec rejection tests.
2. Table + kernel + `jit_intra_run` emission; Layer-1 shape tests.
3. `cooperative_groups.h` stub; Layer-2 wiring.
4. GPU co-sim (Layer 3) on 2×2, then 16×16; record numbers; PR.
