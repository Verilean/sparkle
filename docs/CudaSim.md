# CUDA simulation backend

Batch-parallel cycle simulation on the GPU: run **N independent instances**
of one design in parallel, one instance per thread — a fuzzing sweep, a
Monte-Carlo run, a bank of test vectors. This is the axis that maps naturally
onto GPU SIMT (every thread does the same work on different data), as opposed
to speeding up a single instance.

It is *not* in the default build path; it reuses the CPU C backend
(`Sparkle/Backend/CSim.lean`) and wraps it in device code.

## Provenance

The design, the batch kernel, the pinned-memory host JIT API, and the
benchmark harness all originate in xiangze's PRs
[#33](https://github.com/Verilean/sparkle/pull/33) ("Strategy 1: batch
parallelism") and [#37](https://github.com/Verilean/sparkle/pull/37) (the
nvcc-memory analysis and the CppSim-vs-CUDA benchmark). This backend is those
PRs retargeted onto the current `CSim` backend, which replaced the old CppSim
*class* model with a plain-C `struct` + free functions.

## How it works

`CSim.emitModule` emits, per module, a plain-C `struct <cls>` (inputs +
outputs + observable wires + registers) plus
`sparkle_<cls>_{reset,eval,tick,eval_tick}(struct <cls>*)` free functions.
That struct **is** the state, and `eval_tick` is already device-shaped.

The CUDA backend re-emits exactly that with one change: every module function
is qualified `__host__ __device__` instead of plain `static`, via a
`funcQual` parameter threaded through `emitModule` / `toCDesign`. With
`funcQual = ""` (the default) the output is byte-for-byte the CPU backend, so
**the device code cannot diverge from CSim's semantics — it is CSim compiled
for the device.**

On top of that struct + device functions, `CudaSim.toCudaSim` adds:

* a `__global__` batch kernel — `tid = blockIdx.x*blockDim.x + threadIdx.x`,
  each thread loops one instance's `sparkle_<cls>_eval_tick` for `numCycles`;
* an `extern "C"` host JIT API: `jit_cuda_alloc(N)`, `jit_cuda_free`,
  `jit_cuda_set_input(h, inst, port, val)` / `jit_cuda_get_output(h, inst,
  port)` (port-index ABI, matching the CPU JIT), `jit_cuda_run(h, numCycles)`
  (H→D copy, launch, D→H copy), and `jit_cuda_reset`. Staging uses
  `cudaMallocHost` (pinned memory) for faster transfers.

### What changed from #33

#33 targeted the old CppSim *class* backend: it emitted its own
`<cls>_state_t` device struct and a `<cls>_cuda_evalTick` wrapper that
copied the struct into a local class instance, called `sim.evalTick()`, and
copied back — a full struct↔class copy every cycle. Under `CSim` that class
is gone, so:

* the separate `_state_t` struct and the copy-in/call/copy-out wrapper are
  **removed** — the batch kernel calls `sparkle_<cls>_eval_tick` directly on
  CSim's struct, no per-cycle copy;
* wide (> 64-bit) state now works. #33 mapped wide values onto CUDA
  `uint3`/`uint4` (capped at 128 bit) and excluded wider registers from the
  device struct — which is exactly why the RV32 core's 578-bit bundle showed
  `--` in #37's table. Reusing CSim's `uint32_t[⌈w/32⌉]` word-array layout
  removes that limit.

## Generating a `.cu`

```lean
import Sparkle.Backend.CudaSim

def myTop : Module := …           -- an IR Module

#eval IO.FS.writeFile "my_top.cu" (Sparkle.Backend.CudaSim.toCudaSim myTop)
```

`toCudaSim` is pure string generation — no `nvcc`, no GPU. The emitted `.cu`
is self-contained (no external header include): CSim's struct + device
functions are inlined into it.

## Compiling and running (opt-in, needs `nvcc` + a GPU)

```
nvcc -O1 -std=c++17 -shared -Xcompiler -fPIC -arch=compute_86 \
     -o libmy_top.so my_top.cu
```

`nvcc` is memory-hungry — it parses host and device translation units
together — so the benchmark path uses `-O1` and PTX-only codegen
(`-arch=compute_XX`, which skips the SASS backend) to keep peak memory down on
shared machines (xiangze's #37 analysis). `CUDA_ARCH` selects the GPU
generation: `compute_86` (RTX 30xx), `compute_80` (A100), `compute_89` (RTX
40xx), `compute_90` (H100).

A host program that `dlopen`s the `.so`:

```c
void* h = jit_cuda_alloc(N);
jit_cuda_reset(h);
for (unsigned i = 0; i < N; i++)
  jit_cuda_set_input(h, i, /*port*/0, vectors[i]);   // poke inputs
jit_cuda_run(h, numCycles);                          // H->D, launch, D->H
for (unsigned i = 0; i < N; i++)
  results[i] = jit_cuda_get_output(h, i, /*port*/0); // peek outputs
jit_cuda_free(h);
```

Reported by #37 on an RTX 3080 Ti (`SPARKLE_CUDA=1 CUDA_ARCH=compute_86`):
Counter (4 B state) 11×, WideAccum (64 B) 10× vs the single-thread CPU JIT.

## Testing and CI

Three layers, in decreasing CI-friendliness:

| layer | needs | where |
|---|---|---|
| emitter type-check + shape assertions | nothing | `Tests.TestCudaSim` — `lake test` / `lake build` |
| host `g++ -fsyntax-only` on the emitted `.cu` | a C++ compiler | `lake exe cuda-sim-test` |
| `nvcc` compile + GPU run | `nvcc`, a GPU | opt-in, `SPARKLE_CUDA=1` — not in CI |

The middle layer is the interesting one: it stubs out the CUDA tokens
(`__global__`, `blockIdx`, `cudaMalloc`, …) and strips the `<<<grid,
block>>>` launch syntax so an ordinary host C++ compiler can parse the
generated `.cu`. That proves the emitted code is **well-formed** without a
GPU or `nvcc` — catching real emitter bugs a pure type-check misses (e.g. the
`(void**)&` cast `cudaMalloc` requires) — and it *skips* (does not fail) when
no compiler is present.

## Hierarchical designs (`toCudaSimDesign`)

`toCudaSim` takes a single `Module`; `toCudaSimDesign` takes a whole `Design`
and emits **every** module (in dependency order), then targets the batch
kernel + host API at the top. This is what a design *hierarchy* needs — e.g. a
systolic array whose top instantiates an N×N mesh of `PE` sub-modules:

* the `PE` `struct` + `sparkle_PE_eval` are emitted alongside the top's;
* the top's fused device struct **embeds** every instance (`struct PE
  pe_0_0; …`);
* the PE-to-PE **wire-copy is generated** by CSim inside the top's
  `eval_tick` — each `.inst` lowers to `self->pe_0_1.a_in = aout_0_0; …;
  sparkle_PE_eval(&self->pe_0_1); …` — not hand-written.

So poking the top's input ports and stepping the batch kernel drives the whole
hierarchy. This is the emitter form of the hand-written kernels in
`bench/systolic/` (which measured up to 49× vs CPU for a large array); it
replaces #33's CppSim-class-model `CudaDesignStateStruct` path.

## Scope and follow-ups

Batch simulation (N independent instances), single module or full hierarchy;
same coverage as CSim's scalar path; wide (> 64-bit) values are `uint32_t`
arrays and work identically on the device.

Deliberately **not** here yet:

* **Within-instance (PE-per-thread) scheduling.** `toCudaSimDesign` runs the
  batch axis: one thread simulates one *whole* array instance. Making a
  *single* large array faster by mapping each PE-instance to its own thread
  with a per-cycle barrier (#33's Strategy 4; prototyped in
  `bench/systolic/systolic_gpu_grid.cu`) is a separate kernel the emitter does
  not yet generate — the next step.
* Wide (> 64-bit) *input* ports in `set_input` (outputs already handle the
  per-word form).
