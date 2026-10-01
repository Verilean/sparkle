# Chapter 13 — GPU Simulation: Monte-Carlo Sweeps and Systolic Arrays

Sparkle can compile the same IR that drives the C JIT (Ch8b) into CUDA.
There are **two backends for two different kinds of parallelism**, and
picking the right one matters more than any flag:

| | batch (`#writeCudaDesign`) | intra (`#writeCudaIntraDesign`) |
|---|---|---|
| unit of parallelism | one **design instance** per GPU thread | one **sub-module instance** (PE, core) per thread |
| makes faster | N independent runs: Monte-Carlo, fuzzing, test-vector sweeps | ONE big design: a systolic array, a core bank |
| could you buy it with more machines? | yes — this is throughput | **no** — this is single-run latency/scale |
| measured (RTX 4070 Ti) | 10–11× vs single-thread CPU JIT | grows with the design: 0.5× the CPU at 256 PEs, 1.3× at 1024, 1.9× at 4096 (generated kernel, small MAC cell) |
| requirements | `nvcc` | `nvcc -rdc=true`, Moore-bounded module boundaries |

Everything here is opt-in: no GPU or `nvcc` is needed to *emit* the `.cu`
(that happens at `lake build` time), only to compile and run it.

## 13.1 Case 1 — Monte-Carlo with the batch backend

A Monte-Carlo experiment wants many copies of one circuit, each with
different inputs. Here is a 32-bit linear congruential generator, seedable
through an input port — one flat `circuit do`, nothing GPU-specific:

```lean
def lcg {dom : DomainConfig}
    (seedLoad : Signal dom Bool) (seed : Signal dom (BitVec 32)) :
    Signal dom (BitVec 32) :=
  circuit do
    let x ← Signal.reg (1#32)
    let xS := (x : Signal dom (BitVec 32))
    x <~ Signal.mux seedLoad seed (xS * (1664525#32) + (1013904223#32))
    return xS

#writeCudaDesign lcg "gen/lcg.cu"
```

`#writeCudaDesign` runs at build time and writes a self-contained `.cu`:
the CSim struct and `eval_tick` (qualified `__host__ __device__`, so the
device code *is* the CPU reference), a `__global__` batch kernel, and an
`extern "C"` host API. Compile it into a shared library:

```bash
nvcc -O2 -std=c++17 -shared -Xcompiler -fPIC -o liblcg.so gen/lcg.cu
```

Drive N instances from any host program (dlopen or link directly):

```c
void* h = jit_cuda_alloc(1000000);          // one thread per instance
jit_cuda_reset(h);
for (unsigned i = 0; i < 1000000; i++) {
  jit_cuda_set_input(h, i, /*seedLoad*/0, 1);   // port indices: all inputs
  jit_cuda_set_input(h, i, /*seed*/1, 12345+i); // except clk, in decl order
}
jit_cuda_run(h, 1);                          // latch the seeds
for (unsigned i = 0; i < 1000000; i++)
  jit_cuda_set_input(h, i, 0, 0);            // seedLoad low
jit_cuda_run(h, 10000);                      // 10k cycles × 1M instances
// harvest: jit_cuda_get_output(h, i, 0) — do your statistics host-side
jit_cuda_free(h);
```

The port-index convention is CSim's: **all inputs except `clk`, in
declaration order** (`rst` is index 0 here — under the C model reset is the
initial state, and the `rst` port is an ordinary input). Outputs likewise;
wide (> 64-bit) outputs occupy one index per 32-bit word.

## 13.2 Case 2 — a systolic array with the intra backend

The batch backend cannot make *one* large accelerator faster — for that,
each PE must become its own GPU thread, with barriers separating the phases
of every simulated clock cycle. That is the intra backend
(`docs/CudaIntraSim-design.md` has the schedule and its cycle-exactness
argument; it was co-simulated against the CPU reference on real hardware).

Its one structural demand: **Moore-bounded boundaries** — every cross-PE
connection must tap a register-backed output, never a combinational path
through a PE. Systolic arrays satisfy this by construction, and a violation
is rejected *at build time* with the offending connection named.

### The mesh in the DSL: `systolic_grid%`

A PE is a `@[hardware_module]` returning a record of its outputs; the array
is one call per PE. `systolic_grid%` writes those calls for an R × C array —
each cell wired to its left and upper neighbour — and returns the bottom
row concatenated (`IP/Systolic/MatVec.lean` is this example in full):

```lean
@[hardware_module] def pe {dom} (aIn : Signal dom (BitVec 8))
    (pIn : Signal dom (BitVec 32)) (w : Signal dom (BitVec 8)) : PeOut dom := …

def matVec16 {dom} (a : Signal dom (BitVec 128)) : Signal dom (BitVec 512) :=
  systolic_grid% 16 16
    (cell i j left up => pe left up (Signal.pure (weight i j)))
    (right := aOut) (down := pOut)
    (leftEdge i => activation a i)      -- bits [8i+7 : 8i] of the input
    (topEdge j => Signal.pure 0#32)

#writeCudaIntraDesign matVec16 "gen/matvec16.cu"
```

`i` and `j` become numerals, so `weight i j` is a constant per PE. The
packed input is sliced per row and the results are concatenated at the top
level; the intra backend accepts exactly those two forms of top-level logic
(slices of top inputs, byte-aligned concatenations of instance outputs).
Calls with identical arguments are one instance, so every PE needs
something that distinguishes it — here its neighbours and its weight.

`lake exe systolic-test` checks that the array settles to y = Wᵀ·a;
`SPARKLE_CUDA=1 lake exe systolic-cosim` runs the emitted kernels against
the CPU reference on a GPU.

### The mesh as IR

The top can also be built as explicit IR instances — ~20 lines for an N×N
generator (see `Tests/Drivers/CudaIntraCosimMain.lean` for the parametric
version; `Tests/TestCudaSim.lean` has the literal 2×2):

```lean
-- PE: a_out = registered a_in;  p_out = registered (p_in + a_in·w)
-- Mesh: activations stream right, partial sums flow down.
#eval do
  let cu := Sparkle.Backend.CudaIntra.toCudaIntraDesign!
              Sparkle.Test.CudaSim.systolicDesign
  IO.FS.writeFile "gen/mesh.cu" cu
```

```bash
nvcc -O2 -std=c++17 -rdc=true -shared -Xcompiler -fPIC -o libmesh.so gen/mesh.cu
```

The emitted `.cu` carries **both** APIs: the batch kernel *and*
`jit_intra_run`. Allocate a single instance and step it with the intra
schedule:

```c
void* h = jit_cuda_alloc(1);                 // ONE design instance
jit_cuda_set_input(h, 0, /*ain_0*/1, 3);     // poke edge activations/weights
/* ... */
jit_intra_run(h, 100000);                    // one thread per PE inside
unsigned r0 = jit_cuda_get_output(h, 0, 0);  // bottom-row results
```

`jit_intra_run` picks the kernel automatically: one thread block
(`__syncthreads`, fastest cycle rate) when the instance count fits 1024,
else a cooperative grid launch (any size — this is what scales to
1000+-PE accelerators; needs a cooperative-launch-capable GPU).

## 13.3 Verifying what you got

Three habits, all cheap:

1. **Count instances**: `grep intra_M gen/mesh.cu` must equal your PE count.
2. **Co-simulate**: `SPARKLE_CUDA=1 lake exe cuda-intra-cosim` (IR meshes)
   and `lake exe systolic-cosim` (the DSL array) run the emitted kernel
   cycle-by-cycle against the CPU reference (the `__host__ __device__`
   functions *are* CSim), fail on any divergence, and print both rates.
3. **No GPU?** `lake exe cuda-sim-test` host-syntax-checks the emitted CUDA
   with stubs — catches emitter regressions in ordinary CI.

## 13.4 Environment notes

- `nvcc`'s version must be **≤ the driver's CUDA version** (`nvidia-smi`,
  top right). A newer toolkit fails at runtime with
  "driver version insufficient".
- On NixOS the real `libcuda.so.1` lives in `/run/opengl-driver/lib` — put
  it on `LD_LIBRARY_PATH` or the same error appears with a healthy GPU.
  `shell.nix` pins a matching `cudaPackages` toolkit.
- The intra `.cu` needs `-rdc=true` (cooperative groups); the batch `.cu`
  does not.

## 13.5 Choosing, in one sentence each

- *"I want a million runs with different inputs"* → batch. Cheap, scales
  with money.
- *"My one design has a thousand PEs and simulation is the bottleneck"* →
  intra. This is the axis money can't buy. Expect a win from roughly a
  thousand instances up (1.3× at 1024, 1.9× at 4096 for a small MAC cell;
  more as the cell gets heavier); below a few hundred small instances the
  CPU is faster.
- *"Both"* → they share one `.so`; batch across instances of a design whose
  single-instance rate the intra scheduler sets is a v2 combination.
