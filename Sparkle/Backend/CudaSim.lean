/-
  CUDA Simulation Backend — addition to Sparkle/Backend/CppSim.lean
  Place this section at the end of the file, before `end Sparkle.Backend.CppSim`.

  Design goals
  ─────────────
  • One CUDA kernel per clock cycle (evalTick_kernel).  Each thread handles
    one independent signal slice; the host launches <<<1,1>>> for purely
    combinational/sequential logic (single-module mode) or <<<nBlocks,nThreads>>>
    for parallel batch simulation (N independent reset vectors / fuzzing).
  • The generated .cu file is self-contained: #include the generated C++ header
    and wrap the evalTick body in __device__ / __global__ code.
  • JIT path: host allocates device memory, copies inputs, launches kernel,
    copies outputs back.  The FFI C ABI (extern "C") is identical to the
    existing dlopen JIT ABI so the Lean sim! / #sim macro needs no changes.

  Limitations (v1)
  ─────────────────
  • No memory (BRAM) in device code — memories stay on the host.
  • Packed integers wider than 64 bits use CSim's uint32_t word-array layout;
    the JIT ABI exposes consecutive little-endian 32-bit slots for input and
    output ports.
  • The generated code requires CUDA ≥ 11.0 and a C++17-capable nvcc.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Specialize
import Sparkle.Backend.CSim
namespace Sparkle.Backend.CudaSim

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CSim   -- reuse sanitizeName, buildTypeMap, lookupWidth,
                            -- emitTypeName, emitFieldDecl, toCDesign, emitModule

-- ─────────────────────────────────────────────────────────────────
-- Section 1: CUDA-specific type and qualifier helpers
-- ─────────────────────────────────────────────────────────────────

/-- Emit a CUDA/device-compatible scalar type.  Delegates to CSim's
    `emitTypeName`, so scalars ≤ 64 bit are the native C integer types and
    wide (> 64 bit) values are `uint32_t[⌈w/32⌉]` arrays — identical to the
    CSim struct layout, which is what the device code operates on.

    (#33 originally mapped wide types onto CUDA `uint3`/`uint4`, but those
    cap at 128 bit and don't match the CSim struct's word-array layout; the
    RV32 core's 578-bit bundle is exactly the case that broke.  Reusing
    CSim's layout removes that limit.) -/
def emitCudaType (ty : HWType) : String := emitTypeName ty

/-- Function qualifiers.  The batch path only needs the CSim module functions
    callable from the device; CSim emits them with a `funcQual` slot we fill
    with `hostDev`.  (`__host__ __device__`, not just `__device__`, so the
    same `.cu` can also drive a CPU reference run.) -/
private def hostDev   : String := "__host__ __device__ "
private def globalQ   : String := "__global__"

-- ─────────────────────────────────────────────────────────────────
-- Section 2: Device-side state struct
-- ─────────────────────────────────────────────────────────────────

/-- The device state struct name.  Under CSim the device state IS the plain-C
    `struct <cls>` that `emitModule` emits (inputs + outputs + observable
    wires + registers), so there is no separate `_state_t` type any more —
    the batch kernel and host API point straight at CSim's struct.

    (#33 emitted its own `<cls>_state_t` and a copy-in/`.evalTick()`/copy-out
    wrapper because the old CppSim backend was a C++ *class* with a method.
    CSim replaced that class with a `struct` + free `sparkle_<cls>_eval_tick`
    function, which is already device-shaped — so the wrapper and the extra
    struct are gone.) -/
def deviceStructName (m : Module) : String := s!"struct {sanitizeName m.name}"

/-- The device eval-tick symbol: CSim's own `sparkle_<cls>_eval_tick`, made
    callable from the device by emitting it with `funcQual = hostDev`. -/
def deviceEvalTick (m : Module) : String := s!"sparkle_{sanitizeName m.name}_eval_tick"

-- ─────────────────────────────────────────────────────────────────
-- Section 3: Device code — reuse CSim's struct + eval_tick via funcQual
-- ─────────────────────────────────────────────────────────────────

/-- Emit the device-side design code: exactly CSim's `toCDesign`, but with
    every module function qualified `__host__ __device__`.  With CSim's
    default `funcQual = ""` this would be the CPU backend byte-for-byte, so
    the device code cannot diverge from CSim's semantics — it *is* CSim
    compiled for the device.

    This supersedes #33's `emitCudaStateStruct` + `emitCudaDeviceEvalTick`
    (class-wrapper) path, and because it reuses CSim's word-array layout it
    also handles wide (> 64-bit) state, which the old `uint3`/`uint4` mapping
    could not (the RV32 578-bit bundle). -/
def emitCudaDeviceCode (m : Module) : String :=
  toCDesign { topModule := m.name, modules := [m] } none hostDev

/-- Emit the device code for a whole `Design` — every module, in dependency
    order, host+device qualified.  This is what a *hierarchical* design needs
    (e.g. a systolic array whose top instantiates N×N `PE` sub-modules): the
    PE's `struct` + `sparkle_PE_eval` must be emitted too, and the top's
    `eval_tick` already contains the generated wire-copy between instances
    (CSim lowers each `.inst` to `inst.a_in = <neighbour wire>; …; eval(&inst);
    <wire> = inst.a_out;`).  `emitCudaDeviceCode m` is the single-module case
    of this. -/
def emitCudaDeviceCodeD (d : Design) : String :=
  toCDesign d none hostDev

-- ─────────────────────────────────────────────────────────────────
-- Section 4: __global__ kernel (batch simulation)
-- ─────────────────────────────────────────────────────────────────

/-- Emit a CUDA __global__ kernel that runs N independent simulation instances.
    Each CUDA thread handles one instance (thread index → state array index).

    Launch pattern:
      dim3 blocks((N + 255) / 256, 1, 1);
      dim3 threads(256, 1, 1);
      className_batch_kernel<<<blocks, threads>>>(d_states, N, numCycles);
-/
def emitCudaBatchKernel (m : Module) : String :=
  let className  := sanitizeName m.name
  let structName := deviceStructName m
  [
    s!"{globalQ} void {className}_batch_kernel(",
    s!"    {structName}* states,",
     "    unsigned int N,",
     "    unsigned int numCycles) {",
     "  const unsigned int tid = blockIdx.x * blockDim.x + threadIdx.x;",
     "  if (tid >= N) return;",
    s!"  {structName}* s = states + tid;",
     "  for (unsigned int cyc = 0; cyc < numCycles; ++cyc) {",
    s!"    {deviceEvalTick m}(s);",
     "  }",
     "}",
     ""
  ] |> String.intercalate "\n"

-- ─────────────────────────────────────────────────────────────────
-- Section 5: Host-side JIT C ABI (extern "C") — dlopen compatible
-- ─────────────────────────────────────────────────────────────────

/-- Emit the host-side extern "C" functions that mirror the existing CppSim
    JIT ABI.  These are compiled into the .so loaded by dlopen.

    New symbols added by the CUDA backend:
      jit_cuda_alloc   — allocate device state array (N instances)
      jit_cuda_free    — free device state array
      jit_cuda_set_input  — write one input into host-pinned staging buffer
      jit_cuda_get_output — read one output from host-pinned staging buffer
      jit_cuda_run     — copy H→D, launch kernel for numCycles, copy D→H
      jit_cuda_reset   — reset all instances on device
-/
def emitCudaJITHostAPI (m : Module) : String :=
  let className  := sanitizeName m.name
  let structName := deviceStructName m

  -- Input port list (excluding clk)
  let userInputs := m.inputs.filter fun p => p.name != "clk"

  -- set_input switch.  Wide inputs use the same little-endian sequence of
  -- 32-bit ABI slots as CSim's JIT wrapper: slot 0 writes bits [31:0], slot 1
  -- writes [63:32], and so on.  Keeping this expansion symmetric with the
  -- output side is essential because a wide field is a C array and cannot be
  -- assigned from the scalar `val` parameter.
  let setInputCases := userInputs.foldl (fun (acc : List String × Nat) p =>
    let sn := sanitizeName p.name
    let w := p.ty.bitWidth
    if w > 64 then
      let nWords := (w + 31) / 32
      let wordCases := List.range nWords |>.map fun j =>
        s!"    case {acc.2 + j}: h_state->{sn}[{j}] = (uint32_t)val; break;"
      (acc.1 ++ wordCases, acc.2 + nWords)
    else
      let ct := emitTypeName p.ty
      (acc.1 ++ [s!"    case {acc.2}: h_state->{sn} = ({ct})val; break;"],
        acc.2 + 1)
  ) ([], 0)

  -- get_output switch (using same multi-slot expansion as existing JIT)
  let getOutputCases := m.outputs.foldl (fun (acc : List String × Nat) p =>
    let sn := sanitizeName p.name
    let w  := p.ty.bitWidth
    if w > 64 then
      let nWords := (w + 31) / 32
      let wcs := List.range nWords |>.map fun j =>
        s!"    case {acc.2 + j}: return (uint64_t)h_state->{sn}[{j}];"
      (acc.1 ++ wcs, acc.2 + nWords)
    else
      (acc.1 ++ [s!"    case {acc.2}: return (uint64_t)h_state->{sn};"], acc.2 + 1)
  ) ([], 0)

  let lines : List String := [
    "// ── CUDA JIT host API ────────────────────────────────────────────",
    "#include <cuda_runtime.h>",
    "#include <cassert>",
    "",
    s!"// Forward declaration of the batch kernel (defined earlier in this TU;",
    s!"// the device eval_tick it calls is CSim's {deviceEvalTick m}).",
    s!"extern {globalQ} void {className}_batch_kernel({structName}* states, unsigned int N, unsigned int numCycles);",
    "",
    "extern \"C\" {",
    "",
    s!"// Allocate N device state instances + one pinned host staging buffer.",
    s!"// Returns opaque handle = pointer to CudaHandle struct.",
    "struct CudaHandle {",
    s!"  {structName}*  d_states;   // device array",
    s!"  {structName}*  h_staging;  // pinned host buffer (N instances)",
    "  unsigned int   N;",
    "};",
    "",
    "void* jit_cuda_alloc(unsigned int N) {",
    "  CudaHandle* h = new CudaHandle;",
    "  h->N = N;",
    s!"  cudaMalloc((void**)&h->d_states, N * sizeof({structName}));",
    s!"  cudaMallocHost((void**)&h->h_staging, N * sizeof({structName}));",
    s!"  memset(h->h_staging, 0, N * sizeof({structName}));",
    "  return h;",
    "}",
    "",
    "void jit_cuda_free(void* handle) {",
    "  CudaHandle* h = (CudaHandle*)handle;",
    "  cudaFree(h->d_states);",
    "  cudaFreeHost(h->h_staging);",
    "  delete h;",
    "}",
    "",
    "// Set input port by index (instance 0..N-1, port index as in JIT ABI).",
    "void jit_cuda_set_input(void* handle, unsigned int inst, int port, uint64_t val) {",
    "  CudaHandle* h = (CudaHandle*)handle;",
    "  if (inst >= h->N) return;",
    s!"  {structName}* h_state = h->h_staging + inst;",
    "  switch (port) {",
  ] ++
  setInputCases.1 ++
  [
    "  }",
    "}",
    "",
    "// Get output port value by index.",
    "uint64_t jit_cuda_get_output(void* handle, unsigned int inst, int port) {",
    "  CudaHandle* h = (CudaHandle*)handle;",
    "  if (inst >= h->N) return 0ULL;",
    s!"  {structName}* h_state = h->h_staging + inst;",
    "  switch (port) {",
  ] ++
  getOutputCases.1 ++
  [
    "  }",
    "  return 0ULL;",
    "}",
    "",
    "// Run numCycles on device.  Copies staging buffer H→D, launches kernel, D→H.",
    "void jit_cuda_run(void* handle, unsigned int numCycles) {",
    "  CudaHandle* h = (CudaHandle*)handle;",
    s!"  cudaMemcpy(h->d_states, h->h_staging, h->N * sizeof({structName}), cudaMemcpyHostToDevice);",
    "  const unsigned int blockSize = 256;",
    "  const unsigned int gridSize  = (h->N + blockSize - 1) / blockSize;",
    s!"  {className}_batch_kernel<<<gridSize, blockSize>>>(h->d_states, h->N, numCycles);",
    "  cudaDeviceSynchronize();",
    s!"  cudaMemcpy(h->h_staging, h->d_states, h->N * sizeof({structName}), cudaMemcpyDeviceToHost);",
    "}",
    "",
    "// Reset all instances (zero state on host staging buffer, copy to device).",
    "void jit_cuda_reset(void* handle) {",
    "  CudaHandle* h = (CudaHandle*)handle;",
    s!"  memset(h->h_staging, 0, h->N * sizeof({structName}));",
    s!"  cudaMemcpy(h->d_states, h->h_staging, h->N * sizeof({structName}), cudaMemcpyHostToDevice);",
    "}",
    "",
    "} // extern \"C\"",
    "",
  ]
  String.intercalate "\n" lines

-- ─────────────────────────────────────────────────────────────────
-- Section 6: Top-level transpile entry points
-- ─────────────────────────────────────────────────────────────────

/-- Assemble a self-contained `.cu`: CUDA includes, the given `deviceCode`
    body (single module or whole design), the `__global__` batch kernel, and
    the host `extern "C"` JIT API.  Fully self-contained — no external header
    include — because the device code is CSim's own struct + module functions
    emitted inline (host+device qualified).  The kernel and host API always
    target the top module `top`, whose fused struct embeds every instance. -/
private def assembleCu (top : Module) (deviceCode : String) : String :=
  let className := sanitizeName top.name
  let preamble := String.intercalate "\n" [
    "// AUTO-GENERATED by Sparkle HDL — CUDA Simulation Backend",
    s!"// Module: {top.name}",
    "//",
    "// Compile with:",
    s!"//   nvcc -O3 -std=c++17 -shared -Xcompiler -fPIC -o lib{className}.so {className}.cu",
    "",
    "#include <cstdint>",
    "#include <cstring>",
    "#include <cuda_runtime.h>",
    "",
    "// ── CSim device code (struct + __host__ __device__ module functions) ─",
  ]
  preamble ++ "\n" ++
  deviceCode ++ "\n" ++
  "// ── Batch kernel ─────────────────────────────────────────────────\n" ++
  emitCudaBatchKernel top ++ "\n" ++
  emitCudaJITHostAPI top

/-- CudaSim shares CSim's concrete-width representation and therefore cannot
    consume native symbolic-width modules. -/
private def unsupportedSymbolicWidthError : String :=
  "#error \"Sparkle CudaSim requires concrete widths; specialize retained parameters before CUDA lowering\"\n"

/-- Generate a self-contained `.cu` for a single `Module` (no sub-instances).
    `_cppHeaderName` is accepted for source compatibility with #33/#37 call
    sites but is unused — nothing is `#include`d. -/
def toCudaSim (m : Module) (_cppHeaderName : String := "") : String :=
  if moduleHasSymbolicWidth m then unsupportedSymbolicWidthError
  else assembleCu m (emitCudaDeviceCode m)

/-- Generate a self-contained `.cu` for a full `Design`.  Emits EVERY module
    (not just the top): for a hierarchical design the top's `eval_tick` calls
    the sub-modules' `eval`, so their `struct`s + functions must be present in
    the same translation unit.  The batch kernel and host API target the top,
    whose fused device struct embeds every instance — so poking the top's
    input ports and stepping the kernel drives the whole hierarchy.

    This is the path a systolic array / PE-mesh design takes: the PE-to-PE
    wire-copy is generated by CSim inside the top's `eval_tick`, not written
    by hand. -/
def toCudaSimDesign (d : Design) (_cppHeaderName : String := "") : String :=
  if d.modules.any moduleHasSymbolicWidth then
    unsupportedSymbolicWidthError
  else match d.modules.find? fun m => m.name == d.topModule with
  | none   => s!"// ERROR: top module '{d.topModule}' not found in design\n"
  | some top => assembleCu top (emitCudaDeviceCodeD d)

/-- Specialize retained dimensions for one explicit configuration, then emit
    one fixed-layout CUDA batch model for a single module. -/
def toCudaSimWithParameters (m : Module)
    (bindings : Sparkle.IR.Specialize.Bindings)
    (_cppHeaderName : String := "") : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeModule m bindings
  return toCudaSim concrete _cppHeaderName

/-- Specialize every module in a retained-parameter design, then emit one
    fixed-layout CUDA batch model for that explicit configuration. -/
def toCudaSimDesignWithParameters (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings)
    (_cppHeaderName : String := "") : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeDesign d bindings
  return toCudaSimDesign concrete _cppHeaderName

end Sparkle.Backend.CudaSim
