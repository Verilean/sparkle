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
  • Wide integers (> 64 bit) are passed as uint64_t (low 64 bits), same as the
    existing JIT ABI.
  • The generated code requires CUDA ≥ 11.0 and a C++17-capable nvcc.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.CppSim
namespace Sparkle.Backend.CudaSim

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CppSim   -- reuse emitCppType, sanitizeName, etc.

-- ─────────────────────────────────────────────────────────────────
-- Section 1: CUDA-specific type and qualifier helpers
-- ─────────────────────────────────────────────────────────────────

/-- Emit a CUDA/device-compatible scalar type (same as C++ for scalars ≤ 64 bit).
    Wide types (> 64 bit) are represented as uint2 (two 32-bit words in a struct)
    or uint4 (four words) for ≤ 128 bit; wider unsupported in device code. -/
def emitCudaType : HWType → String
  | .bit          => "uint8_t"
  | .bitVector w  =>
    if      w ≤ 8  then "uint8_t"
    else if w ≤ 16 then "uint16_t"
    else if w ≤ 32 then "uint32_t"
    else if w ≤ 64 then "uint64_t"
    else if w ≤ 96 then "uint3"   -- CUDA built-in: {x,y,z}
    else                 "uint4"  -- CUDA built-in: {x,y,z,w}
  | .array sz elemTy =>
    -- Fixed-size arrays allowed in device code as local variables
    emitCudaType elemTy ++ "[" ++ toString sz ++ "]"

/-- Prefix for __device__ / __host__ __device__ functions -/
private def devQual   : String := "__device__ __forceinline__"
private def hostDev   : String := "__host__ __device__ __forceinline__"
private def globalQ   : String := "__global__"

-- ─────────────────────────────────────────────────────────────────
-- Section 2: Device-side state struct
-- ─────────────────────────────────────────────────────────────────

/-- Emit a flat struct holding all registers and I/O ports, suitable for
    placement in shared or global memory on the GPU.
    Memories are excluded (they live on the host). -/
def emitCudaStateStruct (m : Module) : String :=
  let typeMap := buildTypeMap m
  let className := sanitizeName m.name
  let structName := className ++ "_state_t"

  -- Collect fields: inputs + outputs + registers (≤ 64 bit)
  let inputFields  := m.inputs.map  fun p => s!"  {emitCudaType p.ty} {sanitizeName p.name};"
  let outputFields := m.outputs.map fun p => s!"  {emitCudaType p.ty} {sanitizeName p.name};"
  let regFields    := m.body.filterMap fun stmt => match stmt with
    | .register out .. =>
      let w := lookupWidth typeMap out
      if w ≤ 64 then some s!"  {emitCudaType (.bitVector w)} {sanitizeName out};"
      else            none  -- wide regs excluded from device state
    | _ => none

  -- Deduplicate (output regs appear in both outputs and registers)
  let regNames := m.body.filterMap fun s => match s with
    | .register out .. => some (sanitizeName out) | _ => none
  let filteredOutputFields := outputFields.filter fun line =>
    let name := (line.trim.splitOn " ").getLast? |>.map (·.dropRight 1) |>.getD ""
    !regNames.contains name

  let fields := inputFields ++ filteredOutputFields ++ regFields
  "struct " ++ structName ++ " {\n" ++
  String.intercalate "\n" fields ++ "\n" ++
  "};\n"

-- ─────────────────────────────────────────────────────────────────
-- Section 3: Device __device__ evalTick
-- ─────────────────────────────────────────────────────────────────

/-- Re-emit the evalTick logic as a __device__ function operating on a
    pointer to the state struct.  Memories are stubbed out (read returns 0,
    writes are no-ops) — they must be handled separately on the host.

    The body is taken from `emitModule`'s evalTick output; we strip the
    `void evalTick()` signature and class member accesses, replacing them
    with `s->field` dereferences. -/
def emitCudaDeviceEvalTick (m : Module) : String :=
  if m.isPrimitive then
    s!"// Primitive module {m.name}: no CUDA device code\n"
  else
    let className  := sanitizeName m.name
    let structName := className ++ "_state_t"

    -- Generate a minimal evalTick body in the same style as emitModule but
    -- annotated for device code.  We call the existing CppSim emitter for
    -- the body lines and prefix every member access with "s->".
    -- For simplicity in v1, emit a wrapper that calls the host-side class:
    -- the device function copies the struct into a local class instance,
    -- runs evalTick(), then writes back registers and outputs.

    let sig := s!"{devQual} void {className}_cuda_evalTick({structName}* s)"
    let open_ := " {"
    -- Local class instance, copy-initialized from device struct fields
    let localInst := s!"  {className} sim;"

    -- Copy inputs into sim
    let inputCopies := m.inputs.map fun p =>
      let sn := sanitizeName p.name
      s!"  sim.{sn} = s->{sn};"

    -- Copy register state into sim
    let typeMap := buildTypeMap m
    let regCopies := m.body.filterMap fun stmt => match stmt with
      | .register out .. =>
        let w := lookupWidth typeMap out
        let sn := sanitizeName out
        if w ≤ 64 then some s!"  sim.{sn} = s->{sn};" else none
      | _ => none

    -- Run the cycle
    let runCycle := "  sim.evalTick();"

    -- Write outputs back
    let outputWrites := m.outputs.map fun p =>
      let sn := sanitizeName p.name
      s!"  s->{sn} = sim.{sn};"

    -- Write register state back
    let regWrites := m.body.filterMap fun stmt => match stmt with
      | .register out .. =>
        let w := lookupWidth typeMap out
        let sn := sanitizeName out
        if w ≤ 64 then some s!"  s->{sn} = sim.{sn};" else none
      | _ => none

    let close_ := "}"

    String.intercalate "\n" (
      [sig, open_, localInst, ""] ++
      ["  // Copy inputs"] ++ inputCopies ++
      ["", "  // Copy register state"] ++ regCopies ++
      ["", runCycle, ""] ++
      ["  // Write outputs back"] ++ outputWrites ++
      ["", "  // Write register state back"] ++ regWrites ++
      [close_, ""]
    )

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
  let structName := className ++ "_state_t"
  [
    s!"{globalQ} void {className}_batch_kernel(",
    s!"    {structName}* states,",
     "    unsigned int N,",
     "    unsigned int numCycles) {",
     "  const unsigned int tid = blockIdx.x * blockDim.x + threadIdx.x;",
     "  if (tid >= N) return;",
    s!"  {structName}* s = states + tid;",
     "  for (unsigned int cyc = 0; cyc < numCycles; ++cyc) {",
    s!"    {className}_cuda_evalTick(s);",
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
  let structName := className ++ "_state_t"
  let typeMap    := buildTypeMap m

  -- Input port list (excluding clk)
  let userInputs := m.inputs.filter fun p => p.name != "clk"

  -- set_input switch
  let setInputCases := (userInputs.zip (List.range userInputs.length)).map
    fun (p, i) =>
      let sn := sanitizeName p.name
      let ct := emitCppType p.ty
      s!"    case {i}: h_state->{sn} = ({ct})val; break;"

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
    s!"// Forward declaration of device function (in same .cu TU)",
    s!"extern {devQual} void {className}_cuda_evalTick({structName}* s);",
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
    s!"  cudaMalloc(&h->d_states, N * sizeof({structName}));",
    s!"  cudaMallocHost(&h->h_staging, N * sizeof({structName}));",
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
  setInputCases ++
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

/-- Generate a self-contained .cu file for a single Module.

    The output should be compiled as:
      nvcc -O3 -std=c++17 -shared -fPIC \
           -I<sparkle_include_dir> \
           -o lib<module>.so <module>.cu

    The generated file:
      1. Includes the C++ simulation header (from CppSim).
      2. Defines the device state struct.
      3. Defines the __device__ evalTick wrapper.
      4. Defines the __global__ batch kernel.
      5. Provides the host-side extern "C" JIT API.
-/
def toCudaSim (m : Module) (cppHeaderName : String := "") : String :=
  let className  := sanitizeName m.name
  let headerName := if cppHeaderName.isEmpty then className ++ "_sim.h" else cppHeaderName
  let preamble := String.intercalate "\n" [
    "// AUTO-GENERATED by Sparkle HDL — CUDA Simulation Backend",
    s!"// Module: {m.name}",
    "//",
    "// Compile with:",
    s!"//   nvcc -O3 -std=c++17 -shared -fPIC -o lib{className}.so {className}.cu",
    "",
    "#include <cstdint>",
    "#include <array>",
    "#include <cstring>",
    "#include <cuda_runtime.h>",
    s!"#include \"{headerName}\"",
    "",
    "// ── Device state struct ──────────────────────────────────────────",
  ]
  preamble ++ "\n" ++
  emitCudaStateStruct m ++ "\n" ++
  "// ── Device evalTick ──────────────────────────────────────────────\n" ++
  emitCudaDeviceEvalTick m ++ "\n" ++
  "// ── Batch kernel ─────────────────────────────────────────────────\n" ++
  emitCudaBatchKernel m ++ "\n" ++
  emitCudaJITHostAPI m

/-- Generate .cu for a full Design (top module only; sub-modules included via header). -/
def toCudaSimDesign (d : Design) (cppHeaderName : String := "") : String :=
  match d.modules.find? fun m => m.name == d.topModule with
  | none   => s!"// ERROR: top module '{d.topModule}' not found in design\n"
  | some m => toCudaSim m cppHeaderName

end Sparkle.Backend.CudaSim
