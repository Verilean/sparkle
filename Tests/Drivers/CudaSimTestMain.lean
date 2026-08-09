import Sparkle.Backend.CudaSim
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Builder
open Sparkle.Backend.CudaSim Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Builder CircuitM

/-  Layer 2 of the CUDA backend tests: prove the emitted `.cu` is *well-formed*
    without `nvcc` or a GPU.  We stub the CUDA tokens, strip the `<<<grid,
    block>>>` launch syntax, and run a host C++ compiler's `-fsyntax-only`.
    This catches emitter bugs a pure type-check (Layer 1, TestCudaSim) can't —
    e.g. the `void**` cast the host API needs for `cudaMalloc`.  It *skips*
    (does not fail) when no compiler is present. -/

/-- CUDA stub header: define the CUDA tokens so a host C++ compiler can parse
    the emitted `.cu` without `nvcc`.  Well-formedness only; not a GPU run. -/
def cudaStub : String := "\
#pragma once\n\
#include <cstdlib>\n\
#include <cstring>\n\
#include <cstdint>\n\
#define __host__\n\
#define __device__\n\
#define __global__\n\
#define __forceinline__\n\
typedef unsigned int cudaError_t;\n\
struct uint3 { unsigned x,y,z; };\n\
struct dim3 { unsigned x,y,z; dim3(unsigned a=1,unsigned b=1,unsigned c=1):x(a),y(b),z(c){} };\n\
static uint3 blockIdx = {0,0,0};\n\
static uint3 threadIdx = {0,0,0};\n\
static dim3 blockDim = dim3(1,1,1);\n\
static inline cudaError_t cudaMalloc(void** p, size_t n){ *p=malloc(n); return 0; }\n\
static inline cudaError_t cudaMallocHost(void** p, size_t n){ *p=malloc(n); return 0; }\n\
static inline cudaError_t cudaFree(void* p){ free(p); return 0; }\n\
static inline cudaError_t cudaFreeHost(void* p){ free(p); return 0; }\n\
enum cudaMemcpyKind { cudaMemcpyHostToDevice, cudaMemcpyDeviceToHost };\n\
static inline cudaError_t cudaMemcpy(void* d,const void* s,size_t n,cudaMemcpyKind){ memcpy(d,s,n); return 0; }\n\
static inline cudaError_t cudaDeviceSynchronize(){ return 0; }\n"

/-- Strip the `<<<grid, block>>>` launch config (nvcc-only syntax) so host
    g++ can parse the kernel call as an ordinary function call: turns
    `kernel<<<g,b>>>(args)` into `kernel(args)` by dropping everything from
    `<<<` up to and including the matching `>>>`. -/
partial def stripLaunch (s : String) : String :=
  match s.splitOn "<<<" with
  | [] => s
  | [only] => only
  | head :: rest =>
    let joined := String.intercalate "<<<" rest
    match joined.splitOn ">>>" with
    -- `_launchCfg` is the grid/block config — discarded on purpose.
    | _launchCfg :: tail => head ++ stripLaunch (String.intercalate ">>>" tail)
    | [] => head

/-- A small sequential fixture with an 8-bit register and an input port, so
    the `.cu` exercises the struct, `eval_tick`, the batch kernel, and the
    set_input/get_output switches. -/
def cudaTop : Module :=
  runModule "CudaTop" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en" (.bitVector 8)
    addOutput "count_out" (.bitVector 8)
    let inc   ← makeWire "inc" (.bitVector 8)
    let count ← emitRegister "count" "clk" "rst" (.ref inc) 0 (.bitVector 8)
    emitAssign inc (.op .add [.ref count, .const 1 8])
    emitAssign "count_out" (.ref count)

def main : IO Unit := do
  let cu := toCudaSim cudaTop
  IO.println s!"[cuda] emitted {cu.length} chars"

  let dir := ".lake/build/gen/cuda"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/cuda_top.cu" cu
  IO.FS.writeFile s!"{dir}/cuda_stub.h" cudaStub

  -- Prepare a host-parseable variant: swap the CUDA runtime include for the
  -- stub, and strip the kernel launch syntax.
  let hostCu := (cu.replace "#include <cuda_runtime.h>" "#include \"cuda_stub.h\"")
                |> stripLaunch
  let checkPath := s!"{dir}/cuda_top_hostcheck.cu"
  IO.FS.writeFile checkPath hostCu

  let findCC : IO (Option String) := do
    for cc in ["g++", "c++", "clang++"] do
      let r ← IO.Process.output { cmd := "which", args := #[cc] }
      if r.exitCode == 0 then return some cc
    return none
  match ← findCC with
  | none =>
    IO.println "[cuda] no host C++ compiler found — syntax check skipped (Layer 1 type-check already ran)"
  | some cc =>
    let r ← IO.Process.output
      { cmd := cc, args := #["-std=c++17", "-fsyntax-only", "-x", "c++", checkPath] }
    if r.exitCode == 0 then
      IO.println s!"[cuda] {cc} -fsyntax-only: OK — emitted CUDA is well-formed"
    else
      IO.println s!"[cuda] {cc} syntax check FAILED:\n{r.stderr}"
      IO.Process.exit 1
  IO.println "\nALL PASS"
