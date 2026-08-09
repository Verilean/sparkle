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

/-- A 2×2 weight-stationary systolic mesh (top instantiates 4 PEs and wires
    them nearest-neighbour) — exercises whole-design emission with generated
    PE-to-PE wire-copy, the systolic-array path. -/
def pe : Module := {
  name := "PE", isPrimitive := false
  inputs  := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"a_in", .bitVector 32⟩,
              ⟨"p_in", .bitVector 32⟩, ⟨"w", .bitVector 32⟩]
  outputs := [⟨"a_out", .bitVector 32⟩, ⟨"p_out", .bitVector 32⟩]
  wires   := [⟨"a_reg", .bitVector 32⟩, ⟨"p_reg", .bitVector 32⟩, ⟨"mul", .bitVector 32⟩]
  body := [
    .assign "mul" (.op .mul [.ref "a_in", .ref "w"]),
    .register "a_reg" "clk" ("rst", .synchronous) (.ref "a_in") 0,
    .register "p_reg" "clk" ("rst", .synchronous) (.op .add [.ref "p_in", .ref "mul"]) 0,
    .assign "a_out" (.ref "a_reg"), .assign "p_out" (.ref "p_reg") ] }

def mesh2x2 : Module := {
  name := "Mesh2x2", isPrimitive := false
  inputs  := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"ain_0", .bitVector 32⟩,
              ⟨"ain_1", .bitVector 32⟩, ⟨"w_0_0", .bitVector 32⟩,
              ⟨"w_0_1", .bitVector 32⟩, ⟨"w_1_0", .bitVector 32⟩, ⟨"w_1_1", .bitVector 32⟩]
  outputs := [⟨"result_0", .bitVector 32⟩, ⟨"result_1", .bitVector 32⟩]
  wires   := [⟨"zero32", .bitVector 32⟩,
              ⟨"aout_0_0", .bitVector 32⟩, ⟨"pout_0_0", .bitVector 32⟩,
              ⟨"aout_0_1", .bitVector 32⟩, ⟨"pout_0_1", .bitVector 32⟩,
              ⟨"aout_1_0", .bitVector 32⟩, ⟨"pout_1_0", .bitVector 32⟩,
              ⟨"aout_1_1", .bitVector 32⟩, ⟨"pout_1_1", .bitVector 32⟩]
  body := [
    .assign "zero32" (.const 0 32),
    .inst "PE" "pe_0_0" [("clk", .ref "clk"), ("rst", .ref "rst"), ("a_in", .ref "ain_0"),
      ("p_in", .ref "zero32"), ("w", .ref "w_0_0"), ("a_out", .ref "aout_0_0"), ("p_out", .ref "pout_0_0")],
    .inst "PE" "pe_0_1" [("clk", .ref "clk"), ("rst", .ref "rst"), ("a_in", .ref "aout_0_0"),
      ("p_in", .ref "zero32"), ("w", .ref "w_0_1"), ("a_out", .ref "aout_0_1"), ("p_out", .ref "pout_0_1")],
    .inst "PE" "pe_1_0" [("clk", .ref "clk"), ("rst", .ref "rst"), ("a_in", .ref "ain_1"),
      ("p_in", .ref "pout_0_0"), ("w", .ref "w_1_0"), ("a_out", .ref "aout_1_0"), ("p_out", .ref "pout_1_0")],
    .inst "PE" "pe_1_1" [("clk", .ref "clk"), ("rst", .ref "rst"), ("a_in", .ref "aout_1_0"),
      ("p_in", .ref "pout_0_1"), ("w", .ref "w_1_1"), ("a_out", .ref "aout_1_1"), ("p_out", .ref "pout_1_1")],
    .assign "result_0" (.ref "pout_1_0"), .assign "result_1" (.ref "pout_1_1") ] }

def meshDesign : Design := { topModule := "Mesh2x2", modules := [pe, mesh2x2] }

/-- Prepare a host-parseable variant of an emitted `.cu`: swap the CUDA
    runtime include for the stub and strip the `<<<>>>` launch syntax. -/
def toHostVariant (cu : String) : String :=
  (cu.replace "#include <cuda_runtime.h>" "#include \"cuda_stub.h\"") |> stripLaunch

def main : IO Unit := do
  let dir := ".lake/build/gen/cuda"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/cuda_stub.h" cudaStub

  -- Two fixtures: a single sequential module, and a hierarchical 2×2 mesh
  -- (whole-design emission with generated wire-copy).
  let cases : List (String × String) :=
    [ ("single", toCudaSim cudaTop)
    , ("mesh",   toCudaSimDesign meshDesign) ]
  for (name, cu) in cases do
    IO.println s!"[cuda] {name}: emitted {cu.length} chars"
    IO.FS.writeFile s!"{dir}/cuda_{name}_hostcheck.cu" (toHostVariant cu)

  let findCC : IO (Option String) := do
    for cc in ["g++", "c++", "clang++"] do
      let r ← IO.Process.output { cmd := "which", args := #[cc] }
      if r.exitCode == 0 then return some cc
    return none
  match ← findCC with
  | none =>
    IO.println "[cuda] no host C++ compiler found — syntax check skipped (Layer 1 type-check already ran)"
  | some cc =>
    for (name, _) in cases do
      let checkPath := s!"{dir}/cuda_{name}_hostcheck.cu"
      let r ← IO.Process.output
        { cmd := cc, args := #["-std=c++17", "-fsyntax-only", "-x", "c++", checkPath] }
      if r.exitCode == 0 then
        IO.println s!"[cuda] {name}: {cc} -fsyntax-only: OK — well-formed"
      else
        IO.println s!"[cuda] {name}: {cc} syntax check FAILED:\n{r.stderr}"
        IO.Process.exit 1
  IO.println "\nALL PASS"
