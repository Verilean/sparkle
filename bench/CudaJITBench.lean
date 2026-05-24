/-
  CudaJIT vs CppJIT Performance Benchmark
  ========================================

  Compares simulation throughput across three backends for the same circuit:

    Backend            Instances  Parallelism  Expected throughput
    ─────────────────────────────────────────────────────────────
    CppJIT (1 inst)       1       serial        ~100–1000 Mcyc/s
    CppJIT batch (N)      N       serial CPU    N × single throughput
    CudaJIT (N)           N       GPU parallel  >> N × serial (if GPU available)

  Subject circuits:
    • ALU  — pure combinational (add/and mux), 32-bit operands
    • Counter8 — sequential register (8-bit counter with enable)

  Usage:
    lake exe cuda-jit-bench                 # defaults: 1M cycles, 1K instances
    lake exe cuda-jit-bench 5000000 4096    # 5M cycles, 4096 GPU instances

  The CUDA path requires:
    • nvcc (NVIDIA CUDA Toolkit ≥ 11.0)
    • A CUDA-capable GPU
    Set env var SPARKLE_CUDA=1 to enable it; skipped otherwise.

  Results are printed as a comparison table:
    Backend          Throughput (Minstcyc/s)   Speedup vs CppJIT-1
-/

import Sparkle.Backend.CppSim
import Sparkle.Backend.CudaSim_addition
import Sparkle.Backend.CudaDesignStateStruct
import Sparkle.Core.JIT
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Builder

open Sparkle.Backend.CppSim
open Sparkle.Backend.CudaSim
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.IR.Builder
open Sparkle.Core.JIT
open CircuitM

-- ─────────────────────────────────────────────────────────────────
-- Benchmark circuits
-- ─────────────────────────────────────────────────────────────────

/-- 8-bit counter with synchronous enable.
    Inputs: clk, rst, en.  Output: count_out (8-bit). -/
def benchCounter : Module :=
  runModule "Counter8" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en"  .bit
    addOutput "count_out" (.bitVector 8)
    let inc   ← makeWire "inc"   (.bitVector 8)
    let count ← emitRegister "count" "clk" "rst" (.ref inc) 0 (.bitVector 8)
    emitAssign inc (.op .add [.ref count, .const 1 8])
    let next ← makeWire "next" (.bitVector 8)
    emitAssign next (.op .mux [.ref "en", .ref inc, .ref count])
    emitAssign "count_out" (.ref count)

/-- 32-bit ALU: rs1, rs2, op → result.  Purely combinational. -/
def benchAlu : Module := {
  name        := "ALU32"
  isPrimitive := false
  inputs      := [⟨"rs1", .bitVector 32⟩, ⟨"rs2", .bitVector 32⟩,
                  ⟨"op",  .bitVector 4⟩]
  outputs     := [⟨"result", .bitVector 32⟩]
  wires       := [⟨"_sum", .bitVector 32⟩]
  body        := [
    .assign "_sum"   (.op .add [.ref "rs1", .ref "rs2"]),
    .assign "result" (.op .mux [
      .op .eq [.ref "op", .const 0 4],
      .ref "_sum",
      .op .and [.ref "rs1", .ref "rs2"]]),
  ]
}

-- Wrap a single module as a minimal Design
private def singleModuleDesign (m : Module) : Design :=
  { topModule := m.name, modules := [m] }

-- ─────────────────────────────────────────────────────────────────
-- Result types
-- ─────────────────────────────────────────────────────────────────

structure BenchResult where
  label      : String
  instances  : Nat
  cycles     : Nat
  elapsedMs  : UInt64  -- wall-clock milliseconds
  deriving Repr

/-- Compute instance-cycles per second (Minstcyc/s). -/
def BenchResult.throughput (r : BenchResult) : Float :=
  let instCycles := (r.instances : Float) * (r.cycles : Float)
  instCycles / (r.elapsedMs.toFloat * 1000.0)  -- → Mcyc/s

-- ─────────────────────────────────────────────────────────────────
-- Code generation helpers
-- ─────────────────────────────────────────────────────────────────

/-- Generate JIT-compatible C++ and write to path.  Returns gen time (ms). -/
def genCppJIT (m : Module) (outPath : String) : IO UInt64 := do
  let t0 ← IO.monoMsNow
  let code := toCppSimJIT (singleModuleDesign m)
  IO.FS.writeFile outPath code
  let t1 ← IO.monoMsNow
  return t1 - t0

/-- Generate CUDA .cu and the C++ header, write to paths.  Returns gen time (ms). -/
def genCudaJIT (m : Module) (hdrPath cuPath : String) : IO UInt64 := do
  let d := singleModuleDesign m
  let t0 ← IO.monoMsNow
  -- C++ header (for evalTick class, included by the .cu)
  let hdrCode := toCppSim m
  IO.FS.writeFile hdrPath hdrCode
  -- CUDA .cu (state struct + batch kernel + host JIT API)
  let cuCode := toCudaSim m hdrPath
  IO.FS.writeFile cuPath cuCode
  let t1 ← IO.monoMsNow
  return t1 - t0

-- ─────────────────────────────────────────────────────────────────
-- Compilation helpers
-- ─────────────────────────────────────────────────────────────────

/-- Compile a JIT .cpp → .so with c++ compiler.  Returns compile time (ms). -/
def compileCpp (cppPath soPath : String) : IO UInt64 := do
  let t0 ← IO.monoMsNow
  let r ← IO.Process.output {
    cmd  := "c++"
    args := #["-O2", "-std=c++17", "-shared", "-fPIC",
              "-o", soPath, cppPath]
  }
  let t1 ← IO.monoMsNow
  if r.exitCode != 0 then
    throw (IO.userError s!"CppJIT compile failed:\n{r.stderr}")
  return t1 - t0

/-- Compile a CUDA .cu → .so with nvcc.  Returns compile time (ms).
    Throws if nvcc is not on PATH. -/
def compileCuda (cuPath hdrDir soPath : String) : IO UInt64 := do
  let t0 ← IO.monoMsNow
  let r ← IO.Process.output {
    cmd  := "nvcc"
    args := #["-O2", "-std=c++17", "--compiler-options", "-fPIC",
              "-shared", "-I", hdrDir,
              "-o", soPath, cuPath]
  }
  let t1 ← IO.monoMsNow
  if r.exitCode != 0 then
    throw (IO.userError s!"CudaJIT nvcc compile failed:\n{r.stderr}")
  return t1 - t0

/-- Check whether nvcc is available on PATH. -/
def nvccAvailable : IO Bool := do
  let r ← IO.Process.output { cmd := "nvcc", args := #["--version"] }
  return r.exitCode == 0

-- ─────────────────────────────────────────────────────────────────
-- Inline C harness generators
-- ─────────────────────────────────────────────────────────────────

/-- Generate a C++ benchmark harness for the CppJIT .so.
    Runs N_CYCLES evalTick calls; prints throughput (Mcyc/s) to stdout. -/
def cppJITHarness (soPath : String) (cycles : Nat) : String :=
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <chrono>\n" ++
  "#include <dlfcn.h>\n" ++
  "typedef void*(*fn0)();\n" ++
  "typedef void(*fn1)(void*);\n" ++
  "int main() {\n" ++
  s!"  const uint64_t N = {cycles};\n" ++
  s!"  void* lib = dlopen(\"{soPath}\", RTLD_LAZY);\n" ++
  "  if (!lib) { fprintf(stderr, \"dlopen: %s\\n\", dlerror()); return 1; }\n" ++
  "  auto create  = (fn0)dlsym(lib, \"jit_create\");\n" ++
  "  auto destroy = (fn1)dlsym(lib, \"jit_destroy\");\n" ++
  "  auto reset   = (fn1)dlsym(lib, \"jit_reset\");\n" ++
  "  auto step    = (fn1)dlsym(lib, \"jit_eval_tick\");\n" ++
  "  void* ctx = create(); reset(ctx);\n" ++
  "  auto t0 = std::chrono::high_resolution_clock::now();\n" ++
  "  for (uint64_t i = 0; i < N; i++) step(ctx);\n" ++
  "  auto t1 = std::chrono::high_resolution_clock::now();\n" ++
  "  double ms = std::chrono::duration<double,std::milli>(t1-t0).count();\n" ++
  "  printf(\"%.3f\\n\", N / ms / 1000.0);\n" ++
  "  destroy(ctx); dlclose(lib); return 0;\n" ++
  "}\n"

/-- Generate a C++ batch benchmark harness for the CppJIT .so.
    Runs `instances` independent simulation contexts for `cycles` cycles each
    (all on one CPU thread, sequentially — CPU batch baseline).
    Prints throughput (Minstcyc/s) to stdout. -/
def cppJITBatchHarness (soPath : String) (instances cycles : Nat) : String :=
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <vector>\n" ++
  "#include <chrono>\n" ++
  "#include <dlfcn.h>\n" ++
  "typedef void*(*fn0)();\n" ++
  "typedef void(*fn1)(void*);\n" ++
  "int main() {\n" ++
  s!"  const uint64_t N = {instances};\n" ++
  s!"  const uint64_t C = {cycles};\n" ++
  s!"  void* lib = dlopen(\"{soPath}\", RTLD_LAZY);\n" ++
  "  if (!lib) { fprintf(stderr, \"dlopen: %s\\n\", dlerror()); return 1; }\n" ++
  "  auto create  = (fn0)dlsym(lib, \"jit_create\");\n" ++
  "  auto destroy = (fn1)dlsym(lib, \"jit_destroy\");\n" ++
  "  auto reset   = (fn1)dlsym(lib, \"jit_reset\");\n" ++
  "  auto step    = (fn1)dlsym(lib, \"jit_eval_tick\");\n" ++
  "  std::vector<void*> ctxs(N);\n" ++
  "  for (auto& c : ctxs) { c = create(); reset(c); }\n" ++
  "  auto t0 = std::chrono::high_resolution_clock::now();\n" ++
  "  for (uint64_t i = 0; i < N; i++)\n" ++
  "    for (uint64_t j = 0; j < C; j++) step(ctxs[i]);\n" ++
  "  auto t1 = std::chrono::high_resolution_clock::now();\n" ++
  "  double ms = std::chrono::duration<double,std::milli>(t1-t0).count();\n" ++
  "  double instcyc = (double)N * (double)C;\n" ++
  "  printf(\"%.3f\\n\", instcyc / ms / 1000.0);\n" ++
  "  for (auto c : ctxs) destroy(c);\n" ++
  "  dlclose(lib); return 0;\n" ++
  "}\n"

/-- Generate a C++ benchmark harness for the CudaJIT .so.
    Calls jit_cuda_alloc → jit_cuda_reset → jit_cuda_run(cycles).
    Prints throughput (Minstcyc/s) to stdout. -/
def cudaJITHarness (soPath : String) (instances cycles : Nat) : String :=
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstdint>\n" ++
  "#include <chrono>\n" ++
  "#include <dlfcn.h>\n" ++
  "typedef void* (*fn_alloc)(unsigned int);\n" ++
  "typedef void  (*fn_free)(void*);\n" ++
  "typedef void  (*fn_run)(void*, unsigned int);\n" ++
  "typedef void  (*fn_reset)(void*);\n" ++
  "int main() {\n" ++
  s!"  const unsigned int N = {instances};\n" ++
  s!"  const unsigned int C = {cycles};\n" ++
  s!"  void* lib = dlopen(\"{soPath}\", RTLD_LAZY);\n" ++
  "  if (!lib) { fprintf(stderr, \"dlopen: %s\\n\", dlerror()); return 1; }\n" ++
  "  auto alloc = (fn_alloc) dlsym(lib, \"jit_cuda_alloc\");\n" ++
  "  auto free_h = (fn_free)  dlsym(lib, \"jit_cuda_free\");\n" ++
  "  auto run  = (fn_run)   dlsym(lib, \"jit_cuda_run\");\n" ++
  "  auto rst  = (fn_reset) dlsym(lib, \"jit_cuda_reset\");\n" ++
  "  void* h = alloc(N);\n" ++
  "  rst(h);\n" ++
  "  // Warmup: one run to warm up GPU caches and JIT compilation\n" ++
  "  run(h, 1);\n" ++
  "  auto t0 = std::chrono::high_resolution_clock::now();\n" ++
  "  run(h, C);\n" ++
  "  auto t1 = std::chrono::high_resolution_clock::now();\n" ++
  "  double ms = std::chrono::duration<double,std::milli>(t1-t0).count();\n" ++
  "  double instcyc = (double)N * (double)C;\n" ++
  "  printf(\"%.3f\\n\", instcyc / ms / 1000.0);\n" ++
  "  free_h(h); dlclose(lib); return 0;\n" ++
  "}\n"

-- ─────────────────────────────────────────────────────────────────
-- Harness compile + run
-- ─────────────────────────────────────────────────────────────────

/-- Compile a C++ harness source and run it; return stdout as String. -/
def compileAndRunHarness (src : String) (srcPath exePath : String) : IO String := do
  IO.FS.writeFile srcPath src
  let compile ← IO.Process.output {
    cmd  := "c++"
    args := #["-O2", "-std=c++17", "-o", exePath, srcPath, "-ldl"]
  }
  if compile.exitCode != 0 then
    throw (IO.userError s!"Harness compile failed:\n{compile.stderr}")
  let run ← IO.Process.output { cmd := exePath, args := #[] }
  if run.exitCode != 0 then
    throw (IO.userError s!"Harness run failed:\n{run.stderr}")
  return run.stdout.trim

-- ─────────────────────────────────────────────────────────────────
-- Single benchmark runners
-- ─────────────────────────────────────────────────────────────────

/-- Run CppJIT single-instance benchmark.  Returns (throughput_Mcycs, BenchResult). -/
def runCppJITSingle (m : Module) (cycles : Nat) (tag : String) : IO BenchResult := do
  let prefix := s!"/tmp/sparkle_bench_{sanitizeName m.name}"
  -- Code generation
  let _genMs ← genCppJIT m (prefix ++ ".cpp")
  -- Compile simulation .so
  let _compMs ← compileCpp (prefix ++ ".cpp") (prefix ++ ".so")
  -- Generate + compile harness
  let harnessSrc := cppJITHarness (prefix ++ ".so") cycles
  let outStr ← compileAndRunHarness harnessSrc
    (prefix ++ "_bench.cpp") (prefix ++ "_bench")
  -- outStr is "X.XXX" (Mcyc/s)
  let tp := outStr.toFloat?.getD 0.0
  -- Convert Mcyc/s → elapsed ms for BenchResult
  let elapsedMs := if tp > 0 then
    ((cycles : Float) / (tp * 1000.0)).toUInt64
  else 0
  return { label := tag, instances := 1, cycles := cycles, elapsedMs := elapsedMs }

/-- Run CppJIT batch benchmark (N independent instances, sequential on CPU). -/
def runCppJITBatch (m : Module) (instances cycles : Nat) (tag : String) : IO BenchResult := do
  let prefix := s!"/tmp/sparkle_bench_{sanitizeName m.name}"
  -- Reuse existing .so (already compiled by runCppJITSingle or compile fresh)
  let soPath := prefix ++ ".so"
  if !(← System.FilePath.pathExists soPath) then
    let _ ← genCppJIT m (prefix ++ ".cpp")
    let _ ← compileCpp (prefix ++ ".cpp") soPath
  -- Generate + compile batch harness
  let harnessSrc := cppJITBatchHarness soPath instances cycles
  let outStr ← compileAndRunHarness harnessSrc
    (prefix ++ "_batch.cpp") (prefix ++ "_batch")
  let tp := outStr.toFloat?.getD 0.0
  let totalInstCyc := (instances : Float) * (cycles : Float)
  let elapsedMs := if tp > 0 then (totalInstCyc / (tp * 1000.0)).toUInt64 else 0
  return { label := tag, instances := instances, cycles := cycles, elapsedMs := elapsedMs }

/-- Run CudaJIT benchmark (N parallel GPU instances).
    Returns none if nvcc unavailable or compilation fails. -/
def runCudaJIT (m : Module) (instances cycles : Nat) (tag : String)
    : IO (Option BenchResult) := do
  -- Check for nvcc
  unless ← nvccAvailable do
    return none
  let prefix := s!"/tmp/sparkle_bench_cuda_{sanitizeName m.name}"
  let hdrPath := prefix ++ ".h"
  let cuPath  := prefix ++ ".cu"
  let soPath  := prefix ++ ".so"
  -- Generate files
  let _genMs ← genCudaJIT m hdrPath cuPath
  -- Compile with nvcc
  let _compMs ← compileCuda cuPath "/tmp" soPath
  -- Generate + compile CUDA harness
  let harnessSrc := cudaJITHarness soPath instances cycles
  let outStr ← compileAndRunHarness harnessSrc
    (prefix ++ "_bench.cpp") (prefix ++ "_bench")
  let tp := outStr.toFloat?.getD 0.0
  let totalInstCyc := (instances : Float) * (cycles : Float)
  let elapsedMs := if tp > 0 then (totalInstCyc / (tp * 1000.0)).toUInt64 else 0
  return some { label := tag, instances := instances, cycles := cycles, elapsedMs := elapsedMs }

-- ─────────────────────────────────────────────────────────────────
-- Code generation timing report
-- ─────────────────────────────────────────────────────────────────

/-- Print code generation sizes for both backends. -/
def printCodeGenStats (m : Module) : IO Unit := do
  let cppCode  := toCppSimJIT (singleModuleDesign m)
  let hdrCode  := toCppSim m
  let cuCode   := toCudaSim m (sanitizeName m.name ++ ".h")
  IO.println s!"  C++ JIT code size : {cppCode.length} bytes"
  IO.println s!"  CUDA header size  : {hdrCode.length} bytes"
  IO.println s!"  CUDA .cu size     : {cuCode.length} bytes"

-- ─────────────────────────────────────────────────────────────────
-- Results table
-- ─────────────────────────────────────────────────────────────────

def printTable (results : List (BenchResult × Option Float)) : IO Unit := do
  let hdr := s!"{"Backend",-28} {"Inst":>6} {"Cycles":>10} {"Throughput":>16} {"Speedup":>9}"
  IO.println (String.replicate 75 '─')
  IO.println hdr
  IO.println (String.replicate 75 '─')
  for (r, speedup) in results do
    let tp := r.throughput
    let tpStr := s!"{tp:.3f} Minstcyc/s"
    let spStr := match speedup with
      | none    => "   baseline"
      | some s  => s!"{s:.2f}x"
    IO.println s!"{r.label,-28} {r.instances:>6} {r.cycles:>10} {tpStr:>16} {spStr:>9}"
  IO.println (String.replicate 75 '─')

-- ─────────────────────────────────────────────────────────────────
-- Main
-- ─────────────────────────────────────────────────────────────────

def main (args : List String) : IO UInt32 := do
  -- Parse command-line arguments
  let cycles    := (args.get? 0 >>= String.toNat?).getD 1_000_000
  let instances := (args.get? 1 >>= String.toNat?).getD 1_000

  IO.println "╔══════════════════════════════════════════════════════════════════════════╗"
  IO.println "║          Sparkle: CudaJIT vs CppJIT Performance Benchmark              ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println s!"  Circuits  : Counter8 (sequential), ALU32 (combinational)"
  IO.println s!"  Cycles    : {cycles}"
  IO.println s!"  Instances : {instances} (for batch and CUDA benchmarks)"
  IO.println ""

  -- Check environment
  let cudaEnabled ← nvccAvailable
  IO.println s!"  nvcc      : {if cudaEnabled then "found — CUDA benchmarks enabled" else "not found — CUDA benchmarks skipped"}"
  IO.println ""

  -- ── Counter8 benchmarks ──────────────────────────────────────────
  IO.println "── Circuit: Counter8 (8-bit counter, register) ──────────────────────────"
  IO.println ""
  IO.println "  Code generation:"
  printCodeGenStats benchCounter
  IO.println ""

  IO.println "  Running CppJIT single instance..."
  let cppSingle ← runCppJITSingle benchCounter cycles "CppJIT (1 inst)"

  IO.println s!"  Running CppJIT batch ({instances} instances, sequential)..."
  let cppBatch ← runCppJITBatch benchCounter instances cycles "CppJIT batch"

  let cudaResult? ← if cudaEnabled then do
    IO.println s!"  Running CudaJIT ({instances} GPU instances)..."
    runCudaJIT benchCounter instances cycles "CudaJIT"
  else pure none

  -- Compute speedups relative to single-instance throughput
  let baseTP := cppSingle.throughput
  let counterResults : List (BenchResult × Option Float) :=
    [ (cppSingle, none)
    , (cppBatch, some (cppBatch.throughput / baseTP))
    ] ++ match cudaResult? with
          | none   => []
          | some r => [(r, some (r.throughput / baseTP))]

  IO.println ""
  IO.println "  Counter8 results:"
  printTable counterResults
  IO.println ""

  -- ── ALU32 benchmarks ────────────────────────────────────────────
  IO.println "── Circuit: ALU32 (combinational add/and mux) ───────────────────────────"
  IO.println ""
  IO.println "  Code generation:"
  printCodeGenStats benchAlu
  IO.println ""

  IO.println "  Running CppJIT single instance..."
  let aluSingle ← runCppJITSingle benchAlu cycles "CppJIT (1 inst)"

  IO.println s!"  Running CppJIT batch ({instances} instances, sequential)..."
  let aluBatch ← runCppJITBatch benchAlu instances cycles "CppJIT batch"

  let aluCuda? ← if cudaEnabled then do
    IO.println s!"  Running CudaJIT ({instances} GPU instances)..."
    runCudaJIT benchAlu instances cycles "CudaJIT"
  else pure none

  let aluBase := aluSingle.throughput
  let aluResults : List (BenchResult × Option Float) :=
    [ (aluSingle, none)
    , (aluBatch, some (aluBatch.throughput / aluBase))
    ] ++ match aluCuda? with
          | none   => []
          | some r => [(r, some (r.throughput / aluBase))]

  IO.println ""
  IO.println "  ALU32 results:"
  printTable aluResults
  IO.println ""

  -- ── Summary ────────────────────────────────────────────────────
  IO.println "── Summary ──────────────────────────────────────────────────────────────"
  IO.println ""
  IO.println s!"  CppJIT single-instance throughput:"
  IO.println s!"    Counter8 : {cppSingle.throughput:.3f} Mcyc/s"
  IO.println s!"    ALU32    : {aluSingle.throughput:.3f} Mcyc/s"
  IO.println ""
  IO.println s!"  CppJIT batch ({instances} instances) speedup over single:"
  IO.println s!"    Counter8 : {cppBatch.throughput / cppSingle.throughput:.2f}x  ({cppBatch.throughput:.3f} Minstcyc/s)"
  IO.println s!"    ALU32    : {aluBatch.throughput / aluSingle.throughput:.2f}x  ({aluBatch.throughput:.3f} Minstcyc/s)"
  IO.println ""
  match cudaResult?, aluCuda? with
  | some ctr, some alu =>
    IO.println s!"  CudaJIT ({instances} GPU instances) speedup over CppJIT single:"
    IO.println s!"    Counter8 : {ctr.throughput / cppSingle.throughput:.2f}x  ({ctr.throughput:.3f} Minstcyc/s)"
    IO.println s!"    ALU32    : {alu.throughput / aluSingle.throughput:.2f}x  ({alu.throughput:.3f} Minstcyc/s)"
    IO.println ""
    IO.println s!"  CudaJIT speedup over CppJIT batch (same # instances):"
    IO.println s!"    Counter8 : {ctr.throughput / cppBatch.throughput:.2f}x"
    IO.println s!"    ALU32    : {alu.throughput / aluBatch.throughput:.2f}x"
  | _, _ =>
    IO.println "  CudaJIT: skipped (nvcc not found)"
    IO.println "  To enable: install CUDA Toolkit and ensure nvcc is on PATH"
  IO.println ""
  IO.println "  Expected CUDA speedups (indicative, depends on GPU and circuit):"
  IO.println "    ~10–100x over CppJIT single for large instance counts (N≥1024)"
  IO.println "    ~1–10x  over CppJIT batch  (GPU parallelism vs CPU sequential)"
  IO.println ""

  return 0
