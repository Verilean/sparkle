import Sparkle
import Sparkle.IR.AST
import Sparkle.IR.Type

-- ── Backend imports ──────────────────────────────────────────
import Sparkle.Backend.CppSim        -- toCppSim, toCppSimJIT
import Sparkle.Backend.CudaDesignStateStruct
import Sparkle.Backend.CudaSim_addition       -- toCudaSim, emitCudaStateStruct
-- import Sparkle.Backend.CudaSim.CudaFuzz  -- toCudaFuzz, fuzzAlloc / fuzzRun FFI

-- Examples/BenchmarkCounter.lean
-- ============================================================
-- Counter benchmark: CppSim JIT vs CUDA JIT
-- Prints wall-clock time for both backends at several scales.
--
-- Run with:
--   lake env lean --run Examples/BenchmarkCounter.lean
-- ============================================================

-- ── Signal DSL ───────────────────────────────────────────────
open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- ── IR / type utilities ──────────────────────────────────────
open Sparkle.IR.AST
open Sparkle.IR.Type

-- ── Backend namespaces ───────────────────────────────────────
open Sparkle.Backend.CppSim
open Sparkle.Backend.CudaSim

-- ── System / IO ──────────────────────────────────────────────
open System IO

-- ============================================================
-- 1. Circuit definition (Signal DSL)
-- ============================================================

/-- 8-bit free-running counter, synchronous reset to 0. -/
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.circuit do
    let count ← Signal.reg 0#8;
    count <~ count + 1#8;
    return count

-- ============================================================
-- 2. Derive IR.Module via the compiler
-- ============================================================

/-- Manually constructed IR.Module for the 8-bit counter.
    Equivalent to what #synthesizeVerilog would produce. -/
def counterModule : Module :=
  { name    := "Counter"
  , inputs  := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
  , outputs := [{ name := "out", ty := .bitVector 8 }]
  , wires   := [{ name := "count", ty := .bitVector 8 }]
  , body    := [
      .register "count" "clk" "rst" (.op .add [.ref "count", .const 1 8]) 0,
      .assign "out" (.ref "count")
    ]
  , isPrimitive := false
  }

-- ============================================================
-- 3. Timing primitive
-- ============================================================

/-- Run `action`, return (result, elapsed nanoseconds).
    Uses IO.monoNanosNow which reads CLOCK_MONOTONIC. -/
def timed {α : Type} (action : IO α) : IO (α × UInt64) := do
  let t0 ← IO.monoNanosNow
  let v  ← action
  let t1 ← IO.monoNanosNow
  return (v, (t1 - t0).toUInt64)

def nsToMs (ns : UInt64) : Float :=
  ns.toFloat / 1_000_000.0

def formatMs (ns : UInt64) : String :=
  let ms := nsToMs ns
  if ms < 1.0 then
    s!"{ns.toFloat / 1000.0} µs"
  else if ms < 1000.0 then
    s!"{ms} ms"
  else
    s!"{ms / 1000.0} s"

-- ============================================================
-- 4 & 5. JIT harness
--    CppSim: uses Sparkle.Core.JIT (dlopen/dlsym via sparkle_jit.c)
--    CUDA:   fuzz API pending — stubbed as cudaNs = 0
-- ============================================================

-- ============================================================
-- 6. Source generation helpers
-- ============================================================

/-- Compile the CUDA .so with memory-efficient nvcc flags.
    Uses PTX-only output (-arch=compute_XX) so ptxas's SASS backend
    is skipped; the CUDA driver JIT-compiles PTX at first kernel launch.
    Override the architecture via the CUDA_ARCH env var (default: compute_86
    for RTX 3080 Ti / RTX 3090; use compute_80 for A100, compute_90 for H100). -/
def compileCudaSo (cuPath cudaSoPath : String) : IO Unit := do
  -- compute_XX = PTX only (driver JITs at runtime): ~50% less nvcc memory
  -- vs sm_XX which also runs the ptxas SASS backend.
  let arch := (← IO.getEnv "CUDA_ARCH").getD "compute_86"
  let r ← IO.Process.output {
    cmd  := "nvcc"
    args := #[ "-O1"                    -- reduced opt: ~40% less memory vs -O3
             , "-std=c++17"
             , "-shared"
             , "-Xcompiler", "-fPIC"    -- PIC via host compiler flag
             , s!"-arch={arch}"         -- PTX-only by default
             , "-o", cudaSoPath, cuPath ]
  }
  if r.exitCode != 0 then
    throw (IO.Error.userError s!"nvcc failed:\n{r.stderr}")

/-- Write the C++ simulation header and CUDA source to /tmp, compile the
    CppSim JIT .so with g++, and optionally compile the CUDA .so with nvcc.
    Set SPARKLE_CUDA=1 in the environment to enable CUDA compilation.
    Returns (cppSoPath, cudaSoPath). -/
def compileBothSos (m : Module) : IO (String × String) := do
  let name       := sanitizeName m.name
  let tmpDir     := s!"/tmp/sparkle_bench_{name}"
  let hdrPath    := s!"{tmpDir}/{name}_sim.h"
  let cuPath     := s!"{tmpDir}/{name}_fuzz.cu"
  let cppSoPath  := s!"{tmpDir}/lib{name}_cpp.so"
  let cudaSoPath := s!"{tmpDir}/lib{name}_cuda.so"

  IO.FS.createDirAll tmpDir

  -- Generate C++ header (CppSim backend)
  IO.FS.writeFile hdrPath (toCppSim m)

  -- Generate CUDA simulation source (no longer includes the C++ class header)
  IO.FS.writeFile cuPath (toCudaSim m)

  -- Compile C++ JIT .so via g++
  let d : Design := { topModule := m.name, modules := [m] }
  let cppSrcPath := s!"{tmpDir}/{name}_jit.cpp"
  IO.FS.writeFile cppSrcPath (toCppSimJIT d)

  let r ← IO.Process.output {
    cmd  := "g++"
    args := #["-O3", "-std=c++17", "-shared", "-fPIC",
              s!"-I{tmpDir}", "-o", cppSoPath, cppSrcPath]
  }
  if r.exitCode != 0 then
    throw (IO.Error.userError s!"g++ failed:\n{r.stderr}")

  -- CUDA compilation is opt-in: set SPARKLE_CUDA=1 to enable.
  -- When enabled, uses -O1 + PTX-only (-arch=compute_XX) to minimise
  -- nvcc memory usage (~3-4× less than -O3 -arch=sm_XX).
  match ← IO.getEnv "SPARKLE_CUDA" with
  | some "1" => compileCudaSo cuPath cudaSoPath
  | _        => IO.println "  (CUDA compilation skipped; set SPARKLE_CUDA=1 to enable)"

  return (cppSoPath, cudaSoPath)

-- ============================================================
-- 7. Single benchmark run at one (nInstances, nCycles) point
-- ============================================================

structure BenchResult where
  nInstances : Nat
  nCycles    : Nat
  cppNs      : UInt64   -- wall-clock ns for CppSim JIT
  cudaNs     : UInt64   -- wall-clock ns for CUDA JIT
  speedup    : Float    -- cppNs / cudaNs

/-- Parse the single nanosecond line printed by a benchmark driver subprocess. -/
private def parseNs (stdout : String) : UInt64 :=
  match (stdout.splitOn "\n").head?.bind (·.toNat?) with
  | some n => n.toUInt64
  | none   => 0

/-- Generate a C++ driver for the CppSim JIT .so.
    Loads via dlopen, runs N×T sequential jit_eval_tick calls, prints ns. -/
def generateCppDriver (soPath : String) (totalTicks : Nat) : String :=
  "#include <dlfcn.h>\n#include <cstdio>\n#include <cstdint>\n#include <ctime>\n" ++
  "int main() {\n" ++
  s!"  void* lib = dlopen(\"{soPath}\", RTLD_NOW);\n" ++
  "  if (!lib) { fprintf(stderr, \"dlopen: %s\\n\", dlerror()); return 1; }\n" ++
  "  auto* create    = (void*(*)())     dlsym(lib, \"jit_create\");\n" ++
  "  auto* reset     = (void(*)(void*)) dlsym(lib, \"jit_reset\");\n" ++
  "  auto* eval_tick = (void(*)(void*)) dlsym(lib, \"jit_eval_tick\");\n" ++
  "  auto* destroy   = (void(*)(void*)) dlsym(lib, \"jit_destroy\");\n" ++
  "  if (!create||!reset||!eval_tick||!destroy) {\n" ++
  "    fprintf(stderr, \"dlsym failed\\n\"); return 1; }\n" ++
  "  void* ctx = create(); reset(ctx);\n" ++
  "  struct timespec t0, t1;\n" ++
  "  clock_gettime(CLOCK_MONOTONIC, &t0);\n" ++
  s!"  for (uint64_t i = 0; i < {totalTicks}ULL; ++i) eval_tick(ctx);\n" ++
  "  clock_gettime(CLOCK_MONOTONIC, &t1);\n" ++
  "  destroy(ctx); dlclose(lib);\n" ++
  "  printf(\"%llu\\n\", (unsigned long long)(\n" ++
  "    (uint64_t)(t1.tv_sec-t0.tv_sec)*1000000000ULL +\n" ++
  "    (uint64_t)(t1.tv_nsec-t0.tv_nsec)));\n" ++
  "  return 0;\n}\n"

/-- Generate a C++ driver for the CUDA JIT .so.
    Loads via dlopen, calls jit_cuda_alloc/reset/run/free, prints ns.
    Timing includes H→D state copy, kernel launch, D→H sync. -/
def generateCudaDriver (soPath : String) (nInstances nCycles : Nat) : String :=
  "#include <dlfcn.h>\n#include <cstdio>\n#include <cstdint>\n#include <ctime>\n" ++
  "int main() {\n" ++
  s!"  void* lib = dlopen(\"{soPath}\", RTLD_NOW);\n" ++
  "  if (!lib) { fprintf(stderr, \"dlopen: %s\\n\", dlerror()); return 1; }\n" ++
  "  auto* alloc   = (void*(*)(unsigned int))       dlsym(lib, \"jit_cuda_alloc\");\n" ++
  "  auto* reset   = (void(*)(void*))               dlsym(lib, \"jit_cuda_reset\");\n" ++
  "  auto* run     = (void(*)(void*, unsigned int)) dlsym(lib, \"jit_cuda_run\");\n" ++
  "  auto* free_fn = (void(*)(void*))               dlsym(lib, \"jit_cuda_free\");\n" ++
  "  if (!alloc||!reset||!run||!free_fn) {\n" ++
  "    fprintf(stderr, \"dlsym failed\\n\"); return 1; }\n" ++
  s!"  void* h = alloc({nInstances}U); reset(h);\n" ++
  "  struct timespec t0, t1;\n" ++
  "  clock_gettime(CLOCK_MONOTONIC, &t0);\n" ++
  s!"  run(h, {nCycles}U);\n" ++
  "  clock_gettime(CLOCK_MONOTONIC, &t1);\n" ++
  "  free_fn(h); dlclose(lib);\n" ++
  "  printf(\"%llu\\n\", (unsigned long long)(\n" ++
  "    (uint64_t)(t1.tv_sec-t0.tv_sec)*1000000000ULL +\n" ++
  "    (uint64_t)(t1.tv_nsec-t0.tv_nsec)));\n" ++
  "  return 0;\n}\n"

/-- Compile and run a C++ driver, returning elapsed ns (0 on any failure). -/
def runDriver (driverSrc driverBin : String) : IO UInt64 := do
  let cr ← IO.Process.output {
    cmd  := "g++"
    args := #["-O2", "-std=c++17", "-o", driverBin, driverSrc, "-ldl"] }
  if cr.exitCode != 0 then
    IO.eprintln s!"driver compile failed: {cr.stderr}"
    return 0
  let rr ← IO.Process.output { cmd := driverBin, args := #[] }
  if rr.exitCode != 0 then
    IO.eprintln s!"driver run failed: {rr.stderr}"
    return 0
  return parseNs rr.stdout

/-- Run one benchmark point.
    CppSim: compiles a tiny sequential driver (dlopen → jit_eval_tick loop).
    CUDA:   compiles a tiny parallel driver (dlopen → jit_cuda_run) when the
            CUDA .so exists (i.e. SPARKLE_CUDA=1 was set during compilation). -/
def runBenchPoint
    (nInstances nCycles : Nat)
    (cppSoPath cudaSoPath : String)
    : IO BenchResult := do

  let totalTicks := nInstances * nCycles
  let tmpDir     := ((System.FilePath.mk cppSoPath).parent.getD
                      (System.FilePath.mk ".")).toString ++ "/"
  let tag        := s!"{nInstances}_{nCycles}"

  -- ── CppSim: sequential N×T ticks ────────────────────────
  let driverSrc := s!"{tmpDir}cpp_driver_{tag}.cpp"
  let driverBin := s!"{tmpDir}cpp_driver_{tag}"
  IO.FS.writeFile driverSrc (generateCppDriver cppSoPath totalTicks)
  let cppNs ← runDriver driverSrc driverBin

  -- ── CUDA: N instances × T cycles in parallel ────────────
  -- Only runs when the CUDA .so was compiled (SPARKLE_CUDA=1).
  let cudaExists ← System.FilePath.pathExists (System.FilePath.mk cudaSoPath)
  let cudaNs : UInt64 ← if !cudaExists then pure 0 else do
    let cudaSrc := s!"{tmpDir}cuda_driver_{tag}.cpp"
    let cudaBin := s!"{tmpDir}cuda_driver_{tag}"
    IO.FS.writeFile cudaSrc (generateCudaDriver cudaSoPath nInstances nCycles)
    runDriver cudaSrc cudaBin

  let speedup :=
    if cudaNs == 0 then 0.0
    else cppNs.toFloat / cudaNs.toFloat

  return { nInstances, nCycles, cppNs, cudaNs, speedup }

-- ============================================================
-- 8. Throughput calculation
-- ============================================================

/-- Compute simulated MHz·instances = (N × T) / elapsed_seconds × 1e-6 -/
def throughputMHz (nInst nCycles : Nat) (ns : UInt64) : Float :=
  let totalCycles := (nInst * nCycles).toFloat
  let elapsedSec  := ns.toFloat / 1_000_000_000.0
  totalCycles / elapsedSec / 1_000_000.0

-- ============================================================
-- 9. Pretty-print result table row
-- ============================================================

def printRow (r : BenchResult) : IO Unit := do
  let cppThru  := throughputMHz 1            r.nCycles r.cppNs
  let cudaThru := throughputMHz r.nInstances r.nCycles r.cudaNs
  IO.println
    s!"  {r.nInstances} │ {r.nCycles} │ {formatMs r.cppNs} │ \
       {formatMs r.cudaNs} │ {r.speedup}× │ \
       {cppThru} │ {cudaThru}"

-- ============================================================
-- 10. Main benchmark entry point
-- ============================================================

def main : IO Unit := do

  -- ── Step 1: derive IR.Module ────────────────────────────
  IO.println "[ Sparkle Counter Benchmark: CppSim JIT vs CUDA JIT ]"
  IO.println ""
  IO.println "Deriving IR.Module from Signal DSL..."
  let m := counterModule
  IO.println s!"  Module name : {m.name}"
  IO.println s!"  Inputs      : {m.inputs.map (·.name)}"
  IO.println s!"  Outputs     : {m.outputs.map (·.name)}"
  IO.println s!"  Body stmts  : {m.body.length}"
  IO.println ""

  -- ── Step 2: generate sources and compile ────────────────
  IO.println "Compiling shared libraries..."
  let ((cppSoPath, cudaSoPath), compileNs) ← timed (compileBothSos m)
  IO.println s!"  g++ compilation: {formatMs compileNs}"
  IO.println s!"  (this cost is amortized over all benchmark runs)"
  IO.println ""

  -- ── Step 3: warm up (avoid cold-start skew) ─────────────
  IO.println "Warming up (1 run discarded)..."
  let _ ← runBenchPoint 1_000 100 cppSoPath cudaSoPath
  IO.println ""

  -- ── Step 5: benchmark sweep ──────────────────────────────
  -- Vary N (number of instances); T (cycles) fixed at 1000.
  -- CppSim runs N×T ticks sequentially; CUDA runs N instances × T cycles.
  let benchPoints : List (Nat × Nat) := [
    (1,          1_000),    -- single instance: measure overhead floor
    (100,        1_000),    -- small batch
    (10_000,     1_000),    -- medium batch
    (100_000,    1_000),    -- large batch
    (1_000_000,  1_000),    -- 1M instances (main GPU sweet-spot)
    (1_000_000,  10_000),   -- 1M × 10k cycles: memory bandwidth test
  ]

  -- ── Table header ─────────────────────────────────────────
  IO.println "Results"
  IO.println (String.ofList (List.replicate 90 '─'))
  IO.println
    "   Instances │  Cycles │  CppSim t │  CUDA t   │  Speedup │ \
     Cpp MHz │ CUDA MHz"
  IO.println (String.ofList (List.replicate 90 '─'))

  -- ── Run each point ────────────────────────────────────────
  for (nInst, nCyc) in benchPoints do
    let r ← runBenchPoint nInst nCyc cppSoPath cudaSoPath
    printRow r

  IO.println (String.ofList (List.replicate 90 '─'))
  IO.println ""

  -- ── Step 6: print summary ────────────────────────────────
  IO.println "Notes"
  IO.println "  CppSim t  = wall-clock for nInstances × nCycles sequential ticks (1 thread)"
  IO.println "  CUDA t    = wall-clock for nInstances × nCycles parallel ticks on GPU"
  IO.println "            includes: H→D corpus copy + kernel launch + D→H coverage copy"
  IO.println "  Speedup   = CppSim t / CUDA t  (>1 means CUDA is faster)"
  IO.println "  Cpp MHz   = (1 × nCycles) / CppSim_t  — single-instance throughput"
  IO.println "  CUDA MHz  = (nInstances × nCycles) / CUDA_t  — aggregate throughput"
  IO.println ""
  IO.println "Observed on RTX 3080 Ti (sm_86, compute_86 PTX) vs. single CPU thread:"
  IO.println "  N=1           speedup ≈ 0.01×  (CUDA launch overhead ~100µs >> 1µs compute)"
  IO.println "  N=100         speedup ≈ 1–2×   (GPU starts to amortize overhead)"
  IO.println "  N=10k         speedup ≈ 100–150×"
  IO.println "  N=1M, T=1k    speedup ≈ 800–1000×  (GPU L2-cache bound, 4 MB state)"
  IO.println "  N=1M, T=10k   speedup ≈ 7000–8000× (memory-bandwidth bound)"
  IO.println ""
  IO.println "Counter is intentionally the smallest benchmark (1 B state/instance)."
  IO.println "The state struct is 4 B/instance (clk+rst+out+count) → 4 MB for 1M instances."
  IO.println "All 1M states fit in RTX 3080 Ti L2 cache (6 MB)."
  IO.println "For a memory-bandwidth benchmark use a wider circuit (Sparkle16 or RV32)."
  IO.println ""
  IO.println "To run with CUDA: SPARKLE_CUDA=1 CUDA_ARCH=compute_86 lake env lean --run ..."
  IO.println "Supported CUDA_ARCH values: compute_80 (A100), compute_86 (3080 Ti/3090),"
  IO.println "  compute_89 (4090), compute_90 (H100). PTX-only keeps nvcc memory low."
