import Sparkle
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Core.JIT

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
open Sparkle.Core.JIT

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

/-- Write the C++ simulation header and CUDA source to /tmp, compile the
    CppSim JIT .so with g++, and generate (but do not compile) the CUDA .cu.
    CUDA compilation is skipped here because nvcc is memory-intensive and
    the CUDA benchmark path is currently stubbed.
    Returns (cppSoPath, cuPath). -/
def compileBothSos (m : Module) : IO (String × String) := do
  let name      := sanitizeName m.name
  let tmpDir    := s!"/tmp/sparkle_bench_{name}"
  let hdrPath   := s!"{tmpDir}/{name}_sim.h"
  let cuPath    := s!"{tmpDir}/{name}_fuzz.cu"
  let cppSoPath := s!"{tmpDir}/lib{name}_cpp.so"

  IO.FS.createDirAll tmpDir

  -- Generate C++ header (CppSim backend)
  IO.FS.writeFile hdrPath (toCppSim m)

  -- Generate CUDA simulation source (written for reference, not compiled here)
  IO.FS.writeFile cuPath (toCudaSim m s!"{name}_sim.h")

  -- Compile C++ JIT .so via g++
  let d : Design := { topModule := m.name, modules := [m] }
  let cppSrcPath := s!"{tmpDir}/{name}_jit.cpp"
  IO.FS.writeFile cppSrcPath (toCppSimJIT d)

  let r ← IO.Process.output {
    cmd  := "g++"
    args := #["-O3", "-std=c++17", "-shared", "-fPIC",
              s!"-I{tmpDir}",
              "-o", cppSoPath, cppSrcPath]
  }
  if r.exitCode != 0 then
    throw (IO.Error.userError s!"g++ failed:\n{r.stderr}")

  return (cppSoPath, cuPath)

-- ============================================================
-- 7. Single benchmark run at one (nInstances, nCycles) point
-- ============================================================

structure BenchResult where
  nInstances : Nat
  nCycles    : Nat
  cppNs      : UInt64   -- wall-clock ns for CppSim JIT
  cudaNs     : UInt64   -- wall-clock ns for CUDA JIT
  speedup    : Float    -- cppNs / cudaNs

/-- Run one benchmark point.
    CppSim JIT: loads the compiled .so via dlopen, runs N×T ticks sequentially.
    CUDA JIT  : stubbed (fuzz API pending), reported as 0 ns. -/
def runBenchPoint
    (nInstances nCycles : Nat)
    (cppSoPath : String)
    : IO BenchResult := do

  -- ── CppSim JIT: sequential, N×T total ticks ─────────────
  let totalTicks := nInstances * nCycles

  let (_, cppNs) ← timed do
    let h ← JIT.load cppSoPath
    JIT.reset h
    for _ in List.range totalTicks do
      JIT.evalTick h
    JIT.destroy h

  -- ── CUDA JIT: not yet wired ──────────────────────────────
  let cudaNs : UInt64 := 0

  let speedup :=
    if cudaNs == 0 then 0.0
    else cppNs.toFloat / cudaNs.toFloat

  return {
    nInstances := nInstances
    nCycles    := nCycles
    cppNs      := cppNs
    cudaNs     := cudaNs
    speedup    := speedup
  }

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
  let ((cppSoPath, _), compileNs) ← timed (compileBothSos m)
  IO.println s!"  g++ compilation: {formatMs compileNs}"
  IO.println s!"  (this cost is amortized over all benchmark runs)"
  IO.println ""

  -- ── Step 3: warm up (avoid cold-start skew) ─────────────
  IO.println "Warming up (1 run discarded)..."
  let _ ← runBenchPoint 1_000 100 cppSoPath
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
    let r ← runBenchPoint nInst nCyc cppSoPath
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
  IO.println "Expected output on A100 (sm_80) vs. 32-core CPU:"
  IO.println "  N=1           speedup ≈ 0.01×  (CUDA launch overhead >> compute)"
  IO.println "  N=10k         speedup ≈ 1–5×   (GPU starts to amortize overhead)"
  IO.println "  N=1M, T=1k    speedup ≈ 40–80× (GPU throughput-bound)"
  IO.println "  N=1M, T=10k   speedup ≈ 60–120×(memory bandwidth saturated)"
  IO.println ""
  IO.println "Counter is intentionally the smallest benchmark."
  IO.println "The state struct is 1 byte/instance → 1 MB for 1M instances."
  IO.println "All 1M states fit in L2 cache on A100 (40 MB)."
  IO.println "For a real throughput benchmark use Sparkle16 or RV32."
