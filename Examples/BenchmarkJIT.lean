-- Examples/BenchmarkJIT.lean
-- ============================================================
-- Combined JIT benchmark: Counter (8-bit, 4 B state) vs
--                         WideAccum (16×32-bit, 128 B state)
-- CppSim JIT (sequential, 1 thread) vs CUDA JIT (parallel, N instances)
--
-- Run with:
--   lake env lean --run Examples/BenchmarkJIT.lean
--
-- CUDA compilation is opt-in (nvcc uses ~500 MB even for small .cu files):
--   SPARKLE_CUDA=1 CUDA_ARCH=compute_86 lake env lean --run Examples/BenchmarkJIT.lean
--
-- CUDA_ARCH choices: compute_86 (RTX 30xx/3080Ti), compute_80 (A100),
--                    compute_89 (RTX 40xx), compute_90 (H100)
-- ============================================================

-- ── Sparkle core ─────────────────────────────────────────────
import Sparkle
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Compiler.SynthesizeModule   -- #synthesizeModule command

-- ── Backends ─────────────────────────────────────────────────
import Sparkle.Backend.CppSim
import Sparkle.Backend.CudaSim_addition

-- ── IP modules ───────────────────────────────────────────────
import IP.RV32.Pipeline

-- ── DSL / domain ─────────────────────────────────────────────
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CppSim
open Sparkle.Backend.CudaSim

-- ============================================================
-- 1.  Circuit definitions (Signal DSL)
-- ============================================================

-- ── 1a. Counter (8-bit, 4 B state per instance) ──────────────
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  Signal.circuit do
    let count ← Signal.reg 0#8;
    count <~ count + 1#8;
    return count

-- ── 1b. WideAccum: 16 cascaded 32-bit registers (128 B state) ─
-- r0 increments every cycle; r[i] += r[i-1].
-- Provides a memory-bandwidth-bound contrast to the counter.
def wideAccum {dom : DomainConfig} : Signal dom (BitVec 32) :=
  Signal.circuit do
    let r0  ← Signal.reg 0#32; let r1  ← Signal.reg 0#32;
    let r2  ← Signal.reg 0#32; let r3  ← Signal.reg 0#32;
    let r4  ← Signal.reg 0#32; let r5  ← Signal.reg 0#32;
    let r6  ← Signal.reg 0#32; let r7  ← Signal.reg 0#32;
    let r8  ← Signal.reg 0#32; let r9  ← Signal.reg 0#32;
    let r10 ← Signal.reg 0#32; let r11 ← Signal.reg 0#32;
    let r12 ← Signal.reg 0#32; let r13 ← Signal.reg 0#32;
    let r14 ← Signal.reg 0#32; let r15 ← Signal.reg 0#32;
    r0  <~ r0 + 1#32;
    r1  <~ r1  + r0;
    r2  <~ r2  + r1;
    r3  <~ r3  + r2;
    r4  <~ r4  + r3;
    r5  <~ r5  + r4;
    r6  <~ r6  + r5;
    r7  <~ r7  + r6;
    r8  <~ r8  + r7;
    r9  <~ r9  + r8;
    r10 <~ r10 + r9;
    r11 <~ r11 + r10;
    r12 <~ r12 + r11;
    r13 <~ r13 + r12;
    r14 <~ r14 + r13;
    r15 <~ r15 + r14;
    return r15

-- ============================================================
-- 2.  IR.Module derivations
-- ============================================================

-- Counter: built manually (trivial IR)
def counterModule : Module :=
  { name    := "Counter"
  , inputs  := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
  , outputs := [{ name := "out", ty := .bitVector 8 }]
  , wires   := [{ name := "count", ty := .bitVector 8 }]
  , body    := [
      .register "count" "clk" "rst" (.op .add [.ref "count", .const 1 8]) 0,
      .assign "out" (.ref "count")
    ]
  , isPrimitive := false }

-- WideAccum: built manually (16-register cascade)
def wideAccumModule : Module :=
  let nRegs := 16
  let regs  := List.range nRegs |>.map fun i =>
    ({ name := s!"r{i}", ty := .bitVector 32 } : Port)
  let body  := List.range nRegs |>.map fun i =>
    let rhs : Expr :=
      if i == 0 then .op .add [.ref "r0", .const 1 32]
      else .op .add [.ref s!"r{i-1}", .ref s!"r{i}"]
    .register s!"r{i}" "clk" "rst" rhs 0
  let outStmt := [.assign "out" (.ref s!"r{nRegs - 1}")]
  { name    := "WideAccum"
  , inputs  := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
  , outputs := [{ name := "out", ty := .bitVector 32 }]
  , wires   := regs
  , body    := body ++ outStmt
  , isPrimitive := false }

-- RV32Core: synthesized from the Signal DSL pipeline at compile time.
-- Produces a Module with 8 inputs (6 user + clk + rst), 1 output,
-- 1441 wires, and ~1436 body statements (44 registers + combinational logic).
-- Each evalTick call executes ~1436 IR statements (~700× more than Counter).
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open Sparkle.IP.RV32 in
#synthesizeModule rv32SynthMod from rv32iCore

-- Give it a short name and mark user-input ports for display
def rv32Module : Module := { rv32SynthMod with name := "RV32Core" }

-- ============================================================
-- 3.  Timing helpers
-- ============================================================

def timed {α : Type} (action : IO α) : IO (α × UInt64) := do
  let t0 ← IO.monoNanosNow
  let v  ← action
  let t1 ← IO.monoNanosNow
  return (v, (t1 - t0).toUInt64)

def fmtTime (ns : UInt64) : String :=
  let us := ns.toFloat / 1_000.0
  let ms := ns.toFloat / 1_000_000.0
  let s  := ns.toFloat / 1_000_000_000.0
  if ns == 0     then "--"
  else if us < 999.0  then s!"{us} µs"
  else if ms < 999.0  then s!"{ms} ms"
  else s!"{s} s"

def fmtMHz (nInst nCyc : Nat) (ns : UInt64) : String :=
  if ns == 0 then "--"
  else
    let mhz := (nInst * nCyc).toFloat / (ns.toFloat / 1e9) / 1e6
    if mhz < 1.0      then s!"{mhz * 1000.0} kHz"
    else if mhz < 1e4 then s!"{mhz} MHz"
    else s!"{mhz / 1000.0} GHz"

def fmtSpeedup (cppNs cudaNs : UInt64) : String :=
  if cudaNs == 0 then "--"
  else
    let x := cppNs.toFloat / cudaNs.toFloat
    s!"{x}×"

-- ============================================================
-- 4.  Source generation and compilation helpers
-- ============================================================

/-- Compile a CUDA .so with memory-efficient flags.
    PTX-only (-arch=compute_XX) skips the ptxas SASS backend (~50% less RAM).
    Returns true on success, false with a warning on failure (e.g. wide types
    in modules that use Signal.loop with bundled state). -/
def compileCudaSo (cuPath cudaSoPath : String) : IO Bool := do
  let arch := (← IO.getEnv "CUDA_ARCH").getD "compute_86"
  let r ← IO.Process.output {
    cmd  := "nvcc"
    args := #["-O1", "-std=c++17", "-shared", "-Xcompiler", "-fPIC",
              s!"-arch={arch}", "-o", cudaSoPath, cuPath] }
  if r.exitCode != 0 then
    IO.eprintln s!"  nvcc warning: skipping CUDA for this module (wide types not supported in device code)"
    return false
  return true

/-- Compile one module into CppSim and (optionally) CUDA shared libraries.
    CUDA compilation is skipped unless SPARKLE_CUDA=1 is set in the environment.
    Returns (cppSoPath, cudaSoPath). -/
def compileMod (m : Module) : IO (String × String) := do
  let name       := sanitizeName m.name
  let dir        := s!"/tmp/sparkle_jit_bench_{name}"
  let hdrPath    := s!"{dir}/{name}_sim.h"
  let cuPath     := s!"{dir}/{name}_fuzz.cu"
  let cppSrcPath := s!"{dir}/{name}_jit.cpp"
  let cppSoPath  := s!"{dir}/lib{name}_cpp.so"
  let cudaSoPath := s!"{dir}/lib{name}_cuda.so"

  IO.FS.createDirAll dir

  -- C++ simulation header (for reference / CUDA include)
  IO.FS.writeFile hdrPath (toCppSim m)

  -- CUDA source (state-struct-based device code, no class include)
  IO.FS.writeFile cuPath (toCudaSim m)

  -- C++ JIT wrapper
  let d : Design := { topModule := m.name, modules := [m] }
  IO.FS.writeFile cppSrcPath (toCppSimJIT d)

  -- Compile CppSim .so
  let r ← IO.Process.output {
    cmd  := "g++"
    args := #["-O3", "-std=c++17", "-shared", "-fPIC",
              s!"-I{dir}", "-o", cppSoPath, cppSrcPath] }
  if r.exitCode != 0 then
    throw (IO.Error.userError s!"g++ failed for {name}:\n{r.stderr}")

  -- CUDA .so (opt-in); failure is non-fatal (wide types fall back to --)
  match ← IO.getEnv "SPARKLE_CUDA" with
  | some "1" => let _ ← compileCudaSo cuPath cudaSoPath; pure ()
  | _        => pure ()

  return (cppSoPath, cudaSoPath)

-- ============================================================
-- 5.  Benchmark driver generators
-- ============================================================

private def parseNs (stdout : String) : UInt64 :=
  match (stdout.splitOn "\n").head?.bind (·.toNat?) with
  | some n => n.toUInt64
  | none   => 0

/-- C++ driver: dlopen CppSim .so, run N×T jit_eval_tick, print ns. -/
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

/-- C++ driver: dlopen CUDA .so, alloc N instances, run T cycles, print ns. -/
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

/-- Compile a driver source with g++ -ldl, return elapsed ns or 0 on failure. -/
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

-- ============================================================
-- 6.  Benchmark point
-- ============================================================

structure BenchPoint where
  label  : String
  nInst  : Nat
  nCyc   : Nat
  cppNs  : UInt64
  cudaNs : UInt64

/-- Run one benchmark point for a pre-compiled .so pair.
    CppSim driver: N×T sequential ticks (single-thread).
    CUDA driver:   N instances × T cycles in parallel (GPU).
                   Skipped if the CUDA .so does not exist. -/
def runPoint
    (label : String)
    (nInst nCyc : Nat)
    (cppSoPath cudaSoPath : String)
    : IO BenchPoint := do
  let totalTicks := nInst * nCyc
  let tmpDir     := ((System.FilePath.mk cppSoPath).parent.getD
                      (System.FilePath.mk ".")).toString ++ "/"
  let tag        := s!"{label}_{nInst}_{nCyc}" |>.replace " " "_"

  -- CppSim driver
  let cppSrc := s!"{tmpDir}cpp_{tag}.cpp"
  let cppBin := s!"{tmpDir}cpp_{tag}"
  IO.FS.writeFile cppSrc (generateCppDriver cppSoPath totalTicks)
  let cppNs ← runDriver cppSrc cppBin

  -- CUDA driver (only when .so was compiled)
  let cudaExists ← System.FilePath.pathExists (System.FilePath.mk cudaSoPath)
  let cudaNs : UInt64 ← if !cudaExists then pure 0 else do
    let cudaSrc := s!"{tmpDir}cuda_{tag}.cpp"
    let cudaBin := s!"{tmpDir}cuda_{tag}"
    IO.FS.writeFile cudaSrc (generateCudaDriver cudaSoPath nInst nCyc)
    runDriver cudaSrc cudaBin

  return { label, nInst, nCyc, cppNs, cudaNs }

-- ============================================================
-- 7.  Table printing
-- ============================================================

def printHeader : IO Unit := do
  let sep := String.ofList (List.replicate 102 '─')
  IO.println sep
  IO.println
    "  Label              │  N Inst   │ Cycles │    CppSim t │    CUDA t   │  Speedup │ Cpp thrput │ CUDA thrput"
  IO.println sep

def printRow (p : BenchPoint) : IO Unit :=
  IO.println
    s!"  {p.label} │ {p.nInst} │ {p.nCyc} │ \
       {fmtTime p.cppNs} │ {fmtTime p.cudaNs} │ \
       {fmtSpeedup p.cppNs p.cudaNs} │ \
       {fmtMHz 1 (p.nInst * p.nCyc) p.cppNs} │ \
       {fmtMHz p.nInst p.nCyc p.cudaNs}"

def printFooter : IO Unit :=
  IO.println (String.ofList (List.replicate 102 '─'))

-- ============================================================
-- 8.  Main
-- ============================================================

def main : IO Unit := do
  IO.println ""
  IO.println "╔══════════════════════════════════════════════════════════╗"
  IO.println "║   Sparkle JIT Benchmark  ·  CppSim vs CUDA              ║"
  IO.println "║   Counter / WideAccum / RV32Core (4B / 64B / ~200B)     ║"
  IO.println "╚══════════════════════════════════════════════════════════╝"
  IO.println ""

  -- ── Step 1: show IR module stats ────────────────────────
  IO.println "▸ IR modules"
  let allMods : List Module := [counterModule, wideAccumModule, rv32Module]
  for m in allMods do
    let userPorts := m.inputs.filter fun p => p.name != "clk" && p.name != "rst"
    let regBytes  := m.body.foldl (fun acc s => match s with
      | .register _ _ _ _ _ => acc + 4  | _ => acc) 0
    IO.println s!"  {m.name}: {userPorts.length} user inputs, \
                   {m.body.length} stmts, ~{regBytes} B state/instance"
  IO.println ""

  -- ── Step 2: compile shared libraries ────────────────────
  let cudaEnabled := (← IO.getEnv "SPARKLE_CUDA") == some "1"
  let cudaStatus  := if cudaEnabled then "enabled" else "disabled (set SPARKLE_CUDA=1)"
  IO.println s!"▸ Compiling shared libraries (CUDA {cudaStatus})..."
  let soOf (m : Module) : String × String :=
    let name := sanitizeName m.name
    let dir  := s!"/tmp/sparkle_jit_bench_{name}"
    (s!"{dir}/lib{name}_cpp.so", s!"{dir}/lib{name}_cuda.so")
  for m in allMods do
    let (_, ns) ← timed (compileMod m)
    IO.println s!"  {m.name}: g++ done in {fmtTime ns}"
  IO.println ""

  let (cntCppSo,  cntCudaSo)  := soOf counterModule
  let (wideCppSo, wideCudaSo) := soOf wideAccumModule
  let (rv32CppSo, rv32CudaSo) := soOf rv32Module

  -- ── Step 3: warm-up ──────────────────────────────────────
  IO.println "▸ Warming up (1 discarded run each)..."
  let _ ← runPoint "warmup" 1_000 100 cntCppSo  cntCudaSo
  let _ ← runPoint "warmup" 1_000 100 wideCppSo wideCudaSo
  let _ ← runPoint "warmup" 10    10  rv32CppSo rv32CudaSo
  IO.println "  done."
  IO.println ""

  IO.println "▸ Running benchmarks..."
  IO.println ""

  -- ── Counter (4 B/instance) ───────────────────────────────
  IO.println "  [ Counter — 8-bit, 2 stmts/tick, 4 B/instance ]"
  printHeader
  for (n, t) in [(1, 1_000), (1_000, 1_000), (100_000, 1_000),
                  (1_000_000, 1_000), (1_000_000, 10_000)] do
    printRow (← runPoint s!"cnt N={n}" n t cntCppSo cntCudaSo)
  printFooter
  IO.println ""

  -- ── WideAccum (64 B/instance) ────────────────────────────
  IO.println "  [ WideAccum — 16×32-bit cascade, 16 stmts/tick, ~64 B/instance ]"
  printHeader
  for (n, t) in [(1, 1_000), (1_000, 1_000), (10_000, 1_000),
                  (100_000, 1_000), (500_000, 1_000)] do
    printRow (← runPoint s!"wide N={n}" n t wideCppSo wideCudaSo)
  printFooter
  IO.println ""

  -- ── RV32Core (4-stage RISC-V pipeline, ~200 B/instance) ──
  -- CppSim is ~700× slower per tick than Counter; keep N×T small.
  IO.println "  [ RV32Core — 4-stage RISC-V, 1436 stmts/tick, ~200 B/instance ]"
  IO.println "    (synthesized from IP.RV32.Pipeline via #synthesizeModule)"
  printHeader
  for (n, t) in [(1, 100), (100, 100), (1_000, 100),
                  (10_000, 100), (50_000, 100)] do
    printRow (← runPoint s!"rv32 N={n}" n t rv32CppSo rv32CudaSo)
  printFooter
  IO.println ""

  -- ── Cross-circuit summary at a common point ───────────────
  IO.println "  [ Cross-circuit: N=10,000 × T=100 cycles ]"
  printHeader
  printRow (← runPoint "Counter  (10k×100)"  10_000 100 cntCppSo  cntCudaSo)
  printRow (← runPoint "WideAccum (10k×100)" 10_000 100 wideCppSo wideCudaSo)
  printRow (← runPoint "RV32Core  (10k×100)" 10_000 100 rv32CppSo rv32CudaSo)
  printFooter
  IO.println ""

  IO.println "  Column glossary:"
  IO.println "    CppSim t    wall-clock for N*T sequential ticks (1 thread)"
  IO.println "    CUDA t      wall-clock for N*T parallel ticks on GPU"
  IO.println "                (H->D copy + kernel launch + D->H sync)"
  IO.println "    Speedup     CppSim_t / CUDA_t  (>1 = GPU wins)"
  IO.println "    Cpp thrput  (1 * N*T) / CppSim_t"
  IO.println "    CUDA thrput (N * T)   / CUDA_t"
  IO.println ""
  IO.println "  State-size progression (N=10k):"
  IO.println "    Counter   ~400 KB  fits in 6 MB RTX 3080Ti L2"
  IO.println "    WideAccum ~640 KB  fits in L2"
  IO.println "    RV32Core  ~2 MB    spills to GDDR6X"
  IO.println ""
  IO.println "  CUDA_ARCH=compute_86 (RTX 3080Ti)  -O1  PTX-only"
