# How to use JIT compile with CUDA

libraries
```
Sparkle/Backend/CudaSim_addition.lean
Sparkle/Backend/CudaSim
```
## Basic Usage
```lean
let cuCode := Sparkle.Backend.CudaSim.toCudaSim myModule "mymod_sim.h"
IO.FS.writeFile "mymod.cu" cuCode
```

mymod_sim.h and mymod.cu is generated.

```bash
nvcc -O3 -std=c++17 -shared -fPIC -o libmymod.so mymod.cu
```

## More paralellism: CudaDesignStateStruct

Fused per-design GPU state struct

### Basic Usage

1. Write example code
As an example, define a simple CPU Module. 
```lean
import Sparkle
open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- ── RegFile ──────────────────────────────────────────────────────────────────
def regFile {dom : DomainConfig}
    (raddr1 raddr2 waddr : Signal dom (BitVec 5))
    (wdata : Signal dom (BitVec 32))
    (we    : Signal dom Bit)
    : Signal dom (BitVec 32 × BitVec 32) :=
  Signal.circuit do
    let rdata1 ← Signal.memory 5 32 waddr wdata we raddr1 (comboRead := true)
    let rdata2 ← Signal.memory 5 32 waddr wdata we raddr2 (comboRead := true)
    return (rdata1, rdata2)

-- ── ALU ──────────────────────────────────────────────────────────────────────
def alu {dom : DomainConfig}
    (rs1 rs2 : Signal dom (BitVec 32))
    (op      : Signal dom (BitVec 4))
    : Signal dom (BitVec 32) :=
  Signal.circuit do
    let sum ← Signal.pure (rs1 + rs2)
    return hw_cond (op == 0#4) sum (rs1 &&& rs2)

-- ── CPU Top ───────────────────────────────────────────────────────────────────
def cpu {dom : DomainConfig}
    (raddr1 raddr2 : Signal dom (BitVec 5))
    (op            : Signal dom (BitVec 4))
    (waddr         : Signal dom (BitVec 5))
    (wdata         : Signal dom (BitVec 32))
    (we            : Signal dom Bit)
    : Signal dom (BitVec 32) :=
  Signal.circuit do
    let (rs1, rs2) ← regFile raddr1 raddr2 waddr wdata we
    return ← alu rs1 rs2 op
```

Corresponding Module id descripted as following.

```lean
import Sparkle.IR.AST
import Sparkle.Backend.CppSim
import Sparkle.Backend.CudaSim

open Sparkle.IR.AST
open Sparkle.Backend.CudaSim

-- Build a minimal example design: ALU fed by RegFile, both under CPU top
def regfileModule : Module := {
  name      := "RegFile"
  isPrimitive := false
  inputs    := [⟨"clk", .bit⟩, ⟨"raddr1", .bitVector 5⟩,
                ⟨"raddr2", .bitVector 5⟩, ⟨"waddr", .bitVector 5⟩,
                ⟨"wdata", .bitVector 32⟩, ⟨"we", .bit⟩]
  outputs   := [⟨"rdata1", .bitVector 32⟩, ⟨"rdata2", .bitVector 32⟩]
  wires     := []
  body      := [
    .memory "rf" 5 32 (.ref "clk")
      (.ref "waddr") (.ref "wdata") (.ref "we")
      (.ref "raddr1") "rdata1" true,
    .memory "rf2" 5 32 (.ref "clk")
      (.ref "waddr") (.ref "wdata") (.ref "we")
      (.ref "raddr2") "rdata2" true,
  ]
}

def aluModule : Module := {
  name      := "ALU"
  isPrimitive := false
  inputs    := [⟨"clk", .bit⟩, ⟨"rs1", .bitVector 32⟩,
                ⟨"rs2", .bitVector 32⟩, ⟨"op", .bitVector 4⟩]
  outputs   := [⟨"result", .bitVector 32⟩]
  wires     := [⟨"_gen_sum", .bitVector 32⟩]
  body      := [
    .assign "_gen_sum" (.op .add [.ref "rs1", .ref "rs2"]),
    .assign "result"   (.op .mux [
      .op .eq [.ref "op", .const 0 4],
      .ref "_gen_sum",
      .op .and [.ref "rs1", .ref "rs2"]]),
  ]
}

def cpuTop : Module := {
  name      := "CPU"
  isPrimitive := false
  inputs    := [⟨"clk", .bit⟩, ⟨"raddr1", .bitVector 5⟩,
                ⟨"raddr2", .bitVector 5⟩, ⟨"op", .bitVector 4⟩,
                ⟨"waddr", .bitVector 5⟩, ⟨"wdata", .bitVector 32⟩,
                ⟨"we", .bit⟩]
  outputs   := [⟨"result", .bitVector 32⟩]
  wires     := [⟨"rs1_wire", .bitVector 32⟩, ⟨"rs2_wire", .bitVector 32⟩]
  body      := [
    .inst "RegFile" "rf" [
      ("clk",    .ref "clk"),
      ("raddr1", .ref "raddr1"),
      ("raddr2", .ref "raddr2"),
      ("waddr",  .ref "waddr"),
      ("wdata",  .ref "wdata"),
      ("we",     .ref "we"),
      ("rdata1", .ref "rs1_wire"),   -- output: rf.rdata1 → rs1_wire
      ("rdata2", .ref "rs2_wire"),
    ],
    .inst "ALU" "alu" [
      ("clk",    .ref "clk"),
      ("rs1",    .ref "rs1_wire"),   -- input: rs1_wire → alu.rs1
      ("rs2",    .ref "rs2_wire"),
      ("op",     .ref "op"),
      ("result", .ref "result"),     -- output: alu.result → top result
    ],
  ]
}

def cpuDesign : Design := {
  topModule := "CPU"
  modules   := [regfileModule, aluModule, cpuTop]
}

-- ── Call emitCudaDesignStateStruct ────────────────────────────────
def main : IO Unit := do
  let r := emitCudaDesignStateStruct cpuDesign

  -- The struct definition + wire_copy + reset
  IO.println r.structText

  -- The wire edge list (for inspection / further codegen)
  IO.println s!"Wire edges ({r.wireEdges.length} total):"
  for e in r.wireEdges do
    IO.println s!"  {e.srcModule}.{e.srcPort} → {e.dstModule}.{e.dstPort} [{e.width}b]"
```

Expected output of r.structText is following

```c
// Fused design state for 'CPU' — all modules in one allocation
struct CPU_design_state_t {
  // ── top-level ports ──
  uint8_t   clk;   // top-level input
  uint8_t   raddr1; ...
  uint32_t  result; // top-level output

  // ── per-module sub-structs (topological order: leaves first) ──
  // [level 0] RegFile instance: rf
  RegFile_state_t  rf;
  // [level 0] ALU instance: alu
  ALU_state_t      alu;

  // ── inter-module wires ──
  uint32_t  rf__rdata1;
  uint32_t  rf__rdata2;
  uint32_t  alu__result;
};

__device__ __forceinline__ void CPU_wire_copy(CPU_design_state_t* s) {
  s->rs1_wire   = s->rf.rdata1;
  s->rf__rdata1 = s->rf.rdata1;
  s->rs2_wire   = s->rf.rdata2;
  s->rf__rdata2 = s->rf.rdata2;
  s->result     = s->alu.result;
  s->alu__result= s->alu.result;
}

__host__ __device__ __forceinline__
void CPU_design_reset(CPU_design_state_t* s) {
  memset(s, 0, sizeof(CPU_design_state_t));
}
```

3. Generate the complete .cu (struct + per-module device fns + kernel + host API)
```lean
def main : IO Unit := do
  -- Step 1: generate the C++ header (existing backend)
  let cppHeader := Sparkle.Backend.CppSim.toCppSimDesign cpuDesign
  IO.FS.writeFile "cpu_design_sim.h" cppHeader

  -- Step 2: generate the CUDA .cu file
  let cuCode := toCudaSimHetero cpuDesign "cpu_design_sim.h"
  IO.FS.writeFile "cpu_design.cu" cuCode

  IO.println "Generated cpu_design_sim.h and cpu_design.cu"
```

Or `#sim` macro
```lean
#sim cpu_design
```
And retrieve the cached module

```lean
def ModuleFromCache : Sparkle.IR.AST.Module :=
  match Sparkle.Sim.JIT.getLastCompiledModule (← getEnv) with
  | some m => m
  | none   => panic! "sim! has not been run yet"
```


4. Compile and link:
```bash
# Compile the C++ header into a position-independent object (for the .so)
clang++ -O3 -std=c++17 -fPIC -c -o cpu_design_sim.o \
  -x c++ cpu_design_sim.h   # header-only, nothing to compile — skip if pure header

# Compile the CUDA file into a shared library
nvcc -O3 -std=c++17 -shared -fPIC \
  -I. \
  -o libcpu.so cpu_design.cu

# Verify exported symbols
nm -D libcpu.so | grep jit_cuda
#  T jit_cuda_design_alloc
#  T jit_cuda_design_free
#  T jit_cuda_design_set_input
#  T jit_cuda_design_get_output
#  T jit_cuda_design_run
#  T jit_cuda_design_reset
```
5. Lean FFI — driving the compiled .so
```lean
-- Sparkle/Sim/CudaJIT.lean
import Sparkle.Backend.CudaSim

-- FFI declarations matching the extern "C" symbols
@[extern "jit_cuda_design_alloc"]
opaque cudaDesignAlloc (n : UInt32) : IO USize

@[extern "jit_cuda_design_free"]
opaque cudaDesignFree (handle : USize) : IO Unit

@[extern "jit_cuda_design_set_input"]
opaque cudaDesignSetInput (handle : USize) (inst port : UInt32) (val : UInt64) : IO Unit

@[extern "jit_cuda_design_get_output"]
opaque cudaDesignGetOutput (handle : USize) (inst port : UInt32) : IO UInt64

@[extern "jit_cuda_design_run"]
opaque cudaDesignRun (handle : USize) (numCycles : UInt32) : IO Unit

@[extern "jit_cuda_design_reset"]
opaque cudaDesignReset (handle : USize) : IO Unit

-- ── High-level wrapper ────────────────────────────────────────────
structure CudaSimHandle where
  raw      : USize
  nInst    : UInt32

def CudaSimHandle.alloc (n : UInt32) : IO CudaSimHandle := do
  let h ← cudaDesignAlloc n
  return { raw := h, nInst := n }

def CudaSimHandle.free (h : CudaSimHandle) : IO Unit :=
  cudaDesignFree h.raw

def CudaSimHandle.setInput (h : CudaSimHandle)
    (inst port : UInt32) (val : UInt64) : IO Unit :=
  cudaDesignSetInput h.raw inst port val

def CudaSimHandle.getOutput (h : CudaSimHandle)
    (inst port : UInt32) : IO UInt64 :=
  cudaDesignGetOutput h.raw inst port

def CudaSimHandle.run (h : CudaSimHandle) (cycles : UInt32) : IO Unit :=
  cudaDesignRun h.raw cycles

def CudaSimHandle.reset (h : CudaSimHandle) : IO Unit :=
  cudaDesignReset h.raw
```

6. running a batch Simulation
```lean
-- Run 1 million independent test vectors for 100 cycles each
def runBatchFuzz : IO Unit := do
  let N : UInt32 := 1_000_000
  let h ← CudaSimHandle.alloc N

  -- Port indices (must match the order in top.inputs / top.outputs)
  -- CPU top inputs (excl. clk): raddr1=0, raddr2=1, op=2, waddr=3, wdata=4, we=5
  -- CPU top outputs:            result=0
  let portOp     : UInt32 := 2
  let portResult : UInt32 := 0

  -- Initialize: assign random op codes across instances
  for i in List.range N.toNat do
    let op : UInt64 := (i % 16).toUInt64   -- 4-bit op
    h.setInput i.toUInt32 portOp op

  -- Run 100 cycles
  h.run 100

  -- Read back results
  let mut nonZero := 0
  for i in List.range N.toNat do
    let v ← h.getOutput i.toUInt32 portResult
    if v != 0 then nonZero := nonZero + 1

  IO.println s!"Non-zero results: {nonZero} / {N}"
  h.free
```

7. Using wireEdges directly

The DesignStateResult.wireEdges field is useful beyond code generation — for example, to build a static dependency graph for formal analysis or to verify the generated connections:

```lean
def inspectWireGraph (d : Design) : IO Unit := do
  let r := emitCudaDesignStateStruct d

  -- Check for any undriven inputs (dst with no src)
  let driven := r.wireEdges.map fun e => (e.dstModule, e.dstPort)
  let top    := d.modules.find? fun m => m.name == d.topModule
  match top with
  | none => IO.println "top not found"
  | some t =>
    for stmt in t.body do
      match stmt with
      | .inst modName instName connections =>
        let subMod := d.modules.find? fun m => m.name == modName
        let inputs := subMod.map (·.inputs) |>.getD []
        for inp in inputs do
          let iName := sanitizeName instName
          let key   := (iName, sanitizeName inp.name)
          if !driven.contains key then
            IO.println s!"WARNING: {iName}.{inp.name} has no driver"
      | _ => pure ()

  -- Print the DAG as adjacency list
  IO.println "Wire graph:"
  for e in r.wireEdges do
    IO.println s!"  {e.srcModule}.{e.srcPort} --[{e.width}b]--> {e.dstModule}.{e.dstPort}"
```

## Common failure modes and fixes
- Struct padding misalignment. cudaMemcpy copies raw bytes, so if nvcc and your Lean FFI disagree on struct size, state gets corrupted. Add a size-check assertion in the host API:
```cpp
// Add to jit_cuda_design_alloc, after the malloc
static_assert(sizeof(CPU_design_state_t) % 8 == 0,
  "Design state struct must be 8-byte aligned for cudaMemcpy");
```
- Missing __device__ on C++ class methods. The emitCudaDeviceEvalTick wrapper copies state into a local class instance. If the class constructor or reset() calls anything not compiled with __device__, nvcc will fail. Fix: compile the C++ header with -x cu or add a #ifdef __CUDA_ARCH__ guard around any host-only code in the generated header.
- Level-0 modules sharing state. If two level-0 modules both write the same top-level wire (a genuine multi-driver), wire_copy will write it twice — last write wins, which is wrong. The IR should already prevent this via the filteredBody deduplication in emitModule, but it's worth asserting in collectWireEdges that no two edges share (dstModule, dstPort).