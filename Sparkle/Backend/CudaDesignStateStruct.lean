/-
  emitCudaDesignStateStruct — fused per-design GPU state struct
  =============================================================
  Adds to namespace Sparkle.Backend.CudaSim in CudaSim.lean.

  A "design state struct" flattens the entire module hierarchy into one
  contiguous C struct so a single cudaMalloc covers N independent simulation
  instances.  Within one instance the layout is:

    struct <TopName>_design_state_t {
      // ── wires shared between modules (inter-module ports) ──
      <type>  <modName>__<portName>;   // namespaced to avoid collisions

      // ── per-module sub-structs ──
      <ModA>_state_t  modA;
      <ModB>_state_t  modB;
      ...
    };

  All memory arrays are excluded (they stay on the host).
  Wide registers (> 64 bit) are excluded from device state (v1 limitation).

  The function also returns a WireMap: List (srcMod, srcPort, dstMod, dstPort)
  used by emitCudaWireCopyKernel to generate inter-module connection code.
-/

namespace Sparkle.Backend.CudaSim

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CppSim

-- ─────────────────────────────────────────────────────────────────
-- Helper types
-- ─────────────────────────────────────────────────────────────────

/-- One directed wire connection between two module ports in the design. -/
structure WireEdge where
  srcModule : String   -- sanitized module instance name
  srcPort   : String   -- sanitized port name (output side)
  dstModule : String   -- sanitized module instance name
  dstPort   : String   -- sanitized port name (input side)
  width     : Nat      -- bit-width (for type emission)
  deriving Repr

/-- Result of emitCudaDesignStateStruct: the C struct text + the wire edge list. -/
structure DesignStateResult where
  structText : String
  wireEdges  : List WireEdge

-- ─────────────────────────────────────────────────────────────────
-- Step 1: extract inter-module connections from the top module's body
-- ─────────────────────────────────────────────────────────────────

/-- Walk the top module's `.inst` statements and collect every port connection
    that crosses a module boundary.

    Each `.inst` statement looks like:
      .inst "SubModName" "instName" [("portA", expr), ("portB", expr), ...]

    We classify each connection as input (host→sub) or output (sub→host) by
    comparing against the sub-module's declared output port list.  Output
    connections have the form (.ref wireName) on the RHS — the wire that
    carries the sub-module's output into the top module's wire namespace.

    Returns a flat list of WireEdge records. -/
def collectWireEdges (d : Design) (top : Module) : List WireEdge :=
  let topTypeMap := buildTypeMap top
  top.body.foldl (fun acc stmt =>
    match stmt with
    | .inst modName instName connections =>
      let iName    := sanitizeName instName
      let rawIName := sanitizeName modName
      -- Use the same name-collision rule as emitStmt
      let iName := if iName == rawIName then iName ++ "_inst" else iName

      -- Look up the sub-module to find its output ports
      let subMod := d.modules.find? fun m => m.name == modName
      let outputPorts : List String := match subMod with
        | some sm => sm.outputs.map fun p => p.name
        | none    => []

      let edges := connections.filterMap fun (portName, expr) =>
        let sPort := sanitizeName portName
        let w     := match subMod with
          | some sm =>
            let allPorts := sm.inputs ++ sm.outputs
            match allPorts.find? fun p => p.name == portName with
            | some p => p.ty.bitWidth
            | none   => lookupWidth topTypeMap portName
          | none => lookupWidth topTypeMap portName

        if outputPorts.contains portName then
          -- sub → top: edge from sub-module output to top-level wire
          match expr with
          | .ref wireName =>
            some {
              srcModule := iName
              srcPort   := sPort
              dstModule := sanitizeName top.name
              dstPort   := sanitizeName wireName
              width     := w
            }
          | _ => none
        else
          -- top → sub: edge from top-level wire/expr to sub-module input
          match expr with
          | .ref wireName =>
            some {
              srcModule := sanitizeName top.name
              srcPort   := sanitizeName wireName
              dstModule := iName
              dstPort   := sPort
              width     := w
            }
          | _ => none  -- constant/complex expr: handled inline, no wire edge

      acc ++ edges
    | _ => acc
  ) []

-- ─────────────────────────────────────────────────────────────────
-- Step 2: topological level assignment
-- ─────────────────────────────────────────────────────────────────

/-- Assign a topological level (0 = leaf) to each module by walking the
    instantiation tree bottom-up.  Returns a list of (moduleName, level). -/
def topoLevels (d : Design) : List (String × Nat) :=
  -- getInstModules defined in CppSim.toCppSimDesign; replicate here
  let getDeps (m : Module) : List String :=
    m.body.filterMap fun s => match s with
      | .inst modName _ _ => some modName | _ => none

  -- BFS from leaves
  let moduleMap : List (String × Module) :=
    d.modules.map fun m => (m.name, m)

  let rec computeLevel (name : String) (visited : List String) : Nat :=
    if visited.contains name then 0  -- cycle guard
    else
      match moduleMap.find? fun (n, _) => n == name with
      | none       => 0
      | some (_, m) =>
        let deps := getDeps m
        if deps.isEmpty then 0
        else
          let childLevels := deps.map fun dep =>
            computeLevel dep (name :: visited)
          (childLevels.foldl Nat.max 0) + 1

  d.modules.map fun m => (m.name, computeLevel m.name [])

-- ─────────────────────────────────────────────────────────────────
-- Step 3: per-module sub-struct emission
-- ─────────────────────────────────────────────────────────────────

/-- Emit a single module's contribution to the fused design state.
    This is `emitCudaStateStruct` but qualified with the instance name prefix
    so multiple instances of the same module type don't collide.

    Output example (instName = "alu", module = "ALU"):
      // [level 1] ALU instance: alu
      ALU_state_t  alu;
-/
def emitModuleSubStructField (m : Module) (instName : String) (level : Nat) : String :=
  let className := sanitizeName m.name
  s!"  // [level {level}] {m.name} instance: {instName}\n" ++
  s!"  {className}_state_t  {instName};\n"

-- ─────────────────────────────────────────────────────────────────
-- Step 4: shared inter-module wire fields
-- ─────────────────────────────────────────────────────────────────

/-- Emit struct fields for wires that carry values between modules.
    These are the intermediate values that must be visible to the wire-copy
    kernel between topo levels.  They are namespaced as:
      <srcModule>__<portName>
    to guarantee uniqueness across the flat struct. -/
def emitInterModuleWireFields (edges : List WireEdge) : String :=
  -- Deduplicate by (srcModule, srcPort)
  let seen : List (String × String) := []
  let (fields, _) := edges.foldl (fun (acc, seen) edge =>
    let key := (edge.srcModule, edge.srcPort)
    if seen.contains key then (acc, seen)
    else
      let w       := edge.width
      let ctype   := emitCudaType (.bitVector (min w 64))  -- clamp to 64 per v1
      let field   := s!"  {ctype}  {edge.srcModule}__{edge.srcPort};"
      (acc ++ [field], seen ++ [key])
  ) ([], seen)
  if fields.isEmpty then ""
  else
    "  // ── inter-module wires ──\n" ++
    String.intercalate "\n" fields ++ "\n"

-- ─────────────────────────────────────────────────────────────────
-- Step 5: fused design state struct + wire-copy helpers
-- ─────────────────────────────────────────────────────────────────

/-- Emit the complete fused design state struct together with a
    __device__ wire_copy function that propagates inter-module signals
    between topo levels.

    The struct layout (for a design "cpu" with submodules alu, regfile, ctrl):

      struct cpu_design_state_t {
        // ── per-module sub-structs (topo order: leaves first) ──
        regfile_state_t  regfile;   // level 0
        alu_state_t      alu;       // level 0
        ctrl_state_t     ctrl;      // level 1

        // ── inter-module wires ──
        uint32_t  alu__result;
        uint32_t  regfile__rdata1;
        uint32_t  regfile__rdata2;
        // ...
      };

    Wire-copy helper (called between topo levels in the batch kernel):

      __device__ __forceinline__
      void cpu_wire_copy(cpu_design_state_t* s) {
        // alu outputs → ctrl inputs
        s->ctrl.alu_result  = s->alu.result;
        s->alu__result      = s->alu.result;   // cache in shared wire field
        // regfile outputs → alu inputs
        s->alu.rs1_data     = s->regfile.rdata1;
        // ...
      }
-/
def emitCudaDesignStateStruct (d : Design) : DesignStateResult :=
  -- Find the top module
  let topOpt := d.modules.find? fun m => m.name == d.topModule
  match topOpt with
  | none =>
    { structText := s!"// ERROR: top module '{d.topModule}' not found\n"
    , wireEdges  := [] }
  | some top =>

  let topName    := sanitizeName d.topModule
  let structName := topName ++ "_design_state_t"

  -- Compute topo levels for all modules
  let levels := topoLevels d

  -- Collect sub-module instances from top module's body
  -- Each .inst gives us (moduleName, instanceName)
  let instances : List (String × String × Nat) :=   -- (modName, instName, level)
    top.body.filterMap fun stmt => match stmt with
      | .inst modName instName _ =>
        let rawIName := sanitizeName instName
        let className := sanitizeName modName
        let iName := if rawIName == className then rawIName ++ "_inst" else rawIName
        let level := (levels.find? fun (n, _) => n == modName).map (·.2) |>.getD 0
        some (modName, iName, level)
      | _ => none

  -- Sort instances by topo level (leaves first)
  let sortedInstances := instances.mergeSort (fun (_, _, la) (_, _, lb) => la ≤ lb)

  -- Collect wire edges
  let edges := collectWireEdges d top

  -- ── Emit the struct ──────────────────────────────────────────
  let topInputFields := top.inputs.map fun p =>
    s!"  {emitCudaType p.ty} {sanitizeName p.name};   // top-level input"
  let topOutputFields := top.outputs.map fun p =>
    s!"  {emitCudaType p.ty} {sanitizeName p.name};   // top-level output"

  let subStructFields := sortedInstances.map fun (modName, iName, level) =>
    match d.modules.find? fun m => m.name == modName with
    | none   => s!"  // WARNING: module '{modName}' not found\n"
    | some m => emitModuleSubStructField m iName level

  let wireFields := emitInterModuleWireFields edges

  let structBody :=
    "  // ── top-level ports ──\n" ++
    String.intercalate "\n" topInputFields ++ "\n" ++
    String.intercalate "\n" topOutputFields ++ "\n\n" ++
    "  // ── per-module sub-structs (topological order: leaves first) ──\n" ++
    String.intercalate "" subStructFields ++
    "\n" ++ wireFields

  let structText :=
    s!"// Fused design state for '{d.topModule}' — all modules in one allocation\n" ++
    s!"// Generated by Sparkle HDL CUDA backend\n" ++
    s!"struct {structName} {{\n" ++
    structBody ++
    "};\n"

  -- ── Emit wire_copy device function ──────────────────────────
  -- For each edge: s->dstModule.dstPort = s->srcModule.srcPort;
  -- Also update the shared wire cache field.
  let wireCopyLines := edges.map fun e =>
    -- sub→top connection: update top-level wire and inter-module cache
    if e.dstModule == topName then
      s!"  s->{e.dstPort} = s->{e.srcModule}.{e.srcPort};   // {e.srcModule} → top"
    -- top→sub connection: propagate top-level input/wire to sub-module
    else if e.srcModule == topName then
      s!"  s->{e.dstModule}.{e.dstPort} = s->{e.srcPort};   // top → {e.dstModule}"
    -- sub→sub connection through shared wire cache
    else
      s!"  s->{e.srcModule}__{e.srcPort} = s->{e.srcModule}.{e.srcPort};\n" ++
      s!"  s->{e.dstModule}.{e.dstPort} = s->{e.srcModule}__{e.srcPort};"

  let wireCopyFn :=
    s!"{devQual} void {topName}_wire_copy({structName}* s) {{\n" ++
    (if wireCopyLines.isEmpty then "  // no inter-module wires\n"
     else String.intercalate "\n" wireCopyLines ++ "\n") ++
    "}\n"

  -- ── Emit reset function ──────────────────────────────────────
  -- Zero-initializes the struct (correct for all-zero register reset)
  let resetFn :=
    s!"{hostDev} void {topName}_design_reset({structName}* s) {{\n" ++
    s!"  memset(s, 0, sizeof({structName}));\n" ++
    "}\n"

  let fullText :=
    structText ++ "\n" ++
    wireCopyFn ++ "\n" ++
    resetFn    ++ "\n"

  { structText := fullText
  , wireEdges  := edges }

-- ─────────────────────────────────────────────────────────────────
-- Step 6: fused batch kernel using the design state struct
-- ─────────────────────────────────────────────────────────────────

/-- Emit the fused __global__ batch kernel.

    Each thread handles one design instance and runs numCycles cycles.
    Within each cycle:
      1. copy top-level inputs into sub-module inputs  (top→sub edges)
      2. for each topo level: run evalTick for all modules at that level
      3. copy outputs between levels                   (sub→sub, sub→top edges)

    The inter-level wire copy is done by the generated wire_copy() helper.
    Because threads are independent (no shared state between instances),
    this is embarrassingly parallel — no __syncthreads() needed.
-/
def emitCudaFusedBatchKernel (d : Design) : String :=
  let topOpt := d.modules.find? fun m => m.name == d.topModule
  match topOpt with
  | none => s!"// ERROR: top module '{d.topModule}' not found\n"
  | some top =>

  let topName    := sanitizeName d.topModule
  let structName := topName ++ "_design_state_t"

  -- Collect instances grouped by topo level
  let levels     := topoLevels d
  let instances  : List (String × String × Nat) :=
    top.body.filterMap fun stmt => match stmt with
      | .inst modName instName _ =>
        let rawIName  := sanitizeName instName
        let className := sanitizeName modName
        let iName := if rawIName == className then rawIName ++ "_inst" else rawIName
        let level := (levels.find? fun (n, _) => n == modName).map (·.2) |>.getD 0
        some (modName, iName, level)
      | _ => none

  let maxLevel := instances.foldl (fun acc (_, _, l) => Nat.max acc l) 0

  -- Group by level
  let levelGroups : List (Nat × List (String × String)) :=
    (List.range (maxLevel + 1)).map fun lvl =>
      (lvl, instances.filterMap fun (modName, iName, l) =>
        if l == lvl then some (modName, iName) else none)

  -- Body lines: for each level, run evalTick for all modules, then wire_copy
  let bodyLines : List String :=
    levelGroups.foldl (fun acc (lvl, mods) =>
      let calls := mods.map fun (_, iName) =>
        -- Use the per-module device evalTick (generated by emitCudaDeviceEvalTick)
        let modName := instances.findSome? fun (mn, iN, _) =>
          if iN == iName then some mn else none
        let className := sanitizeName (modName.getD iName)
        s!"    {className}_cuda_evalTick(&s->{iName});"
      let syncLine :=
        s!"    // level {lvl} → level {lvl+1}: propagate wires"
      acc ++ calls ++ [syncLine, s!"    {topName}_wire_copy(s);"]
    ) []

  -- Top-level input propagation (before first level)
  let topInputLines :=
    ["    // propagate top-level inputs into sub-modules",
     s!"    {topName}_wire_copy(s);"]

  let kernelLines := [
    s!"{globalQ} void {topName}_fused_batch_kernel(",
    s!"    {structName}* states,",
     "    unsigned int N,",
     "    unsigned int numCycles,",
     "    const void* /* input_overrides — future use */) {",
     "  const unsigned int tid = blockIdx.x * blockDim.x + threadIdx.x;",
     "  if (tid >= N) return;",
    s!"  {structName}* s = states + tid;",
     "  for (unsigned int cyc = 0; cyc < numCycles; ++cyc) {",
  ] ++
  topInputLines ++
  bodyLines ++
  [
     "  }  // end cycle loop",
     "}",
     "",
  ]
  String.intercalate "\n" kernelLines

-- ─────────────────────────────────────────────────────────────────
-- Step 7: updated host JIT API for the fused design
-- ─────────────────────────────────────────────────────────────────

/-- Emit the full extern "C" host API for the fused design.
    Replaces the per-module API emitted by emitCudaJITHostAPI. -/
def emitCudaDesignJITHostAPI (d : Design) : String :=
  let topOpt := d.modules.find? fun m => m.name == d.topModule
  match topOpt with
  | none => s!"// ERROR: top module '{d.topModule}' not found\n"
  | some top =>

  let topName    := sanitizeName d.topModule
  let structName := topName ++ "_design_state_t"

  let userInputs := top.inputs.filter fun p => p.name != "clk"
  let setInputCases := (userInputs.zip (List.range userInputs.length)).map
    fun (p, i) =>
      let sn := sanitizeName p.name
      let ct := emitCppType p.ty
      s!"    case {i}: h->staging->{sn} = ({ct})val; break;"

  let getOutputCases := top.outputs.foldl (fun (acc : List String × Nat) p =>
    let sn := sanitizeName p.name
    (acc.1 ++ [s!"    case {acc.2}: return (uint64_t)h->staging->{sn};"], acc.2 + 1)
  ) ([], 0)

  String.intercalate "\n" ([
    "// ── Fused design CUDA JIT host API ─────────────────────────────",
    "#include <cuda_runtime.h>",
    "#include <cassert>",
    "#include <cstring>",
    "",
    "struct DesignCudaHandle {",
    s!"  {structName}*  d_states;",
    s!"  {structName}*  staging;   // pinned host memory",
    "  unsigned int   N;",
    "};",
    "",
    "extern \"C\" {",
    "",
    "void* jit_cuda_design_alloc(unsigned int N) {",
    "  auto* h = new DesignCudaHandle;",
    "  h->N = N;",
    s!"  cudaMalloc(&h->d_states, N * sizeof({structName}));",
    s!"  cudaMallocHost(&h->staging, N * sizeof({structName}));",
    s!"  memset(h->staging, 0, N * sizeof({structName}));",
    s!"  cudaMemcpy(h->d_states, h->staging, N * sizeof({structName}), cudaMemcpyHostToDevice);",
    "  return h;",
    "}",
    "",
    "void jit_cuda_design_free(void* handle) {",
    "  auto* h = (DesignCudaHandle*)handle;",
    "  cudaFree(h->d_states);",
    "  cudaFreeHost(h->staging);",
    "  delete h;",
    "}",
    "",
    "void jit_cuda_design_set_input(void* handle, unsigned int inst, int port, uint64_t val) {",
    "  auto* h = (DesignCudaHandle*)handle;",
    "  if (inst >= h->N) return;",
    s!"  {structName}* s = h->staging + inst;",
    "  switch (port) {",
  ] ++
  setInputCases ++
  [
    "  }",
    "}",
    "",
    "uint64_t jit_cuda_design_get_output(void* handle, unsigned int inst, int port) {",
    "  auto* h = (DesignCudaHandle*)handle;",
    "  if (inst >= h->N) return 0ULL;",
    s!"  {structName}* s = h->staging + inst;",
    "  switch (port) {",
  ] ++
  getOutputCases.1 ++
  [
    "  }",
    "  return 0ULL;",
    "}",
    "",
    "void jit_cuda_design_run(void* handle, unsigned int numCycles) {",
    "  auto* h = (DesignCudaHandle*)handle;",
    s!"  cudaMemcpy(h->d_states, h->staging, h->N * sizeof({structName}), cudaMemcpyHostToDevice);",
    "  const unsigned int blockSize = 256;",
    "  const unsigned int gridSize  = (h->N + blockSize - 1) / blockSize;",
    s!"  {topName}_fused_batch_kernel<<<gridSize, blockSize>>>(h->d_states, h->N, numCycles, nullptr);",
    "  cudaDeviceSynchronize();",
    s!"  cudaMemcpy(h->staging, h->d_states, h->N * sizeof({structName}), cudaMemcpyDeviceToHost);",
    "}",
    "",
    "void jit_cuda_design_reset(void* handle) {",
    "  auto* h = (DesignCudaHandle*)handle;",
    s!"  for (unsigned i = 0; i < h->N; ++i) {topName}_design_reset(h->staging + i);",
    s!"  cudaMemcpy(h->d_states, h->staging, h->N * sizeof({structName}), cudaMemcpyHostToDevice);",
    "}",
    "",
    "} // extern \"C\"",
  ])

-- ─────────────────────────────────────────────────────────────────
-- Step 8: top-level entry point
-- ─────────────────────────────────────────────────────────────────

/-- Generate a complete .cu file for a full heterogeneous Design.

    Compile with:
      nvcc -O3 -std=c++17 -shared -fPIC \
           -I<sparkle_include_dir> \
           -o libdesign.so <topName>_design.cu
-/
def toCudaSimHetero (d : Design) (cppHeaderName : String := "") : String :=
  let topName    := sanitizeName d.topModule
  let headerName :=
    if cppHeaderName.isEmpty then topName ++ "_design_sim.h" else cppHeaderName

  let preamble := String.intercalate "\n" [
    "// AUTO-GENERATED by Sparkle HDL — CUDA Heterogeneous Design Backend",
    s!"// Top module: {d.topModule}",
    "//",
    "// Compile with:",
    s!"//   nvcc -O3 -std=c++17 -shared -fPIC -o lib{topName}.so {topName}_design.cu",
    "",
    "#include <cstdint>",
    "#include <array>",
    "#include <cstring>",
    "#include <cuda_runtime.h>",
    s!"#include \"{headerName}\"   // generated by toCppSimDesign",
    "",
  ]

  let stateResult := emitCudaDesignStateStruct d

  preamble ++
  "// ── Fused design state ───────────────────────────────────────────\n" ++
  stateResult.structText ++ "\n" ++
  "// ── Per-module device evalTick stubs ────────────────────────────\n" ++
  (d.modules.map fun m =>
    if m.isPrimitive then ""
    else emitCudaDeviceEvalTick m
  |> String.intercalate "\n") ++ "\n" ++
  "// ── Fused batch kernel ───────────────────────────────────────────\n" ++
  emitCudaFusedBatchKernel d ++ "\n" ++
  "// ── Host JIT API ─────────────────────────────────────────────────\n" ++
  emitCudaDesignJITHostAPI d

end Sparkle.Backend.CudaSim
