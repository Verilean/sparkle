/-
  CUDA within-instance (intra) scheduling — one GPU thread per top-level
  instance.  Design: docs/CudaIntraSim-design.md.

  `toCudaSimDesign` (batch) runs N independent copies of a design, one thread
  each.  This backend makes ONE instance faster: each top-level `.inst` (a PE,
  a core) becomes a thread, and each simulated clock cycle runs as three
  barrier-separated phases:

    Phase A  eval every instance        — freshens Moore output fields from
                                          current register state;
    Phase B  connection-table copies    — consumer.input ← producer.output,
                                          top inputs, constants; top output
                                          ports refreshed for observation;
    Phase C  eval_tick every instance   — re-evals with FRESH inputs
                                          (correct next-state), latches.

  Soundness rests on CSim's eval being register-pure (registers latch in tick
  only; memory writes live in tickBody; sync-read address latches are
  last-write-wins), so Phase A's stale-input next-state results are dead
  values overwritten by Phase C.  For Moore-bounded designs — every
  cross-instance connection taps an output with no combinational input
  dependence — the schedule is cycle-exact against CSim's sequential
  reference; the argument is in the design memo §3.

  Scaling is table-driven, not switch-driven: instance offsets, module-kind
  dispatch, and `offsetof`-pair copy descriptors, so a 16K-instance top emits
  kilobytes of tables instead of a 16K-case kernel.

  v1 restrictions (all detected; each error names the offender):
    - Moore-bounded cross-instance connections only (v2: K-round relaxation,
      memo §7);
    - connections are `.ref` (chased through const/ref top assigns) or
      `.const`;
    - the top module contains only `.assign` + `.inst` (no registers,
      memories, or combinational logic at top);
    - no combinational loops.
-/
import Sparkle.Backend.CudaSim

namespace Sparkle.Backend.CudaIntra

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CSim
open Sparkle.Backend.CudaSim

/-! ### Combinational-dependency analysis (per module) -/

private structure NetMaps where
  inputNames : List String
  assigns    : List (String × Expr)
  regOuts    : List String
  memReads   : List (String × Bool × Expr)  -- (readData, comboRead, readAddr)

private def netMapsOf (m : Module) : NetMaps :=
  { inputNames := m.inputs.map (·.name)
  , assigns := m.body.filterMap fun s => match s with
      | .assign lhs rhs => some (lhs, rhs)
      | _ => none
  , regOuts := m.body.filterMap fun s => match s with
      | .register out .. => some out
      | _ => none
  , memReads := m.body.filterMap fun s => match s with
      | .memory _ _ _ _ _ _ _ ra rd cr => some (rd, cr, ra)
      | _ => none }

/-- Walk backwards from `name` through assign chains, collecting the input
    ports it combinationally depends on.  Stops at registers and sync-read
    memories; comboRead memories propagate through their read address. -/
private def combWalk (nm : NetMaps) : Nat → List String → String →
    Except String (List String)
  | 0, path, name =>
    throw s!"combinational chain too deep at '{name}' (suspected loop; path: {String.intercalate " -> " path.reverse})"
  | fuel + 1, path, name => do
    if path.contains name then
      throw s!"combinational loop through '{name}'"
    else if nm.inputNames.contains name then
      return [name]
    else if nm.regOuts.contains name then
      return []
    else
      match nm.memReads.find? (fun e => e.1 == name) with
      | some (_, cr, ra) =>
        if cr then
          (collectExprRefs ra).foldlM (fun acc r => do
            return acc ++ (← combWalk nm fuel (name :: path) r)) []
        else
          return []
      | none =>
        match nm.assigns.find? (fun e => e.1 == name) with
        | some (_, rhs) =>
          (collectExprRefs rhs).foldlM (fun acc r => do
            return acc ++ (← combWalk nm fuel (name :: path) r)) []
        | none => return []   -- undriven: constant-like, no comb dependence

/-- Input ports that output `port` of `m` combinationally depends on.
    `[]` means a Moore output (function of registers/constants only). -/
def combDeps (m : Module) (port : String) : Except String (List String) := do
  let deps ← combWalk (netMapsOf m) (4 * m.body.length + 16) [] port
  return deps.eraseDups

/-! ### Top-level structure -/

/-- One top-level `.inst`, with its resolved module and the fused-struct
    field name CSim gives it (must match `CSim.emitStmt`'s `.inst` naming). -/
structure InstInfo where
  modName  : String
  instName : String
  /-- Sanitised field name inside the top struct. -/
  field    : String
  mod      : Module
  conns    : List (String × Expr)

private def instFieldName (modName instName : String) : String :=
  let c := sanitizeName modName
  let r := sanitizeName instName
  if r == c then r ++ "_inst" else r

/-- Collect the top's instances; reject anything else the v1 top may not
    contain (registers, memories). -/
private def topInsts (d : Design) (top : Module) : Except String (List InstInfo) :=
  top.body.foldlM (fun acc s => do
    match s with
    | .inst modName instName conns =>
      match d.findModule modName with
      | some m =>
        return acc ++ [{ modName, instName, conns, mod := m
                       , field := instFieldName modName instName }]
      | none => throw s!"instance '{instName}': module '{modName}' not found in design"
    | .register out .. =>
      throw s!"top-level register '{out}' — v1 requires the top to contain only assigns and instances; move it into a submodule"
    | .memory nm .. =>
      throw s!"top-level memory '{nm}' — v1 requires the top to contain only assigns and instances; move it into a submodule"
    | .assign _ _ => return acc) []

/-- Wire name → the (instance, output port) that drives it, from `.inst`
    output connections of the `.ref wire` shape (the only shape CSim's own
    lowering honours for outputs). -/
private def outputDrivers (insts : List InstInfo) : List (String × InstInfo × String) :=
  insts.flatMap fun ii =>
    let outs := ii.mod.outputs.map (·.name)
    ii.conns.filterMap fun (port, e) =>
      if outs.contains port then
        match e with
        | .ref w => some (w, ii, port)
        | _ => none
      else none

/-- Where a connection's value comes from, after chasing top-level
    const/ref assign chains. -/
inductive ConnSource where
  | instOutput (producer : InstInfo) (port : String)
  | topInput (port : String)
  | imm (value : Int) (width : Nat)

private def resolveRef (top : Module) (drivers : List (String × InstInfo × String)) :
    Nat → String → Except String ConnSource
  | 0, n => throw s!"reference chain too deep at '{n}' — loop in top-level assigns?"
  | fuel + 1, n =>
    if top.inputs.any (·.name == n) then
      pure (.topInput n)
    else
      match drivers.find? (fun t => t.1 == n) with
      | some (_, ii, port) => pure (.instOutput ii port)
      | none =>
        let drv : Option Expr := top.body.findSome? (fun s => match s with
          | .assign lhs rhs => if lhs == n then some rhs else none
          | _ => none)
        match drv with
        | some (.ref n') => resolveRef top drivers fuel n'
        | some (.const v w) => pure (.imm v w)
        | some _ =>
          throw s!"top-level combinational logic drives '{n}' — v1 supports only const/ref assigns at top; move the logic into a submodule"
        | none => throw s!"'{n}' is undriven at the top level"

private def resolveConn (top : Module) (drivers : List (String × InstInfo × String))
    (fuel : Nat) (e : Expr) : Except String ConnSource :=
  match e with
  | .const v w => pure (.imm v w)
  | .ref n => resolveRef top drivers fuel n
  | _ => throw "instance connection must be a wire/port reference or a constant — got a compound expression (materialise it in a submodule)"

/-! ### Copy / immediate tables -/

structure CopyEnt where
  dstC  : String
  srcC  : String
  bytes : Nat

structure ImmEnt where
  dstC  : String
  bytes : Nat
  value : String

/-- C storage size of a port, matching CSim's field emission
    (uint8/16/32/64 by width; wide → uint32_t words). -/
private def byteSize : HWType → Except String Nat
  | .bit => pure 1
  | .bitVector w =>
    pure <| if w ≤ 8 then 1 else if w ≤ 16 then 2 else if w ≤ 32 then 4
    else if w ≤ 64 then 8 else 4 * ((w + 31) / 32)
  | .bitVectorDim width =>
    throw s!"CudaIntra requires a concrete bit width, found {width}; specialize retained parameters before CUDA lowering"
  | .array n t => return n * (← byteSize t)

private def portTy (ports : List Port) (name : String) : Option HWType :=
  (ports.find? (·.name == name)).map (·.ty)

private def maskedULL (v : Int) (width : Nat) : String :=
  let w := min width 64
  let m : Int := Int.ofNat (2 ^ w)
  let x := ((v % m) + m) % m
  s!"{x.toNat}ULL"

/-- Build the Phase-B copy and immediate tables: instance input connections
    (clk/rst copied uniformly, exactly like CSim's `.inst` lowering) plus the
    top output ports for host observation.  Applies the Moore check to every
    cross-instance source. -/
private def buildTables (top : Module) (insts : List InstInfo) :
    Except String (List CopyEnt × List ImmEnt) := do
  let topC := sanitizeName top.name
  let drivers := outputDrivers insts
  let fuel := 2 * top.body.length + 8
  let mut copies : List CopyEnt := []
  let mut imms : List ImmEnt := []

  let mooreCheck (consumerDesc : String) (prod : InstInfo) (pport : String) :
      Except String Unit := do
    let deps ← combDeps prod.mod pport
    if !deps.isEmpty then
      throw s!"Mealy boundary: {consumerDesc} ← '{prod.instName}.{pport}', but output '{pport}' of module '{prod.modName}' combinationally depends on input(s) {deps} — register the output (v1 requires Moore-bounded cross-instance connections)"

  for ii in insts do
    let modC := sanitizeName ii.modName
    let outNames := ii.mod.outputs.map (·.name)
    for (port, e) in ii.conns do
      if outNames.contains port then
        continue   -- output connections become `drivers` entries
      let some ty := portTy ii.mod.inputs port
        | throw s!"instance '{ii.instName}': '{port}' is not an input of module '{ii.modName}'"
      let nbytes ← byteSize ty
      let dstC := s!"offsetof(struct {topC}, {ii.field}) + offsetof(struct {modC}, {sanitizeName port})"
      match ← resolveConn top drivers fuel e with
      | .instOutput prod pport =>
        mooreCheck s!"'{ii.instName}.{port}'" prod pport
        let some pty := portTy prod.mod.outputs pport
          | throw s!"internal: output '{pport}' not found on '{prod.modName}'"
        let pbytes ← byteSize pty
        if pbytes != nbytes then
          throw s!"width mismatch: '{ii.instName}.{port}' ({nbytes} bytes) ← '{prod.instName}.{pport}' ({pbytes} bytes)"
        copies := copies ++ [⟨dstC,
          s!"offsetof(struct {topC}, {prod.field}) + offsetof(struct {sanitizeName prod.modName}, {sanitizeName pport})",
          nbytes⟩]
      | .topInput tport =>
        let some tty := portTy top.inputs tport
          | throw s!"internal: top input '{tport}' not found"
        let tbytes ← byteSize tty
        if tbytes != nbytes then
          throw s!"width mismatch: '{ii.instName}.{port}' ({nbytes} bytes) ← top input '{tport}' ({tbytes} bytes)"
        copies := copies ++ [⟨dstC, s!"offsetof(struct {topC}, {sanitizeName tport})", nbytes⟩]
      | .imm v w =>
        if nbytes > 8 then
          throw s!"constant into wide (> 64-bit) input '{ii.instName}.{port}' is unsupported in v1"
        imms := imms ++ [⟨dstC, nbytes, maskedULL v w⟩]

  -- Top output ports: refresh for host observation.  An undriven output is
  -- skipped (it stays at its reset value), but resolvable sources get the
  -- same Moore check — observing a Mealy output would read Phase-A garbage.
  for p in top.outputs do
    let nbytes ← byteSize p.ty
    let dstC := s!"offsetof(struct {topC}, {sanitizeName p.name})"
    match resolveRef top drivers fuel p.name with
    | .error _ => pure ()
    | .ok (.instOutput prod pport) =>
      mooreCheck s!"top output '{p.name}'" prod pport
      copies := copies ++ [⟨dstC,
        s!"offsetof(struct {topC}, {prod.field}) + offsetof(struct {sanitizeName prod.modName}, {sanitizeName pport})",
        nbytes⟩]
    | .ok (.topInput tport) =>
      copies := copies ++ [⟨dstC, s!"offsetof(struct {topC}, {sanitizeName tport})", nbytes⟩]
    | .ok (.imm v w) =>
      if nbytes ≤ 8 then
        imms := imms ++ [⟨dstC, nbytes, maskedULL v w⟩]

  return (copies, imms)

/-! ### Emission -/

/-- Tables, kind dispatch, the templated three-phase cycle body, and the two
    kernels (block barrier / cooperative grid barrier). -/
private def emitIntraSection (top : Module) (insts : List InstInfo)
    (copies : List CopyEnt) (imms : List ImmEnt) : Except String String := do
  let topC := sanitizeName top.name
  let m := insts.length
  let kinds : List String := insts.foldl (fun acc ii =>
    if acc.contains ii.modName then acc else acc ++ [ii.modName]) []
  if kinds.length > 255 then
    throw s!"{kinds.length} distinct instance module types (max 255 for the kind table)"
  let kindOf (ii : InstInfo) : Nat := (kinds.findIdx? (· == ii.modName)).getD 0

  let offEntries := insts.map fun ii =>
    s!"  offsetof(struct {topC}, {ii.field}),"
  let kindEntries := insts.map fun ii => s!"  {kindOf ii},"
  let dispatchCases (fn : String) : List String :=
    (List.range kinds.length).map fun k =>
      let mc := sanitizeName kinds[k]!
      s!"  case {k}: sparkle_{mc}_{fn}((struct {mc}*)b); break;"
  let copyEntries :=
    if copies.isEmpty then ["  { 0, 0, 0u },"]
    else copies.map fun c => s!"  \{ {c.dstC}, {c.srcC}, {c.bytes}u },"
  let immEntries :=
    if imms.isEmpty then ["  { 0, 0u, 0ULL },"]
    else imms.map fun i => s!"  \{ {i.dstC}, {i.bytes}u, {i.value} },"

  return String.intercalate "\n" <|
    [ "// ── Intra-instance scheduling: one thread per top-level instance ──"
    , "// Three-phase eval-twice schedule (docs/CudaIntraSim-design.md §3)."
    , "namespace cg = cooperative_groups;"
    , ""
    , s!"enum \{ {topC}_intra_M = {m}, {topC}_intra_nCopies = {copies.length}, {topC}_intra_nImms = {imms.length} };"
    , ""
    , s!"static __device__ const size_t {topC}_intra_off[{m}] = \{" ]
    ++ offEntries ++
    [ "};"
    , s!"static __device__ const unsigned char {topC}_intra_kind[{m}] = \{" ]
    ++ kindEntries ++
    [ "};"
    , ""
    , "typedef struct { size_t dst; size_t src; unsigned bytes; } SparkleIntraCopy;"
    , "typedef struct { size_t dst; unsigned bytes; unsigned long long v; } SparkleIntraImm;"
    , s!"static __device__ const SparkleIntraCopy {topC}_intra_copies[{max copies.length 1}] = \{" ]
    ++ copyEntries ++
    [ "};"
    , s!"static __device__ const SparkleIntraImm {topC}_intra_imms[{max imms.length 1}] = \{" ]
    ++ immEntries ++
    [ "};"
    , ""
    , s!"static __device__ void {topC}_intra_eval(struct {topC}* self, unsigned t) \{"
    , s!"  char* b = (char*)self + {topC}_intra_off[t];"
    , s!"  switch ({topC}_intra_kind[t]) \{" ]
    ++ dispatchCases "eval" ++
    [ "  }"
    , "}"
    , s!"static __device__ void {topC}_intra_eval_tick(struct {topC}* self, unsigned t) \{"
    , s!"  char* b = (char*)self + {topC}_intra_off[t];"
    , s!"  switch ({topC}_intra_kind[t]) \{" ]
    ++ dispatchCases "eval_tick" ++
    [ "  }"
    , "}"
    , ""
    , "template <typename Group>"
    , s!"static __device__ void {topC}_intra_cycles(Group g, struct {topC}* self, long cycles) \{"
    , "  const unsigned t  = g.thread_rank();"
    , "  const unsigned sz = g.num_threads();"
    , "  for (long c = 0; c < cycles; ++c) {"
    , "    // Phase A: freshen Moore outputs from current register state"
    , s!"    if (t < (unsigned){topC}_intra_M) {topC}_intra_eval(self, t);"
    , "    g.sync();"
    , "    // Phase B: connection copies + constant inputs (+ top outputs)"
    , s!"    for (unsigned i = t; i < (unsigned){topC}_intra_nCopies; i += sz) \{"
    , s!"      const SparkleIntraCopy* e = &{topC}_intra_copies[i];"
    , "      memcpy((char*)self + e->dst, (const char*)self + e->src, e->bytes);"
    , "    }"
    , s!"    for (unsigned i = t; i < (unsigned){topC}_intra_nImms; i += sz) \{"
    , s!"      const SparkleIntraImm* e = &{topC}_intra_imms[i];"
    , "      unsigned long long v = e->v;"
    , "      memcpy((char*)self + e->dst, &v, e->bytes);"
    , "    }"
    , "    g.sync();"
    , "    // Phase C: re-eval with fresh inputs, latch registers"
    , s!"    if (t < (unsigned){topC}_intra_M) {topC}_intra_eval_tick(self, t);"
    , "    g.sync();"
    , "  }"
    , "}"
    , ""
    , s!"__global__ void {topC}_intra_block_kernel(struct {topC}* self, long cycles) \{"
    , s!"  {topC}_intra_cycles(cg::this_thread_block(), self, cycles);"
    , "}"
    , s!"__global__ void {topC}_intra_grid_kernel(struct {topC}* self, long cycles) \{"
    , s!"  {topC}_intra_cycles(cg::this_grid(), self, cycles);"
    , "}"
    , "" ]

/-- `jit_intra_run(handle, cycles)`: run instance 0 of a `jit_cuda_alloc`
    handle for `cycles` clock cycles with the intra schedule.  Picks the
    block kernel when the instance count fits one block (cheap barrier;
    ~5×10⁶ cyc/s in the PoC), else a cooperative grid launch (any size;
    barrier-bound ~9×10⁵ cyc/s, PE-throughput linear). -/
private def emitIntraHostRun (top : Module) : String :=
  let topC := sanitizeName top.name
  let st := s!"struct {topC}"
  String.intercalate "\n"
    [ "extern \"C\" {"
    , ""
    , "// Run instance 0 for numCycles with the intra (PE-per-thread) schedule."
    , "// The handle comes from jit_cuda_alloc (N=1 recommended); poke/peek via"
    , "// jit_cuda_set_input / jit_cuda_get_output as usual."
    , "void jit_intra_run(void* handle, long numCycles) {"
    , "  CudaHandle* h = (CudaHandle*)handle;"
    , s!"  {st}* d_top = h->d_states;"
    , s!"  cudaMemcpy(d_top, h->h_staging, sizeof({st}), cudaMemcpyHostToDevice);"
    , s!"  if ({topC}_intra_M <= 1024) \{"
    , s!"    unsigned threads = (((unsigned){topC}_intra_M + 31u) / 32u) * 32u;"
    , s!"    {topC}_intra_block_kernel<<<1, threads>>>(d_top, numCycles);"
    , "  } else {"
    , "    int dev = 0; cudaGetDevice(&dev);"
    , "    int coop = 0; cudaDeviceGetAttribute(&coop, cudaDevAttrCooperativeLaunch, dev);"
    , "    if (!coop) { fprintf(stderr, \"jit_intra_run: cooperative launch unsupported on this device\\n\"); return; }"
    , "    const unsigned blockSize = 256;"
    , s!"    unsigned gridSize = ((unsigned){topC}_intra_M + blockSize - 1) / blockSize;"
    , "    int perSm = 0;"
    , s!"    cudaOccupancyMaxActiveBlocksPerMultiprocessor(&perSm, {topC}_intra_grid_kernel, blockSize, (size_t)0);"
    , "    cudaDeviceProp prop; cudaGetDeviceProperties(&prop, dev);"
    , "    if (gridSize > (unsigned)(perSm * prop.multiProcessorCount)) {"
    , "      fprintf(stderr, \"jit_intra_run: %u blocks exceed co-resident capacity %d\\n\","
    , "              gridSize, perSm * prop.multiProcessorCount);"
    , "      return;"
    , "    }"
    , "    long cyc = numCycles;"
    , "    void* args[] = { (void*)&d_top, (void*)&cyc };"
    , s!"    cudaLaunchCooperativeKernel((void*){topC}_intra_grid_kernel, dim3(gridSize), dim3(blockSize), args, 0, 0);"
    , "  }"
    , "  cudaDeviceSynchronize();"
    , s!"  cudaMemcpy(h->h_staging, d_top, sizeof({st}), cudaMemcpyDeviceToHost);"
    , "}"
    , ""
    , "} // extern \"C\""
    , "" ]

/-- Generate the intra `.cu` for a whole `Design`.  The file contains the
    CSim device code (all modules, host+device qualified), the intra tables +
    kernels, AND the batch kernel + host JIT API — one `.so` serves both
    axes.  Compile with `-rdc=true` (cooperative groups). -/
def toCudaIntraDesign (d : Design) : Except String String := do
  let some top := d.findModule d.topModule
    | throw s!"top module '{d.topModule}' not found in design"
  let insts ← topInsts d top
  if insts.isEmpty then
    throw s!"top module '{top.name}' has no instances — the intra backend parallelises over top-level .inst; use toCudaSim for a flat module"
  let (copies, imms) ← buildTables top insts
  let intra ← emitIntraSection top insts copies imms
  let topC := sanitizeName top.name
  let preamble := String.intercalate "\n"
    [ "// AUTO-GENERATED by Sparkle HDL — CUDA Intra (within-instance) Backend"
    , s!"// Module: {top.name} — {insts.length} top-level instances, one thread each"
    , "//"
    , "// Compile with (relocatable device code is required by grid.sync):"
    , s!"//   nvcc -O3 -std=c++17 -rdc=true -shared -Xcompiler -fPIC -o lib{topC}.so {topC}.cu"
    , ""
    , "#include <cstdint>"
    , "#include <cstring>"
    , "#include <cstddef>"
    , "#include <cstdio>"
    , "#include <cuda_runtime.h>"
    , "#include <cooperative_groups.h>"
    , ""
    , "// ── CSim device code (struct + __host__ __device__ module functions) ─" ]
  return String.intercalate "\n"
    [ preamble
    , emitCudaDeviceCodeD d
    , intra
    , "// ── Batch kernel ─────────────────────────────────────────────────"
    , emitCudaBatchKernel top
    , emitCudaJITHostAPI top
    , emitIntraHostRun top ]

/-- Like `toCudaIntraDesign`, but renders an analysis error as a `#error`
    line so a build-time generation failure is loud at nvcc time. -/
def toCudaIntraDesign! (d : Design) : String :=
  match toCudaIntraDesign d with
  | .ok s => s
  | .error e => s!"#error \"Sparkle CudaIntra: {e.replace "\"" "'"}\"\n"

end Sparkle.Backend.CudaIntra
