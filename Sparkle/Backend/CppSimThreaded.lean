/-
  Threaded C++ Simulation Code Generator

  Generates 2 C++ classes (CPU + Peripheral) from a partitioned Module,
  plus a barrier-sync runner that exchanges boundary signals each cycle.
-/

import Sparkle.Backend.CppSim
import Sparkle.Backend.Partition
import Sparkle.IR.AST

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CppSim
open Sparkle.Backend.Partition

namespace Sparkle.Backend.CppSimThreaded

/-- Generate a 2-thread barrier-sync simulation from a partitioned module.
    Returns C++ source code with:
    - Class for CPU partition
    - Class for Peripheral partition
    - Barrier-sync runner (main loop)
    - JIT FFI exports -/
def toCppSimThreaded (m : Module) : String :=
  let part := partitionModule m
  let cpuClass := emitModule part.cpuModule
  let periClass := emitModule part.periModule
  let cpuName := sanitizeName part.cpuModule.name
  let periName := sanitizeName part.periModule.name

  let includes := "#include <cstdint>\n#include <array>\n#include <cstring>\n#include <atomic>\n#include <thread>\n\n"

  -- Boundary signal struct
  let boundaryStruct :=
    "// Boundary signals exchanged between CPU and Peripheral each cycle\n" ++
    "struct BoundarySignals {\n" ++
    (part.cpuToPeri.map fun p =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    (part.periToCpu.map fun p =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "};\n\n"

  -- Barrier sync runner
  let runner :=
    "// Barrier-sync 2-thread runner\n" ++
    "struct ThreadedSim {\n" ++
    s!"    {cpuName} cpu;\n" ++
    s!"    {periName} peri;\n" ++
    "    std::atomic<int> barrier{0};\n" ++
    "\n" ++
    "    void reset() { cpu.reset(); peri.reset(); }\n" ++
    "\n" ++
    "    void evalTick() {\n" ++
    "        // Phase 1: Both partitions evaluate\n" ++
    "        cpu.eval();\n" ++
    "        peri.eval();\n" ++
    "\n" ++
    "        // Phase 2: Exchange boundary signals\n" ++
    "        // CPU → Peripheral\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      s!"        peri.{sn} = cpu.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "        // Peripheral → CPU\n" ++
    (part.periToCpu.map fun p =>
      let sn := sanitizeName p.name
      s!"        cpu.{sn} = peri.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "\n" ++
    "        // Phase 3: Both partitions tick\n" ++
    "        cpu.tick();\n" ++
    "        peri.tick();\n" ++
    "    }\n" ++
    "};\n\n"

  -- JIT FFI exports (single-threaded interface wrapping the 2-partition sim)
  let ffi :=
    "extern \"C\" {\n" ++
    "void* jit_create() { return new ThreadedSim(); }\n" ++
    "void  jit_destroy(void* ctx) { delete static_cast<ThreadedSim*>(ctx); }\n" ++
    "void  jit_reset(void* ctx) { static_cast<ThreadedSim*>(ctx)->reset(); }\n" ++
    "void  jit_eval(void* ctx) {\n" ++
    "    auto* s = static_cast<ThreadedSim*>(ctx);\n" ++
    "    s->cpu.eval(); s->peri.eval();\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      s!"    s->peri.{sn} = s->cpu.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    (part.periToCpu.map fun p =>
      let sn := sanitizeName p.name
      s!"    s->cpu.{sn} = s->peri.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "}\n" ++
    "void  jit_tick(void* ctx) {\n" ++
    "    auto* s = static_cast<ThreadedSim*>(ctx);\n" ++
    "    s->cpu.tick(); s->peri.tick();\n" ++
    "}\n" ++
    "void  jit_eval_tick(void* ctx) { static_cast<ThreadedSim*>(ctx)->evalTick(); }\n" ++
    "\n" ++
    "// Input/output forwarding to appropriate partition\n" ++
    "void jit_set_input(void* ctx, uint32_t idx, uint64_t val) {\n" ++
    "    auto* s = static_cast<ThreadedSim*>(ctx);\n" ++
    "    // Route to CPU partition (inputs are shared)\n" ++
    "    switch (idx) {\n" ++
    (m.inputs.toArray.toList.zip (List.range m.inputs.length) |>.map fun (p, i) =>
      s!"        case {i}: s->cpu.{sanitizeName p.name} = ({emitCppType p.ty})val;" ++
      s!" s->peri.{sanitizeName p.name} = ({emitCppType p.ty})val; break;"
    ).foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "    }\n" ++
    "}\n" ++
    "\n" ++
    "uint64_t jit_get_output(void* ctx, uint32_t idx) {\n" ++
    "    auto* s = static_cast<ThreadedSim*>(ctx);\n" ++
    "    switch (idx) {\n" ++
    (m.outputs.toArray.toList.zip (List.range m.outputs.length) |>.map fun (p, i) =>
      let sn := sanitizeName p.name
      let src := if classifyWire p.name == .cpu then "cpu" else "peri"
      s!"        case {i}: return (uint64_t)s->{src}.{sn};"
    ).foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "    }\n" ++
    "    return 0;\n" ++
    "}\n" ++
    "\n" ++
    "uint32_t jit_num_inputs()  { return " ++ toString m.inputs.length ++ "; }\n" ++
    "uint32_t jit_num_outputs() { return " ++ toString m.outputs.length ++ "; }\n" ++
    "uint32_t jit_num_wires()   { return 0; }\n" ++
    "uint32_t jit_num_mems()    { return 0; }\n" ++
    "void jit_set_mem(void*, uint32_t, uint32_t, uint32_t) {}\n" ++
    "uint32_t jit_get_mem(void*, uint32_t, uint32_t) { return 0; }\n" ++
    "uint64_t jit_get_wire(void*, uint32_t) { return 0; }\n" ++
    "const char* jit_wire_name(uint32_t) { return \"\"; }\n" ++
    "uint32_t jit_num_regs() { return 0; }\n" ++
    "void jit_set_reg(void*, uint32_t, uint64_t) {}\n" ++
    "uint64_t jit_get_reg(void*, uint32_t) { return 0; }\n" ++
    "void jit_memset_word(void*, uint32_t, uint32_t, uint32_t, uint32_t) {}\n" ++
    "void* jit_snapshot(void*) { return nullptr; }\n" ++
    "void jit_restore(void*, void*) {}\n" ++
    "void jit_free_snapshot(void*, void*) {}\n" ++
    "}\n"

  includes ++ cpuClass ++ "\n" ++ periClass ++ "\n" ++ boundaryStruct ++ runner ++ ffi

end Sparkle.Backend.CppSimThreaded
