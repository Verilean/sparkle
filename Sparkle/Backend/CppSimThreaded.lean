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

  -- 2-thread worker runner with spinlock barrier
  let runner :=
    "// 2-thread simulation with worker thread and spinlock barrier\n" ++
    "struct ThreadedSim {\n" ++
    s!"    alignas(64) {cpuName} cpu;   // separate cache lines\n" ++
    s!"    alignas(64) {periName} peri;\n" ++
    "\n" ++
    "    // Spinlock barrier: main thread (CPU) and worker thread (Peri)\n" ++
    "    alignas(64) std::atomic<uint64_t> peri_go{0};     // main signals worker to start\n" ++
    "    alignas(64) std::atomic<uint64_t> peri_done{0};   // worker signals completion\n" ++
    "    alignas(64) std::atomic<bool> shutdown{false};     // signal worker to exit\n" ++
    "    std::thread worker;\n" ++
    "\n" ++
    "    ThreadedSim() { reset(); }\n" ++
    "    ~ThreadedSim() { stop_worker(); }\n" ++
    "\n" ++
    "    void start_worker() {\n" ++
    "        worker = std::thread([this]() {\n" ++
    "            uint64_t cycle = 0;\n" ++
    "            while (!shutdown.load(std::memory_order_relaxed)) {\n" ++
    "                // Spin-wait for main thread to signal new work\n" ++
    "                uint64_t target = peri_go.load(std::memory_order_acquire);\n" ++
    "                while (target <= cycle) {\n" ++
    "                    if (shutdown.load(std::memory_order_relaxed)) return;\n" ++
    "                    __builtin_ia32_pause();\n" ++
    "                    target = peri_go.load(std::memory_order_acquire);\n" ++
    "                }\n" ++
    "                // Run all pending cycles in batch\n" ++
    "                while (cycle < target) {\n" ++
    "                    cycle++;\n" ++
    "                    peri.eval();\n" ++
    "                    peri.tick();\n" ++
    "                }\n" ++
    "                // Signal completion\n" ++
    "                peri_done.store(cycle, std::memory_order_release);\n" ++
    "            }\n" ++
    "        });\n" ++
    "    }\n" ++
    "\n" ++
    "    void stop_worker() {\n" ++
    "        shutdown.store(true, std::memory_order_release);\n" ++
    "        peri_go.store(UINT64_MAX, std::memory_order_release);\n" ++
    "        if (worker.joinable()) worker.join();\n" ++
    "    }\n" ++
    "\n" ++
    "    void reset() {\n" ++
    "        cpu.reset(); peri.reset();\n" ++
    "        peri_go.store(0, std::memory_order_relaxed);\n" ++
    "        peri_done.store(0, std::memory_order_relaxed);\n" ++
    "    }\n" ++
    "\n" ++
    "    uint64_t cycle_count{0};\n" ++
    "\n" ++
    "    void evalTick() {\n" ++
    "        cycle_count++;\n" ++
    "\n" ++
    "        // Exchange boundary signals (from previous cycle)\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      s!"        peri.{sn} = cpu.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    (part.periToCpu.map fun p =>
      let sn := sanitizeName p.name
      s!"        cpu.{sn} = peri.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "\n" ++
    "        // Signal worker to evaluate peripheral\n" ++
    "        peri_go.store(cycle_count, std::memory_order_release);\n" ++
    "\n" ++
    "        // CPU eval+tick (in parallel with worker)\n" ++
    "        cpu.eval();\n" ++
    "        cpu.tick();\n" ++
    "\n" ++
    "        // Wait for worker to finish\n" ++
    "        while (peri_done.load(std::memory_order_acquire) < cycle_count) {\n" ++
    "            __builtin_ia32_pause();\n" ++
    "        }\n" ++
    "    }\n" ++
    "\n" ++
    "    // Peripheral-skip trigger-based eval (single-thread, coarse-grained)\n" ++
    "    // Only re-evaluates peripheral when CPU→Peri boundary signals change.\n" ++
    "    // Previous boundary signal values for dirty detection\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      "    " ++ emitCppType p.ty ++ " _prev_" ++ sn ++ " = 0;").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "\n" ++
    "    void evalTickSeq() {\n" ++
    "        // Always evaluate CPU (changes every cycle)\n" ++
    "        cpu.eval();\n" ++
    "\n" ++
    "        // Check if CPU→Peri boundary signals changed (trigger)\n" ++
    "        bool peri_dirty = false;\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      s!"        if (cpu.{sn} != _prev_{sn}) peri_dirty = true;").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "\n" ++
    "        // Exchange boundary signals\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      s!"        peri.{sn} = cpu.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    (part.periToCpu.map fun p =>
      let sn := sanitizeName p.name
      s!"        cpu.{sn} = peri.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "\n" ++
    "        // Only evaluate peripheral if boundary changed\n" ++
    "        if (peri_dirty) {\n" ++
    "            peri.eval();\n" ++
    "            // Save boundary for next dirty check\n" ++
    (part.cpuToPeri.map fun p =>
      let sn := sanitizeName p.name
      s!"            _prev_{sn} = cpu.{sn};").foldl (· ++ "\n" ++ ·) "" ++ "\n" ++
    "        }\n" ++
    "\n" ++
    "        // Tick both (registers always update)\n" ++
    "        cpu.tick();\n" ++
    "        peri.tick();\n" ++
    "    }\n" ++
    "};\n\n"

  -- JIT FFI exports (single-threaded interface wrapping the 2-partition sim)
  let ffi :=
    "extern \"C\" {\n" ++
    "void* jit_create() {\n" ++
    "    auto* s = new ThreadedSim();\n" ++
    "    return s;\n" ++
    "}\n" ++
    "void  jit_destroy(void* ctx) {\n" ++
    "    auto* s = static_cast<ThreadedSim*>(ctx);\n" ++
    "    s->stop_worker();\n" ++
    "    delete s;\n" ++
    "}\n" ++
    "void  jit_reset(void* ctx) {\n" ++
    "    auto* s = static_cast<ThreadedSim*>(ctx);\n" ++
    "    s->stop_worker();\n" ++
    "    s->reset();\n" ++
    "    s->cycle_count = 0;\n" ++
    "    s->shutdown.store(false, std::memory_order_relaxed);\n" ++
    "    // Worker not started: using evalTickSeq (peripheral-skip) mode\n" ++
    "}\n" ++
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
    "void  jit_eval_tick(void* ctx) { static_cast<ThreadedSim*>(ctx)->evalTickSeq(); }\n" ++
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
