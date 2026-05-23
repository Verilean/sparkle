/-
  CUDA Simulation Backend Tests

  Tests that the CudaSim and CudaDesignStateStruct backends generate correct
  CUDA code from IR modules, matching the usage described in docs/CudaSim.md.
-/

import Sparkle.Backend.CudaSim_addition
import Sparkle.Backend.CudaDesignStateStruct
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Builder
import LSpec

namespace Sparkle.Test.CudaSim

open Sparkle.Backend.CudaSim
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.IR.Builder
open CircuitM
open LSpec

private def hasSubstr (s : String) (sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

-- ── Single-module test fixtures ───────────────────────────────────

/-- 8-bit counter: clk, rst, en → count_out (from TestCppSim) -/
def counterModule : Module :=
  runModule "Counter8" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en" (.bitVector 8)
    addOutput "count_out" (.bitVector 8)
    let inc   ← makeWire "inc" (.bitVector 8)
    let count ← emitRegister "count" "clk" "rst" (.ref inc) 0 (.bitVector 8)
    emitAssign inc (.op .add [.ref count, .const 1 8])
    let next ← makeWire "next" (.bitVector 8)
    emitAssign next (.op .mux [.ref "en", .ref inc, .ref count])
    emitAssign "count_out" (.ref count)

/-- Combinational ALU: rs1, rs2, op → result -/
def aluModule : Module := {
  name        := "ALU"
  isPrimitive := false
  inputs      := [⟨"rs1", .bitVector 32⟩, ⟨"rs2", .bitVector 32⟩,
                  ⟨"op", .bitVector 4⟩]
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

-- ── Hierarchical design for emitCudaDesignStateStruct tests ──────

/-- Top module wiring ALU; matches the CPU example from CudaSim.md -/
def simpleTop : Module := {
  name        := "CPU"
  isPrimitive := false
  inputs      := [⟨"in1", .bitVector 32⟩, ⟨"in2", .bitVector 32⟩,
                  ⟨"op", .bitVector 4⟩]
  outputs     := [⟨"out", .bitVector 32⟩]
  wires       := [⟨"alu_result", .bitVector 32⟩]
  body        := [
    .inst "ALU" "alu" [
      ("rs1",    .ref "in1"),
      ("rs2",    .ref "in2"),
      ("op",     .ref "op"),
      ("result", .ref "alu_result"),
    ],
    .assign "out" (.ref "alu_result"),
  ]
}

def simpleDesign : Design := {
  topModule := "CPU"
  modules   := [aluModule, simpleTop]
}

-- ── Tests ─────────────────────────────────────────────────────────

def cudaSimTests : IO TestSeq := do
  -- Single-module code generation
  let counterCu := toCudaSim counterModule "counter_sim.h"
  let aluCu     := toCudaSim aluModule "alu_sim.h"

  -- Hierarchical design state struct
  let dsResult  := emitCudaDesignStateStruct simpleDesign
  let structText := dsResult.structText
  let wireEdges  := dsResult.wireEdges

  -- Full heterogeneous .cu generation
  let hetroCu := toCudaSimHetero simpleDesign "cpu_design_sim.h"

  return group "CUDA Simulation Backend Tests" (
    group "toCudaSim: Counter Module" (
      test "has auto-generated header"               (hasSubstr counterCu "AUTO-GENERATED") $
      test "mentions module name"                    (hasSubstr counterCu "Counter8") $
      test "includes cstdint"                        (hasSubstr counterCu "#include <cstdint>") $
      test "includes cuda_runtime"                   (hasSubstr counterCu "#include <cuda_runtime.h>") $
      test "includes user header"                    (hasSubstr counterCu "counter_sim.h") $
      test "defines state struct"                    (hasSubstr counterCu "Counter8_state_t") $
      test "has device evalTick function"            (hasSubstr counterCu "Counter8_cuda_evalTick") $
      test "has __device__ qualifier"                (hasSubstr counterCu "__device__") $
      test "has __global__ qualifier"                (hasSubstr counterCu "__global__") $
      test "has batch kernel"                        (hasSubstr counterCu "Counter8_batch_kernel") $
      test "kernel reads thread index"               (hasSubstr counterCu "blockIdx.x * blockDim.x + threadIdx.x") $
      test "kernel has numCycles loop"               (hasSubstr counterCu "numCycles") $
      test "has extern C block"                      (hasSubstr counterCu "extern \"C\"") $
      test "has jit_cuda_alloc"                      (hasSubstr counterCu "jit_cuda_alloc") $
      test "has jit_cuda_free"                       (hasSubstr counterCu "jit_cuda_free") $
      test "has jit_cuda_run"                        (hasSubstr counterCu "jit_cuda_run") $
      test "has jit_cuda_reset"                      (hasSubstr counterCu "jit_cuda_reset") $
      test "has cudaMalloc"                          (hasSubstr counterCu "cudaMalloc") $
      test "has cudaMemcpy"                          (hasSubstr counterCu "cudaMemcpy") $
      test "has uint8_t for bit-type ports"          (hasSubstr counterCu "uint8_t")
    ) ++
    group "toCudaSim: ALU Module" (
      test "defines ALU_state_t struct"              (hasSubstr aluCu "ALU_state_t") $
      test "has device evalTick"                     (hasSubstr aluCu "ALU_cuda_evalTick") $
      test "has batch kernel"                        (hasSubstr aluCu "ALU_batch_kernel") $
      test "has uint32_t for 32-bit ports"           (hasSubstr aluCu "uint32_t") $
      test "includes alu_sim.h"                      (hasSubstr aluCu "alu_sim.h") $
      test "has set_input switch"                    (hasSubstr aluCu "jit_cuda_set_input") $
      test "has get_output switch"                   (hasSubstr aluCu "jit_cuda_get_output")
    ) ++
    group "emitCudaDesignStateStruct: simple CPU design" (
      test "has fused design state comment"          (hasSubstr structText "Fused design state") $
      test "defines CPU_design_state_t"              (hasSubstr structText "CPU_design_state_t") $
      test "has top-level ports section"             (hasSubstr structText "top-level ports") $
      test "has per-module sub-structs section"      (hasSubstr structText "per-module sub-structs") $
      test "includes ALU_state_t sub-struct"         (hasSubstr structText "ALU_state_t") $
      test "has wire_copy function"                  (hasSubstr structText "CPU_wire_copy") $
      test "has design_reset function"               (hasSubstr structText "CPU_design_reset") $
      test "reset uses memset"                       (hasSubstr structText "memset") $
      test "wire edges list is non-empty"            (wireEdges.length > 0) $
      test "has edge for ALU result output"
        (wireEdges.any fun e => e.srcPort == "result" || e.dstPort == "result") $
      test "ALU result edge has 32-bit width"
        (wireEdges.any fun e => (e.srcPort == "result" || e.dstPort == "result") && e.width == 32)
    ) ++
    group "toCudaSimHetero: simple CPU design" (
      test "has auto-generated header"              (hasSubstr hetroCu "AUTO-GENERATED") $
      test "mentions Heterogeneous backend"         (hasSubstr hetroCu "Heterogeneous") $
      test "includes cpu_design_sim.h"             (hasSubstr hetroCu "cpu_design_sim.h") $
      test "has fused design state struct"          (hasSubstr hetroCu "CPU_design_state_t") $
      test "has ALU device evalTick stub"           (hasSubstr hetroCu "ALU_cuda_evalTick") $
      test "has fused batch kernel"                 (hasSubstr hetroCu "CPU_fused_batch_kernel") $
      test "has design alloc"                       (hasSubstr hetroCu "jit_cuda_design_alloc") $
      test "has design free"                        (hasSubstr hetroCu "jit_cuda_design_free") $
      test "has design run"                         (hasSubstr hetroCu "jit_cuda_design_run") $
      test "has design reset"                       (hasSubstr hetroCu "jit_cuda_design_reset") $
      test "has design set_input"                   (hasSubstr hetroCu "jit_cuda_design_set_input") $
      test "has design get_output"                  (hasSubstr hetroCu "jit_cuda_design_get_output") $
      test "has DesignCudaHandle struct"            (hasSubstr hetroCu "DesignCudaHandle") $
      test "has thread index calculation"           (hasSubstr hetroCu "blockIdx.x * blockDim.x + threadIdx.x")
    )
  )

end Sparkle.Test.CudaSim
