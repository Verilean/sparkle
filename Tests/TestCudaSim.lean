/-
  CUDA Simulation Backend Tests

  Tests that the CudaSim backend generates well-formed CUDA from IR modules,
  matching the usage in docs/CudaSim.md.  Shape/emitter-level only — nvcc and
  a GPU are not required (see `cuda-sim-test` for the host g++ syntax check).
-/

import Sparkle.Backend.CudaSim
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

-- ── Tests ─────────────────────────────────────────────────────────

def cudaSimTests : IO TestSeq := do
  -- Single-module code generation.  The device code is now CSim's own struct
  -- + `sparkle_<cls>_eval_tick`, host+device qualified (see CudaSim.lean), so
  -- the assertions target CSim's names rather than #33's old `_state_t` /
  -- `_cuda_evalTick` class-wrapper names.
  let counterCu := toCudaSim counterModule
  let aluCu     := toCudaSim aluModule

  return group "CUDA Simulation Backend Tests" (
    group "toCudaSim: Counter Module" (
      test "has auto-generated header"               (hasSubstr counterCu "AUTO-GENERATED") $
      test "mentions module name"                    (hasSubstr counterCu "Counter8") $
      test "includes cstdint"                        (hasSubstr counterCu "#include <cstdint>") $
      test "includes cuda_runtime"                   (hasSubstr counterCu "#include <cuda_runtime.h>") $
      test "reuses CSim device struct"               (hasSubstr counterCu "struct Counter8") $
      test "reuses CSim eval_tick"                   (hasSubstr counterCu "sparkle_Counter8_eval_tick") $
      test "eval_tick is host+device"                (hasSubstr counterCu "__host__ __device__") $
      test "has __global__ qualifier"                (hasSubstr counterCu "__global__") $
      test "has batch kernel"                        (hasSubstr counterCu "Counter8_batch_kernel") $
      test "kernel reads thread index"               (hasSubstr counterCu "blockIdx.x * blockDim.x + threadIdx.x") $
      test "kernel has numCycles loop"               (hasSubstr counterCu "numCycles") $
      test "has extern C block"                      (hasSubstr counterCu "extern \"C\"") $
      test "has jit_cuda_alloc"                      (hasSubstr counterCu "jit_cuda_alloc") $
      test "has jit_cuda_free"                       (hasSubstr counterCu "jit_cuda_free") $
      test "has jit_cuda_run"                        (hasSubstr counterCu "jit_cuda_run") $
      test "has jit_cuda_reset"                      (hasSubstr counterCu "jit_cuda_reset") $
      test "allocates pinned host staging"           (hasSubstr counterCu "cudaMallocHost") $
      test "casts to void** for cudaMalloc"          (hasSubstr counterCu "(void**)&h->d_states") $
      test "has cudaMemcpy"                          (hasSubstr counterCu "cudaMemcpy") $
      test "has uint8_t for bit-type ports"          (hasSubstr counterCu "uint8_t")
    ) ++
    group "toCudaSim: ALU Module" (
      test "reuses CSim device struct"               (hasSubstr aluCu "struct ALU") $
      test "reuses CSim eval_tick"                   (hasSubstr aluCu "sparkle_ALU_eval_tick") $
      test "has batch kernel"                        (hasSubstr aluCu "ALU_batch_kernel") $
      test "has uint32_t for 32-bit ports"           (hasSubstr aluCu "uint32_t") $
      test "has set_input switch"                    (hasSubstr aluCu "jit_cuda_set_input") $
      test "has get_output switch"                   (hasSubstr aluCu "jit_cuda_get_output")
    )
  )

end Sparkle.Test.CudaSim
