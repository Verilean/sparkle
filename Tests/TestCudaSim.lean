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

-- ── Hierarchical fixture: a 2×2 weight-stationary systolic mesh ──────
-- Exercises toCudaSimDesign's whole-design emission: the top instantiates
-- PE sub-modules and wires them nearest-neighbour, so CSim must emit the
-- PE struct/functions AND generate the PE-to-PE wire-copy inside the top's
-- eval — the mechanism a real accelerator SIM relies on.

/-- One weight-stationary MAC PE. -/
def peModule : Module := {
  name        := "PE"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩,
                  ⟨"a_in", .bitVector 32⟩, ⟨"p_in", .bitVector 32⟩,
                  ⟨"w", .bitVector 32⟩]
  outputs     := [⟨"a_out", .bitVector 32⟩, ⟨"p_out", .bitVector 32⟩]
  wires       := [⟨"a_reg", .bitVector 32⟩, ⟨"p_reg", .bitVector 32⟩,
                  ⟨"mul", .bitVector 32⟩]
  body := [
    .assign "mul" (.op .mul [.ref "a_in", .ref "w"]),
    .register "a_reg" "clk" ("rst", .synchronous) (.ref "a_in") 0,
    .register "p_reg" "clk" ("rst", .synchronous) (.op .add [.ref "p_in", .ref "mul"]) 0,
    .assign "a_out" (.ref "a_reg"),
    .assign "p_out" (.ref "p_reg") ]
}

/-- 2×2 mesh of PEs, activations from the left edge, partial sums down. -/
def systolic2x2 : Module := {
  name        := "Systolic2x2"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩,
                  ⟨"ain_0", .bitVector 32⟩, ⟨"ain_1", .bitVector 32⟩,
                  ⟨"w_0_0", .bitVector 32⟩, ⟨"w_0_1", .bitVector 32⟩,
                  ⟨"w_1_0", .bitVector 32⟩, ⟨"w_1_1", .bitVector 32⟩]
  outputs     := [⟨"result_0", .bitVector 32⟩, ⟨"result_1", .bitVector 32⟩]
  wires       := [⟨"zero32", .bitVector 32⟩,
                  ⟨"aout_0_0", .bitVector 32⟩, ⟨"pout_0_0", .bitVector 32⟩,
                  ⟨"aout_0_1", .bitVector 32⟩, ⟨"pout_0_1", .bitVector 32⟩,
                  ⟨"aout_1_0", .bitVector 32⟩, ⟨"pout_1_0", .bitVector 32⟩,
                  ⟨"aout_1_1", .bitVector 32⟩, ⟨"pout_1_1", .bitVector 32⟩]
  body := [
    .assign "zero32" (.const 0 32),
    .inst "PE" "pe_0_0" [("clk", .ref "clk"), ("rst", .ref "rst"),
      ("a_in", .ref "ain_0"), ("p_in", .ref "zero32"), ("w", .ref "w_0_0"),
      ("a_out", .ref "aout_0_0"), ("p_out", .ref "pout_0_0")],
    .inst "PE" "pe_0_1" [("clk", .ref "clk"), ("rst", .ref "rst"),
      ("a_in", .ref "aout_0_0"), ("p_in", .ref "zero32"), ("w", .ref "w_0_1"),
      ("a_out", .ref "aout_0_1"), ("p_out", .ref "pout_0_1")],
    .inst "PE" "pe_1_0" [("clk", .ref "clk"), ("rst", .ref "rst"),
      ("a_in", .ref "ain_1"), ("p_in", .ref "pout_0_0"), ("w", .ref "w_1_0"),
      ("a_out", .ref "aout_1_0"), ("p_out", .ref "pout_1_0")],
    .inst "PE" "pe_1_1" [("clk", .ref "clk"), ("rst", .ref "rst"),
      ("a_in", .ref "aout_1_0"), ("p_in", .ref "pout_0_1"), ("w", .ref "w_1_1"),
      ("a_out", .ref "aout_1_1"), ("p_out", .ref "pout_1_1")],
    .assign "result_0" (.ref "pout_1_0"),
    .assign "result_1" (.ref "pout_1_1") ]
}

def systolicDesign : Design :=
  { topModule := "Systolic2x2", modules := [peModule, systolic2x2] }

-- ── Tests ─────────────────────────────────────────────────────────

def cudaSimTests : IO TestSeq := do
  -- Single-module code generation.  The device code is now CSim's own struct
  -- + `sparkle_<cls>_eval_tick`, host+device qualified (see CudaSim.lean), so
  -- the assertions target CSim's names rather than #33's old `_state_t` /
  -- `_cuda_evalTick` class-wrapper names.
  let counterCu := toCudaSim counterModule
  let aluCu     := toCudaSim aluModule
  let meshCu    := toCudaSimDesign systolicDesign

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
    ) ++
    -- Hierarchical design: whole-design emission + generated PE-to-PE
    -- wire-copy inside the top's eval (the systolic-array mechanism).
    group "toCudaSimDesign: 2×2 systolic mesh" (
      test "emits the PE sub-module struct"          (hasSubstr meshCu "struct PE") $
      test "emits the PE eval function"              (hasSubstr meshCu "sparkle_PE_eval") $
      test "emits the top struct"                    (hasSubstr meshCu "struct Systolic2x2") $
      test "top eval_tick present"                   (hasSubstr meshCu "sparkle_Systolic2x2_eval_tick") $
      test "embeds PE instance pe_0_0"               (hasSubstr meshCu "struct PE pe_0_0") $
      test "embeds PE instance pe_1_1"               (hasSubstr meshCu "struct PE pe_1_1") $
      -- the wire-copy: PE[0][0].a_out feeds PE[0][1].a_in, PE[0][0].p_out
      -- feeds PE[1][0].p_in — generated, not hand-written.
      test "generates activation wire-copy →right"   (hasSubstr meshCu "pe_0_1.a_in = aout_0_0") $
      test "generates partial-sum wire-copy →down"   (hasSubstr meshCu "pe_1_0.p_in = pout_0_0") $
      test "batch kernel targets the top"            (hasSubstr meshCu "Systolic2x2_batch_kernel")
    )
  )

end Sparkle.Test.CudaSim
