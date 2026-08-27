/-
  CUDA Simulation Backend Tests

  Tests that the CudaSim backend generates well-formed CUDA from IR modules,
  matching the usage in docs/CudaSim.md.  Shape/emitter-level only — nvcc and
  a GPU are not required (see `cuda-sim-test` for the host g++ syntax check).
-/

import Sparkle.Backend.CudaSim
import Sparkle.Backend.CudaIntra
import Sparkle.Backend.Partition
import Sparkle.Compiler.Elab
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Builder
import Tests.SymbolicParameterCircuits
import LSpec

-- Build-time command smoke: real Lean → retained IR → specialized CUDA.
#writeParameterizedCudaDesign symbolicXor [W := 17]
  ".lake/build/gen/cuda/symbolic_xor_w17_command.cu"

namespace Sparkle.Test.CudaSim

open Sparkle.Backend.CudaSim
open Sparkle.Backend.CudaIntra
open Sparkle.Backend.Partition
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.IR.Builder
open CircuitM
open LSpec

private def hasSubstr (s : String) (sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

private def errorContainsAll {α : Type} (result : Except String α)
    (needles : List String) : Bool :=
  match result with
  | .ok _ => false
  | .error message => needles.all (hasSubstr message)

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

/-- Fixed-layout CUDA raw APIs must reject this retained-width module until
    callers explicitly specialize W. -/
def symbolicModule : Module := {
  name := "Symbolic"
  parameters := [{ name := "W", defaultValue := 8 }]
  inputs := [⟨"x", .bitVectorDim (.parameter "W")⟩]
  outputs := [⟨"y", .bitVectorDim (.parameter "W")⟩]
  wires := []
  body := [.assign "y" (.ref "x")]
}

def symbolicDesign : Design :=
  { topModule := "Symbolic", modules := [symbolicModule] }

/-- Registered retained-width stage.  Its register makes the child output a
    supported Moore boundary between CUDA intra threads. -/
def retainedStageModule : Module := {
  name := "RetainedStage"
  parameters := [{ name := "W", defaultValue := 8 }]
  inputs := [
    ⟨"clk", .bit⟩,
    ⟨"rst", .bit⟩,
    ⟨"x", .bitVectorDim (.parameter "W")⟩
  ]
  outputs := [⟨"y", .bitVectorDim (.parameter "W")⟩]
  wires := [⟨"r", .bitVectorDim (.parameter "W")⟩]
  body := [
    .register "r" "clk" ("rst", .synchronous) (.ref "x") 0,
    .assign "y" (.ref "r")
  ]
}

/-- One-instance hierarchy: specialization must precede intra layout analysis. -/
def retainedIntraTop : Module := {
  name := "RetainedIntraTop"
  parameters := [{ name := "W", defaultValue := 8 }]
  inputs := [
    ⟨"clk", .bit⟩,
    ⟨"rst", .bit⟩,
    ⟨"x", .bitVectorDim (.parameter "W")⟩
  ]
  outputs := [⟨"y", .bitVectorDim (.parameter "W")⟩]
  wires := [⟨"stage_y", .bitVectorDim (.parameter "W")⟩]
  body := [
    .inst "RetainedStage" "stage0" [
      ("clk", .ref "clk"),
      ("rst", .ref "rst"),
      ("x", .ref "x"),
      ("y", .ref "stage_y")
    ],
    .assign "y" (.ref "stage_y")
  ]
}

def retainedIntraDesign : Design :=
  { topModule := retainedIntraTop.name,
    modules := [retainedStageModule, retainedIntraTop] }

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

-- ── Intra-backend rejection fixtures (v1 restrictions) ──────────────

/-- Purely combinational pass-through: `y = x + 1`.  Its output is a Mealy
    output (comb-depends on the input), so chaining two of them crosses a
    Mealy boundary the intra v1 must reject. -/
def combPassModule : Module := {
  name        := "CombPass"
  isPrimitive := false
  inputs      := [⟨"x", .bitVector 32⟩]
  outputs     := [⟨"y", .bitVector 32⟩]
  wires       := []
  body        := [.assign "y" (.op .add [.ref "x", .const 1 32])]
}

def mealyTop : Module := {
  name        := "MealyTop"
  isPrimitive := false
  inputs      := [⟨"xin", .bitVector 32⟩]
  outputs     := [⟨"yout", .bitVector 32⟩]
  wires       := [⟨"w1", .bitVector 32⟩]
  body := [
    .inst "CombPass" "c0" [("x", .ref "xin"), ("y", .ref "w1")],
    .inst "CombPass" "c1" [("x", .ref "w1"), ("y", .ref "yout")] ]
}

def mealyDesign : Design :=
  { topModule := "MealyTop", modules := [combPassModule, mealyTop] }

def topRegTop : Module := {
  name        := "TopRegTop"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  outputs     := []
  wires       := [⟨"r", .bitVector 8⟩]
  body        := [.register "r" "clk" ("rst", .synchronous) (.ref "r") 0]
}

def topRegDesign : Design :=
  { topModule := "TopRegTop", modules := [peModule, topRegTop] }

def exprConnTop : Module := {
  name        := "ExprConnTop"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"a", .bitVector 32⟩]
  outputs     := []
  wires       := []
  body        := [.inst "PE" "pe0" [("a_in", .op .add [.ref "a", .const 1 32])]]
}

def exprConnDesign : Design :=
  { topModule := "ExprConnTop", modules := [peModule, exprConnTop] }

private def okOut : Except String String → String
  | .ok s => s
  | .error e => s!"<EMIT ERROR: {e}>"

private def errMsg : Except String String → String
  | .ok _ => ""
  | .error e => e

-- ── Tests ─────────────────────────────────────────────────────────

def cudaSimTests : IO TestSeq := do
  -- Single-module code generation.  The device code is now CSim's own struct
  -- + `sparkle_<cls>_eval_tick`, host+device qualified (see CudaSim.lean), so
  -- the assertions target CSim's names rather than #33's old `_state_t` /
  -- `_cuda_evalTick` class-wrapper names.
  let counterCu := toCudaSim counterModule
  let aluCu     := toCudaSim aluModule
  let meshCu    := toCudaSimDesign systolicDesign
  let intraCu   := okOut (toCudaIntraDesign systolicDesign)
  let symbolicCu := toCudaSim symbolicModule
  let symbolicDesignCu := toCudaSimDesign symbolicDesign
  let parameterized3Cu :=
    okOut (toCudaSimWithParameters symbolicModule [("W", 3)])
  let parameterized17Cu :=
    okOut (toCudaSimWithParameters symbolicModule [("W", 17)])
  let parameterized65Cu :=
    okOut (toCudaSimWithParameters symbolicModule [("W", 65)])
  let parameterizedDesign17Cu :=
    okOut (toCudaSimDesignWithParameters symbolicDesign [("W", 17)])
  let parameterizedIntra65Cu :=
    okOut (toCudaIntraDesignWithParameters retainedIntraDesign [("W", 65)])
  let partitionedSymbolic := partitionModule symbolicModule

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
    ) ++
    group "symbolic-width rejection" (
      test "single-module API fails closed"
        (hasSubstr symbolicCu "requires concrete widths") $
      test "design API fails closed"
        (hasSubstr symbolicDesignCu "requires concrete widths") $
      test "raw intra API fails closed before layout analysis"
        (hasSubstr (errMsg (toCudaIntraDesign retainedIntraDesign)) "requires concrete widths")
    ) ++
    group "retained-width CUDA batch specialization" (
      test "W=3 uses byte scalar fields"
        (hasSubstr parameterized3Cu "uint8_t x;" &&
         hasSubstr parameterized3Cu "uint8_t y;" &&
         !hasSubstr parameterized3Cu "#error") $
      test "W=17 uses 32-bit scalar fields"
        (hasSubstr parameterized17Cu "uint32_t x;" &&
         hasSubstr parameterized17Cu "uint32_t y;" &&
         !hasSubstr parameterized17Cu "#error") $
      test "W=65 uses three little-endian words"
        (hasSubstr parameterized65Cu "uint32_t x[3];" &&
         hasSubstr parameterized65Cu "uint32_t y[3];" &&
         !hasSubstr parameterized65Cu "#error") $
      test "W=65 setter exposes the third input word"
        (hasSubstr parameterized65Cu
          "case 2: h_state->x[2] = (uint32_t)val; break;") $
      test "design wrapper specializes W=17"
        (hasSubstr parameterizedDesign17Cu "struct Symbolic" &&
         hasSubstr parameterizedDesign17Cu "uint32_t x;" &&
         !hasSubstr parameterizedDesign17Cu "#error") $
      test "missing binding rejected"
        (errorContainsAll
          (toCudaSimWithParameters symbolicModule []) ["missing", "W"]) $
      test "unknown binding rejected"
        (errorContainsAll
          (toCudaSimWithParameters symbolicModule [("W", 3), ("TYPO", 9)])
          ["unknown", "TYPO"]) $
      test "duplicate binding rejected"
        (errorContainsAll
          (toCudaSimWithParameters symbolicModule [("W", 3), ("W", 17)])
          ["duplicate", "W"]) $
      test "zero binding rejected"
        (errorContainsAll
          (toCudaSimWithParameters symbolicModule [("W", 0)])
          ["W", "zero", "positive"])
    ) ++
    group "partition retained-parameter propagation" (
      test "CPU partition retains W"
        (partitionedSymbolic.cpuModule.parameters == symbolicModule.parameters) $
      test "peripheral partition retains W"
        (partitionedSymbolic.periModule.parameters == symbolicModule.parameters)
    ) ++
    -- Intra (PE-per-thread) backend: table-driven copy descriptors, the two
    -- kernels, and the host entry point (see docs/CudaIntraSim-design.md).
    group "toCudaIntraDesign: 2×2 systolic mesh" (
      test "instance count in tables"                (hasSubstr intraCu "Systolic2x2_intra_M = 4") $
      test "copy dst: consumer a_in offset"          (hasSubstr intraCu "offsetof(struct Systolic2x2, pe_0_1) + offsetof(struct PE, a_in)") $
      test "copy src: producer a_out offset"         (hasSubstr intraCu "offsetof(struct Systolic2x2, pe_0_0) + offsetof(struct PE, a_out)") $
      test "const p_in becomes an immediate"         (hasSubstr intraCu "offsetof(struct PE, p_in)") $
      test "top input feeds a copy entry"            (hasSubstr intraCu "offsetof(struct Systolic2x2, ain_0)") $
      test "top output observed via copy"            (hasSubstr intraCu "offsetof(struct Systolic2x2, result_0)") $
      test "kind dispatch calls PE eval"             (hasSubstr intraCu "sparkle_PE_eval((struct PE*)b)") $
      test "block-barrier kernel emitted"            (hasSubstr intraCu "Systolic2x2_intra_block_kernel") $
      test "grid-barrier kernel emitted"             (hasSubstr intraCu "Systolic2x2_intra_grid_kernel") $
      test "cooperative-groups barrier"              (hasSubstr intraCu "g.sync()") $
      test "host entry jit_intra_run"                (hasSubstr intraCu "jit_intra_run")
    ) ++
    group "retained-width CUDA intra specialization" (
      test "specializes every module in the hierarchy"
        (hasSubstr parameterizedIntra65Cu "struct RetainedStage" &&
         hasSubstr parameterizedIntra65Cu "struct RetainedIntraTop" &&
         hasSubstr parameterizedIntra65Cu "uint32_t x[3];" &&
         hasSubstr parameterizedIntra65Cu "uint32_t y[3];" &&
         !hasSubstr parameterizedIntra65Cu "#error") $
      test "one child instance becomes one intra worker"
        (hasSubstr parameterizedIntra65Cu "RetainedIntraTop_intra_M = 1") $
      test "W=65 setter follows rst and exposes the third word"
        (hasSubstr parameterizedIntra65Cu
          "case 3: h_state->x[2] = (uint32_t)val; break;") $
      test "missing binding rejected before intra analysis"
        (errorContainsAll
          (toCudaIntraDesignWithParameters retainedIntraDesign [])
          ["missing", "W"])
    ) ++
    group "toCudaIntraDesign: v1 rejections" (
      test "Mealy boundary rejected with names"
        (hasSubstr (errMsg (toCudaIntraDesign mealyDesign)) "Mealy boundary") $
      test "top-level register rejected"
        (hasSubstr (errMsg (toCudaIntraDesign topRegDesign)) "top-level register") $
      test "compound connection expr rejected"
        (hasSubstr (errMsg (toCudaIntraDesign exprConnDesign)) "compound expression")
    )
  )

end Sparkle.Test.CudaSim
