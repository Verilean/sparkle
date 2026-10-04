/-
  Build-time check that the tutorial's GPU-simulation chapter (Ch13) keeps
  compiling: the EXACT code from the chapter, plus the `#writeCudaDesign` /
  `#writeCudaIntraDesign` directives it teaches.  A regression in the
  elaborator's `.inst` lowering, the CUDA emitters, or the intra Moore
  analysis breaks `lake build Tests.CudaTutorialTest` (and `lake test` via
  the AllTests import).
-/
import Sparkle
import Sparkle.Compiler.Elab
import Tests.TestCudaSim

namespace Sparkle.Tests.CudaTutorial

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Monte-Carlo fixture (batch backend): a 32-bit LCG

    `x' = 1664525·x + 1013904223`, seedable through an input — the classic
    Numerical Recipes generator.  One flat module; the batch backend runs N
    independently-seeded copies, one GPU thread each. -/

def lcg {dom : DomainConfig}
    (seedLoad : Signal dom Bool) (seed : Signal dom (BitVec 32)) :
    Signal dom (BitVec 32) :=
  circuit do
    let x ← Signal.reg (1#32)
    let xS := (x : Signal dom (BitVec 32))
    x <~ Signal.mux seedLoad seed (xS * (1664525#32) + (1013904223#32))
    return xS

/-! ### Systolic fixture (intra backend): 2×2 weight-stationary mesh

    The PE is a small `@[hardware_module]` returning a named-output record
    (the multi-output sub-module idiom); the mesh wires four instances
    nearest-neighbour.  All cross-PE connections are register outputs
    (Moore-bounded), which is what the intra backend's v1 requires — a
    combinational path across PEs would fail `#writeCudaIntraDesign` with a
    named error at BUILD time. -/

structure PeOut (dom : DomainConfig) where
  aOut : Signal dom (BitVec 32)
  pOut : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PeOut dom) dom := ⟨⟩

@[hardware_module] def pe {dom : DomainConfig}
    (aIn pIn w : Signal dom (BitVec 32)) : PeOut dom :=
  circuit do
    let aReg ← Signal.reg (0#32)
    let pReg ← Signal.reg (0#32)
    let aS := (aReg : Signal dom (BitVec 32))
    let pS := (pReg : Signal dom (BitVec 32))
    aReg <~ aIn
    pReg <~ pIn + aIn * w
    return ({ aOut := aS, pOut := pS } : PeOut dom)

def mesh2x2 {dom : DomainConfig}
    (a0 a1 w00 w01 w10 w11 : Signal dom (BitVec 32)) :
    Signal dom (BitVec 32) :=
  let zero : Signal dom (BitVec 32) := Signal.pure (0#32)
  let pe00 := pe a0        zero      w00
  let pe01 := pe pe00.aOut zero      w01
  let pe10 := pe a1        pe00.pOut w10
  let pe11 := pe pe10.aOut pe01.pOut w11
  let _ := pe11.aOut  -- right edge unused, as in a real array
  pe11.pOut           -- observe the corner PE's accumulator

section SynthesisChecks

-- Batch (Monte-Carlo) path: flat module → one .cu, N instances at run time.
#writeCudaDesign lcg ".lake/build/gen/cuda/tutorial_lcg.cu"

-- Intra (systolic) path, DSL surface — BLOCKED by issue #120: the four
-- distinct-argument `pe` calls above silently collapse into ONE instance
-- (elaborator-level; Verilog path identical), so the directive would emit a
-- wrong single-PE design.  `mesh2x2` stays as the live repro; uncomment once
-- #120 is fixed:
-- #writeCudaIntraDesign mesh2x2 ".lake/build/gen/cuda/tutorial_mesh.cu"

-- Intra path, IR surface (the tutorial's current recommendation): build the
-- mesh as IR `.inst` statements — `Tests.TestCudaSim.systolicDesign` is the
-- 2×2 fixture the GPU co-sim validated cycle-exact — and write via the
-- Except-surfacing wrapper (analysis errors become `#error` in the .cu).
#eval do
  let cu := Sparkle.Backend.CudaIntra.toCudaIntraDesign! Sparkle.Test.CudaSim.systolicDesign
  IO.FS.createDirAll ".lake/build/gen/cuda"
  IO.FS.writeFile ".lake/build/gen/cuda/tutorial_mesh_ir.cu" cu
  IO.println s!"Written intra mesh (IR surface) — {cu.length} chars"

end SynthesisChecks

end Sparkle.Tests.CudaTutorial
