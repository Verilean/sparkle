/-
  Sparkle16 Hierarchical Synthesis Tests

  Tests hierarchical module instantiation where the datapath module
  instantiates the ALU as a submodule.
-/

import Sparkle
import Sparkle.Compiler.Elab
import LSpec
import Tests.Sparkle16.TestALU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle16.Test

/-!
## Hierarchical Datapath Implementation

Datapath that:
1. Uses ALU for arithmetic/logic operations (hierarchical instantiation)
2. Registers the ALU result (sequential logic)
3. Demonstrates multi-module synthesis
-/

/-- Datapath: ALU + Register
  Inputs:
    - opSel: operation selector (false=ADD, true=SUB)
    - a, b: 16-bit operands
  Output:
    - 16-bit registered result
-/
def datapath (opSel : Signal defaultDomain Bool)
             (a b : Signal defaultDomain (BitVec 16))
             : Signal defaultDomain (BitVec 16) :=
  -- Compute ALU result (this will become hierarchical instantiation!)
  let aluResult := alu opSel a b
  -- Register the result
  Signal.register 0#16 aluResult

/-!
## Simulation Tests

Test datapath behavior including register delay.
-/

/-- Test: Datapath output is delayed by one cycle -/
def test_datapath_delay : IO LSpec.TestSeq := do
  let sel := Signal.pure false  -- ADD operation
  let a := Signal.pure 10#16
  let b := Signal.pure 20#16
  let result := datapath sel a b

  return LSpec.group "Datapath Register Delay" (
    LSpec.test "t=0: outputs initial value (0)" (result.atTime 0 == 0#16) $
    LSpec.test "t=1: outputs previous result (30)" (result.atTime 1 == 30#16) $
    LSpec.test "t=2: still outputs 30" (result.atTime 2 == 30#16)
  )

/-- Test: Datapath with time-varying inputs -/
def test_datapath_varying : IO LSpec.TestSeq := do
  -- Time-varying inputs: a(t) = t*10, b(t) = t*5
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 10)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 5)⟩
  let sel := Signal.pure false  -- ADD
  let result := datapath sel a b

  -- t=0: output=0 (initial), ALU computes 0+0=0
  -- t=1: output=0 (delayed), ALU computes 10+5=15
  -- t=2: output=15 (delayed), ALU computes 20+10=30
  -- t=3: output=30 (delayed), ALU computes 30+15=45
  return LSpec.group "Datapath with Varying Inputs" (
    LSpec.test "t=0: initial value" (result.atTime 0 == 0#16) $
    LSpec.test "t=1: still initial" (result.atTime 1 == 0#16) $
    LSpec.test "t=2: shows t=1 result" (result.atTime 2 == 15#16) $
    LSpec.test "t=3: shows t=2 result" (result.atTime 3 == 30#16)
  )

/-!
## E2E Hierarchical Synthesis Tests

These tests verify that:
1. Datapath synthesizes to Verilog without errors
2. Generated Verilog instantiates ALU as submodule
3. Module has clock and reset ports (due to register)
4. Hierarchical connections are correct
-/

/-- Synthesize datapath and return Verilog output -/
def synthesizeDatapath : IO String := do
  -- Set up Lean environment
  let mods : Array Lean.Import := #[
    { module := `Sparkle },
    { module := `Sparkle.Compiler.Elab },
    { module := `Tests.Sparkle16.TestALU },
    { module := `Tests.Sparkle16.TestHierarchical }
  ]
  let env ← Lean.importModules mods {} (trustLevel := 1024)

  let coreCtx : Lean.Core.Context := {
    fileName := "<test>",
    fileMap := default
  }
  let coreState : Lean.Core.State := { env := env }

  -- Synthesize the datapath (hierarchical)
  let (design, _, _) ← Lean.Meta.MetaM.toIO
    (Sparkle.Compiler.Elab.synthesizeHierarchical ``Sparkle16.Test.datapath)
    coreCtx coreState

  -- Generate Verilog for all modules (including ALU)
  let verilog := Sparkle.Backend.Verilog.toVerilogDesign design
  return verilog

/-- E2E Test: Verify hierarchical module instantiation -/
def test_hierarchical_synthesis : IO LSpec.TestSeq := do
  let verilog ← synthesizeDatapath

  return LSpec.group "Hierarchical Datapath Verilog" (
    LSpec.group "Module Structure" (
      LSpec.test "datapath module declared" (verilog.contains "module Sparkle16_Test_datapath") $
      LSpec.test "has clock input" (verilog.contains "input logic clk") $
      LSpec.test "has reset input" (verilog.contains "input logic rst") $
      LSpec.test "has opSel input" (verilog.contains "_gen_opSel_") $
      LSpec.test "has a input" (verilog.contains "_gen_a_") $
      LSpec.test "has b input" (verilog.contains "_gen_b_") $
      LSpec.test "has output port" (verilog.contains "output")
    ) ++
    LSpec.group "Hierarchical Instantiation" (
      LSpec.test "instantiates ALU submodule" (verilog.contains "Sparkle16_Test_alu") $
      LSpec.test "has ALU instance" (verilog.contains "inst_Sparkle16_Test_alu") $
      LSpec.test "connects sel to ALU" (verilog.contains "._gen_sel_") $
      LSpec.test "connects a to ALU" (verilog.contains "._gen_a_") $
      LSpec.test "connects b to ALU" (verilog.contains "._gen_b_")
    ) ++
    LSpec.group "Sequential Logic" (
      LSpec.test "has always_ff block" (verilog.contains "always_ff") $
      LSpec.test "sensitive to posedge clk" (verilog.contains "posedge clk") $
      LSpec.test "has reset logic" (verilog.contains "if (rst)") $
      LSpec.test "has register assignment" (verilog.contains "<=")
    )
  )

/-!
## Combined Test Suite
-/

def hierarchicalTests : IO LSpec.TestSeq := do
  let simDelay ← test_datapath_delay
  let simVarying ← test_datapath_varying
  let synthesis ← test_hierarchical_synthesis

  return LSpec.group "Sparkle16 Hierarchical Tests" (
    LSpec.group "Simulation" (simDelay ++ simVarying) ++
    synthesis
  )

end Sparkle16.Test
