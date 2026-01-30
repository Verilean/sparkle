/-
  Sparkle16 ALU Tests

  Tests for Signal-based ALU that can be used for:
  1. Hierarchical synthesis (generates Verilog module)
  2. Formal verification (provable properties)
  3. Simulation (functional testing)
-/

import Sparkle
import Sparkle.Compiler.Elab
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle16.Test

/-!
## ALU Implementation

Simple 2-operation ALU:
- sel = false → ADD (a + b)
- sel = true  → SUB (a - b)

This definition is pure functional and can be used in proofs!
-/

/-- ALU: Arithmetic Logic Unit
  Inputs:
    - sel: operation selector (false=ADD, true=SUB)
    - a, b: 16-bit operands
  Output:
    - 16-bit result
-/
def alu (sel : Signal defaultDomain Bool)
        (a b : Signal defaultDomain (BitVec 16))
        : Signal defaultDomain (BitVec 16) :=
  let addResult := (· + ·) <$> a <*> b
  let subResult := (· - ·) <$> a <*> b
  Signal.mux sel subResult addResult

/-!
## Simulation Tests

Test ALU behavior through simulation before synthesis.
-/

/-- Test: ALU performs addition when sel=false -/
def test_alu_add : IO LSpec.TestSeq := do
  let sel := Signal.pure false
  let a := Signal.pure 10#16
  let b := Signal.pure 20#16
  let result := alu sel a b

  return LSpec.test "ALU ADD: 10 + 20 = 30" (result.atTime 0 == 30#16)

/-- Test: ALU performs subtraction when sel=true -/
def test_alu_sub : IO LSpec.TestSeq := do
  let sel := Signal.pure true
  let a := Signal.pure 30#16
  let b := Signal.pure 10#16
  let result := alu sel a b

  return LSpec.test "ALU SUB: 30 - 10 = 20" (result.atTime 0 == 20#16)

/-- Test: ALU works with time-varying inputs -/
def test_alu_varying : IO LSpec.TestSeq := do
  -- Create varying signals
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 10)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 5)⟩
  let sel := Signal.pure false
  let result := alu sel a b

  -- At t=0: 0 + 0 = 0
  -- At t=1: 10 + 5 = 15
  -- At t=2: 20 + 10 = 30
  return LSpec.test "ALU with varying inputs at t=2" (result.atTime 2 == 30#16)

/-!
## E2E Synthesis Tests

These tests verify that:
1. ALU synthesizes to Verilog without errors
2. Generated Verilog contains expected operations
3. Module structure is correct
-/

/-- Synthesize ALU and return Verilog output -/
def synthesizeALU : IO String := do
  -- Set up Lean environment
  let mods : Array Lean.Import := #[
    { module := `Sparkle },
    { module := `Sparkle.Compiler.Elab },
    { module := `Tests.Sparkle16.TestALU }
  ]
  let env ← Lean.importModules mods {}  (trustLevel := 1024)

  let coreCtx : Lean.Core.Context := {
    fileName := "<test>",
    fileMap := default
  }
  let coreState : Lean.Core.State := { env := env }

  -- Synthesize the ALU
  let (result, _) ← Lean.Meta.MetaM.toIO
    (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle16.Test.alu)
    coreCtx coreState

  -- Extract module from tuple
  let (module, _design) := result

  -- Generate Verilog
  let verilog := Sparkle.Backend.Verilog.toVerilog module
  return verilog

/-- E2E Test: Verify ALU synthesizes to valid Verilog -/
def test_alu_synthesis : IO LSpec.TestSeq := do
  let verilog ← synthesizeALU

  return LSpec.group "ALU Verilog Generation" (
    LSpec.test "module declared" (verilog.contains "module Sparkle16_Test_alu") $
    LSpec.test "has sel input" (verilog.contains "_gen_sel_") $
    LSpec.test "has a input" (verilog.contains "_gen_a_") $
    LSpec.test "has b input" (verilog.contains "_gen_b_") $
    LSpec.test "has output port" (verilog.contains "output") $
    LSpec.test "performs addition" (verilog.contains "+") $
    LSpec.test "performs subtraction" (verilog.contains "-") $
    LSpec.test "has mux (ternary)" (verilog.contains "?") $
    LSpec.test "assigns output" (verilog.contains "assign out")
  )

/-!
## Combined Test Suite
-/

def aluTests : IO LSpec.TestSeq := do
  let simAdd ← test_alu_add
  let simSub ← test_alu_sub
  let simVarying ← test_alu_varying
  let synthesis ← test_alu_synthesis

  return LSpec.group "Sparkle16 ALU Tests" (
    LSpec.group "Simulation" (simAdd ++ simSub ++ simVarying) ++
    synthesis
  )

end Sparkle16.Test
