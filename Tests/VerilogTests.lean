import Sparkle
import Sparkle.Compiler.Elab
import Tests.TestCircuits
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog
open Lean.Elab.Command
open Lean (Name)
open LSpec

/-!
# Verilog Generation Unit Tests using LSpec

Tests that verify the generated Verilog code by synthesizing modules
and checking the output contains expected patterns.

Run tests: `lake exe verilog-tests`
-/

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Check if a string contains a substring -/
def String.containsSubstr (s : String) (sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

/-- Synthesize a module and return its Verilog as a string -/
def synthesizeToString (declName : Name) : Lean.MetaM String := do
  let (module, _) ← synthesizeCombinational declName
  return toVerilog module

/-- Synthesize a hierarchical design and return its Verilog as a string -/
def synthesizeDesignToString (declName : Name) : Lean.MetaM String := do
  let design ← synthesizeHierarchical declName
  return toVerilogDesign design

/-- Extract a specific module from multi-module Verilog output -/
def extractModule (verilog : String) (moduleName : String) : String :=
  let lines := verilog.splitOn "\n"
  let moduleStart := s!"module {moduleName}"
  let startIdx := lines.findIdx? (·.containsSubstr moduleStart)
  match startIdx with
  | none => ""
  | some start =>
    let endIdx := lines.drop start |>.findIdx? (·.containsSubstr "endmodule")
    match endIdx with
    | none => ""
    | some relEnd =>
      let endPos := start + relEnd
      String.intercalate "\n" (lines.toArray[start:endPos+1].toList)

-- ============================================================================
-- Test Suite
-- ============================================================================

/-- Structure to hold synthesized Verilog for testing -/
structure VerilogOutputs where
  addVerilog : String
  andVerilog : String
  muxVerilog : String
  flipflopVerilog : String
  hierarchicalVerilog : String

/-- Synthesize all modules for testing -/
def synthesizeAll : Lean.MetaM VerilogOutputs := do
  let addVerilog ← synthesizeToString `test_add
  let andVerilog ← synthesizeToString `test_and
  let muxVerilog ← synthesizeToString `test_mux
  let flipflopVerilog ← synthesizeToString `test_flipflop
  let hierarchicalVerilog ← synthesizeDesignToString `test_hierarchical_alu
  return { addVerilog, andVerilog, muxVerilog, flipflopVerilog, hierarchicalVerilog }

/-- Create test suite from synthesized outputs -/
def makeTests (outputs : VerilogOutputs) : TestSeq :=
  let addModule := extractModule outputs.addVerilog "test_add"
  let hierTopModule := extractModule outputs.hierarchicalVerilog "test_hierarchical_alu"

  group "Verilog Generation Tests" (
    group "Combinational Circuits" (
      group "test_add (Addition)" (
        test "module declared" (outputs.addVerilog.containsSubstr "module test_add") $
        test "has assign statement" (outputs.addVerilog.containsSubstr "assign") $
        test "has addition operation" (outputs.addVerilog.containsSubstr " + ") $
        test "NO always block (combinational)" (!addModule.containsSubstr "always") $
        test "NO clock signal (combinational)" (!addModule.containsSubstr "clk")
      ) ++
      group "test_and (AND Gate)" (
        test "module declared" (outputs.andVerilog.containsSubstr "module test_and") $
        test "has AND operation" (outputs.andVerilog.containsSubstr " & ")
      ) ++
      group "test_mux (Multiplexer)" (
        test "module declared" (outputs.muxVerilog.containsSubstr "module test_mux") $
        test "has ternary operator" (outputs.muxVerilog.containsSubstr " ? ")
      )
    ) ++
    group "Hierarchical Circuits" (
      group "test_hierarchical_alu" (
        test "top module declared"
          (outputs.hierarchicalVerilog.containsSubstr "module test_hierarchical_alu") $
        test "instantiates test_add"
          (hierTopModule.containsSubstr "test_add inst_test_add") $
        test "instantiates test_sub"
          (hierTopModule.containsSubstr "test_sub inst_test_sub") $
        test "has signal routing (addResult)"
          (hierTopModule.containsSubstr "_gen_addResult_") $
        test "has signal routing (subResult)"
          (hierTopModule.containsSubstr "_gen_subResult_")
      )
    ) ++
    group "Sequential Circuits" (
      group "test_flipflop (Register)" (
        test "module declared"
          (outputs.flipflopVerilog.containsSubstr "module test_flipflop") $
        test "has clock port"
          (outputs.flipflopVerilog.containsSubstr "input logic clk") $
        test "has reset port"
          (outputs.flipflopVerilog.containsSubstr "input logic rst") $
        test "has sequential block"
          (outputs.flipflopVerilog.containsSubstr "always_ff @(posedge clk") $
        test "has reset condition"
          (outputs.flipflopVerilog.containsSubstr "if (rst)")
      )
    )
  )

-- ============================================================================
-- Main Entry Point
-- ============================================================================

def main : IO UInt32 := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Verilog Generation Unit Tests        ║"
  IO.println "╚════════════════════════════════════════╝"
  IO.println ""

  -- Initialize Lean search path
  Lean.initSearchPath (← Lean.findSysroot)

  -- Import required modules
  let env ← Lean.importModules
    #[{module := `Sparkle.Compiler.Elab}, {module := `Sparkle.Backend.Verilog}, {module := `Tests.TestCircuits}]
    {}
    (trustLevel := 1024)

  let coreCtx : Lean.Core.Context := {
    fileName := "<tests>"
    fileMap := default
  }
  let coreState : Lean.Core.State := { env := env }

  let (outputs, _) ← Lean.Meta.MetaM.toIO
    synthesizeAll
    coreCtx
    coreState

  -- Create and run tests
  let tests := makeTests outputs
  lspecIO (Std.HashMap.ofList [("verilog", [tests])]) []
