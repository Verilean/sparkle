import Sparkle
import Sparkle.Compiler.Elab
import Tests.TestCircuits
import Tests.SymbolicParameterCircuits
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

/-- Synthesize a native parameterized module without specializing its widths. -/
def synthesizeParameterizedToString (declName : Name)
    (parameters : List (String × Nat)) : Lean.MetaM String := do
  let (module, _) ← synthesizeCombinationalWithParameters declName parameters
  return toVerilog module

/-- Check that rejected parameter contracts report the intended reason. -/
def parameterizedSynthesisRejectsWith (declName : Name)
    (parameters : List (String × Nat)) (needle : String) : Lean.MetaM Bool := do
  try
    let _ ← synthesizeCombinationalWithParameters declName parameters
    return false
  catch error =>
    let message ← error.toMessageData.toString
    return message.containsSubstr needle

/-- Check that ordinary synthesis rejects an invalid top with the intended reason. -/
def synthesisRejectsWith (declName : Name) (needle : String) : Lean.MetaM Bool := do
  try
    let _ ← synthesizeCombinational declName
    return false
  catch error =>
    let message ← error.toMessageData.toString
    return message.containsSubstr needle

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
  symbolicXorVerilog : String
  symbolicConcatVerilog : String
  symbolicSliceLowVerilog : String
  symbolicZeroExtendVerilog : String
  concreteSliceLow8Verilog : String
  rejectsOrdinaryUnresolvedWidth : Bool
  rejectsUnretainedWidth : Bool
  rejectsMissingBinder : Bool
  rejectsDuplicateParameter : Bool
  rejectsZeroWidthDefault : Bool

/-- Synthesize all modules for testing -/
def synthesizeAll : Lean.MetaM VerilogOutputs := do
  let addVerilog ← synthesizeToString `test_add
  let andVerilog ← synthesizeToString `test_and
  let muxVerilog ← synthesizeToString `test_mux
  let flipflopVerilog ← synthesizeToString `test_flipflop
  let hierarchicalVerilog ← synthesizeDesignToString `test_hierarchical_alu
  let symbolicXorVerilog ←
    synthesizeParameterizedToString `symbolicXor [("W", 8)]
  let symbolicConcatVerilog ←
    synthesizeParameterizedToString `symbolicConcat [("HI", 5), ("LO", 3)]
  let symbolicSliceLowVerilog ←
    synthesizeParameterizedToString `symbolicSliceLow [("W", 8)]
  let symbolicZeroExtendVerilog ←
    synthesizeParameterizedToString `symbolicZeroExtend [("W", 8)]
  let concreteSliceLow8Verilog ← synthesizeToString `concreteSliceLow8
  let rejectsOrdinaryUnresolvedWidth ←
    synthesisRejectsWith `symbolicXor "Unresolved symbolic hardware width"
  let rejectsUnretainedWidth ←
    parameterizedSynthesisRejectsWith `symbolicXor [] "was not retained"
  let rejectsMissingBinder ←
    parameterizedSynthesisRejectsWith `symbolicXor [("MISSING", 8)]
      "is not a top-level Nat binder"
  let rejectsDuplicateParameter ←
    parameterizedSynthesisRejectsWith `symbolicXor [("W", 8), ("W", 16)]
      "must be unique"
  let rejectsZeroWidthDefault ←
    parameterizedSynthesisRejectsWith `symbolicXor [("W", 0)]
      "must have a positive default"
  return {
    addVerilog, andVerilog, muxVerilog, flipflopVerilog, hierarchicalVerilog,
    symbolicXorVerilog, symbolicConcatVerilog, symbolicSliceLowVerilog,
    symbolicZeroExtendVerilog, concreteSliceLow8Verilog,
    rejectsOrdinaryUnresolvedWidth, rejectsUnretainedWidth, rejectsMissingBinder,
    rejectsDuplicateParameter, rejectsZeroWidthDefault
  }

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
    group "Native Symbolic Parameters" (
      group "symbolicXor" (
        test "module has a parameter list"
          (outputs.symbolicXorVerilog.containsSubstr "module symbolicXor #(") $
        test "retains W with its default"
          (outputs.symbolicXorVerilog.containsSubstr "parameter integer W = 8") $
        test "input width depends on W"
          (outputs.symbolicXorVerilog.containsSubstr "input logic [W-1:0]") $
        test "output width depends on W"
          (outputs.symbolicXorVerilog.containsSubstr "output logic [W-1:0]") $
        test "does not freeze the default width"
          (!outputs.symbolicXorVerilog.containsSubstr "[7:0]") $
        test "emits XOR logic"
          (outputs.symbolicXorVerilog.containsSubstr " ^ ")
      ) ++
      group "derived dimensions" (
        test "concat retains both parameters"
          (outputs.symbolicConcatVerilog.containsSubstr "parameter integer HI = 5" &&
           outputs.symbolicConcatVerilog.containsSubstr "parameter integer LO = 3") $
        test "concat output width is HI + LO"
          (outputs.symbolicConcatVerilog.containsSubstr "logic [(HI + LO)-1:0]") $
        test "slice length remains W"
          (outputs.symbolicSliceLowVerilog.containsSubstr "[W-1:0]") $
        test "slice high index remains W - 1"
          (outputs.symbolicSliceLowVerilog.containsSubstr "[(W - 1):0]") $
        test "extension output width remains W + 1"
          (outputs.symbolicZeroExtendVerilog.containsSubstr "logic [(W + 1)-1:0]")
      ) ++
      group "ordinary concrete specialization" (
        test "specializes W + 1 in the input width"
          (outputs.concreteSliceLow8Verilog.containsSubstr "input logic [8:0]") $
        test "specializes W in the output width"
          (outputs.concreteSliceLow8Verilog.containsSubstr "output logic [7:0]")
      ) ++
      group "fail-closed diagnostics" (
        test "ordinary synthesis rejects an unresolved width"
          outputs.rejectsOrdinaryUnresolvedWidth $
        test "rejects an unretained generic width" outputs.rejectsUnretainedWidth $
        test "rejects a requested name without a binder" outputs.rejectsMissingBinder $
        test "rejects duplicate parameter names" outputs.rejectsDuplicateParameter $
        test "rejects a zero hardware-width default" outputs.rejectsZeroWidthDefault
      )
    ) ++
    group "Hierarchical Circuits" (
      group "test_hierarchical_alu" (
        test "top module declared"
          (outputs.hierarchicalVerilog.containsSubstr "module test_hierarchical_alu") $
        -- These used to assert the NAMES `_gen_addResult` / `_gen_subResult`
        -- survive into the netlist.  That was the old blanket contract
        -- ("every `_gen_*` wire is JIT-observable"), which is now opt-in:
        -- unobserved internal wires are the optimiser's to inline, and these
        -- two are.  What the test actually cares about is that the inlined
        -- ALU still computes — so assert the operators, not the names.
        test "has addition (inlined test_add)"
          (hierTopModule.containsSubstr " + ") $
        test "has subtraction (inlined test_sub)"
          (hierTopModule.containsSubstr " - ") $
        test "has mux for op select"
          (hierTopModule.containsSubstr "_gen_op ? ")
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
    #[{module := `Sparkle.Compiler.Elab}, {module := `Sparkle.Backend.Verilog},
      {module := `Tests.TestCircuits}, {module := `Tests.SymbolicParameterCircuits}]
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
