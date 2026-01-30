import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog
import Tests.TestCircuits
import Tests.TestArray
import Tests.Sparkle16.TestALU
import Tests.Sparkle16.TestHierarchical
import Tests.Sparkle16.TestVCD
import Tests.Sparkle16.TestCoSim
import Tests.Sparkle16.TestOverflow
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog
open Sparkle.IR.Type
open Sparkle.IR.AST
open Sparkle.IR.Builder
open Lean (Name)
open LSpec
open CircuitM

/-!
# Comprehensive Test Suite

Integrates all tests:
- Simulation tests (signal behavior)
- IR/Verilog synthesis tests
- Verilog generation verification tests

Run tests: `lake test`
-/

-- ============================================================================
-- Simulation Tests
-- ============================================================================

def simulationTests : TestSeq :=
  group "Signal Simulation Tests" (
    group "Combinational Logic" (
      let a : Signal defaultDomain (BitVec 8) := Signal.pure 5#8
      let b : Signal defaultDomain (BitVec 8) := Signal.pure 3#8
      let sum := (· + ·) <$> a <*> b
      let diff := (· - ·) <$> a <*> b
      let prod := (· * ·) <$> a <*> b

      test "addition works" (sum.atTime 0 == 8#8) $
      test "subtraction works" (diff.atTime 0 == 2#8) $
      test "multiplication works" (prod.atTime 0 == 15#8)
    ) ++
    group "Register Delays" (
      let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 (t * 10)⟩
      let delayed := Signal.register 99#8 input

      test "outputs initial value at t=0" (delayed.atTime 0 == 99#8) $
      test "delays by one cycle at t=1" (delayed.atTime 1 == 0#8) $
      test "delays by one cycle at t=2" (delayed.atTime 2 == 10#8)
    ) ++
    group "Register Chain" (
      let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
      let delay1 := Signal.register 255#8 input
      let delay2 := Signal.register 254#8 delay1
      let delay3 := Signal.register 253#8 delay2

      test "3-cycle delay at t=0" (delay3.atTime 0 == 253#8) $
      test "3-cycle delay at t=1" (delay3.atTime 1 == 254#8) $
      test "3-cycle delay at t=2" (delay3.atTime 2 == 255#8) $
      test "3-cycle delay at t=3" (delay3.atTime 3 == 0#8) $
      test "3-cycle delay at t=4" (delay3.atTime 4 == 1#8)
    ) ++
    group "Multiplexer" (
      let sel : Signal defaultDomain Bool := ⟨fun t => t % 2 == 0⟩
      let a : Signal defaultDomain (BitVec 8) := Signal.pure 0xAA#8
      let b : Signal defaultDomain (BitVec 8) := Signal.pure 0xBB#8
      let result := Signal.mux sel a b

      test "selects a when sel=true" (result.atTime 0 == 0xAA#8) $
      test "selects b when sel=false" (result.atTime 1 == 0xBB#8) $
      test "selects a when sel=true again" (result.atTime 2 == 0xAA#8)
    ) ++
    group "Map with Register" (
      let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
      let doubled := input.map (· * 2#8)
      let registered := Signal.register 0#8 doubled

      test "input value at t=3" (input.atTime 3 == 3#8) $
      test "doubled value at t=3" (doubled.atTime 3 == 6#8) $
      test "registered value at t=3" (registered.atTime 3 == 4#8)
    ) ++
    group "Bundle and Unbundle" (
      let a : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 t⟩
      let b : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 (t + 10)⟩
      let bundled := bundle2 a b
      let (a', b') := unbundle2 bundled

      test "unbundled a preserves value" (a'.atTime 2 == 2#4) $
      test "unbundled b preserves value" (b'.atTime 2 == 12#4)
    )
  )

-- ============================================================================
-- IR/Synthesis Tests
-- ============================================================================

def irSynthesisTests : TestSeq :=
  group "IR and Verilog Synthesis Tests" (
    group "Module Structure" (
      let m := runModule "Passthrough" do
        addInput "in" (.bitVector 8)
        addOutput "out" (.bitVector 8)
        emitAssign "out" (.ref "in")

      test "has correct input count" (m.inputs.length == 1) $
      test "has correct output count" (m.outputs.length == 1) $
      test "has no internal wires" (m.wires.length == 0) $
      test "has one statement" (m.body.length == 1)
    ) ++
    group "Combinational Operators" (
      let m := runModule "CombOps" do
        addInput "a" (.bitVector 4)
        addInput "b" (.bitVector 4)
        let andWire ← makeWire "and_result" (.bitVector 4)
        emitAssign andWire (.op .and [.ref "a", .ref "b"])
        let orWire ← makeWire "or_result" (.bitVector 4)
        emitAssign orWire (.op .or [.ref "a", .ref "b"])
        let xorWire ← makeWire "xor_result" (.bitVector 4)
        emitAssign xorWire (.op .xor [.ref "a", .ref "b"])
        addOutput "and_out" (.bitVector 4)
        emitAssign "and_out" (.ref andWire)
        addOutput "or_out" (.bitVector 4)
        emitAssign "or_out" (.ref orWire)
        addOutput "xor_out" (.bitVector 4)
        emitAssign "xor_out" (.ref xorWire)

      let verilog := toVerilog m

      test "has correct wire count" (m.wires.length == 3) $
      test "has correct statement count" (m.body.length == 6) $
      test "generates non-empty Verilog" (decide (verilog.length > 100)) $
      test "Verilog contains AND operator" (decide ((verilog.splitOn " & ").length > 1)) $
      test "Verilog contains OR operator" (decide ((verilog.splitOn " | ").length > 1)) $
      test "Verilog contains XOR operator" (decide ((verilog.splitOn " ^ ").length > 1))
    ) ++
    group "Register Synthesis" (
      let m := runModule "RegTest" do
        addInput "clk" .bit
        addInput "rst" .bit
        addInput "d" (.bitVector 8)
        let q ← emitRegister "q" "clk" "rst" (.ref "d") 0 (.bitVector 8)
        addOutput "q_out" (.bitVector 8)
        emitAssign "q_out" (.ref q)

      let verilog := toVerilog m

      test "has register statement" (m.body.any (fun s => match s with | Stmt.register .. => true | _ => false)) $
      test "Verilog contains always_ff" (decide ((verilog.splitOn "always_ff").length > 1)) $
      test "Verilog contains posedge clk" (decide ((verilog.splitOn "posedge clk").length > 1)) $
      test "Verilog contains reset logic" (decide ((verilog.splitOn "if (rst)").length > 1))
    )
  )

-- ============================================================================
-- Verilog Generation Verification Tests
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

/-- Create Verilog generation tests from synthesized outputs -/
def makeVerilogTests (outputs : VerilogOutputs) : TestSeq :=
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
  IO.println "║  Sparkle Comprehensive Test Suite     ║"
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

  -- Run Sparkle16 tests
  let sparkle16AluTests ← Sparkle16.Test.aluTests
  let sparkle16HierarchicalTests ← Sparkle16.Test.hierarchicalTests
  let sparkle16VCDTests ← Sparkle16.Test.vcdTests
  let sparkle16CoSimTests ← Sparkle16.Test.coSimTests
  let sparkle16OverflowTests ← Sparkle.Test.Overflow.overflowTests

  -- Run Array/Vector tests
  let arrayTests ← Sparkle.Test.Array.arrayTests

  -- Combine all test suites
  let allTests :=
    simulationTests ++
    irSynthesisTests ++
    makeVerilogTests outputs ++
    arrayTests ++
    sparkle16AluTests ++
    sparkle16HierarchicalTests ++
    sparkle16VCDTests ++
    sparkle16CoSimTests ++
    sparkle16OverflowTests

  lspecIO (Std.HashMap.ofList [("all", [allTests])]) []
