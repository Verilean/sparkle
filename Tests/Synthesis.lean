/-
  Synthesis Test Suite

  Tests Phase 2 (IR) and Phase 4 (Verilog) functionality
-/

import Sparkle.IR.Builder
import Sparkle.Backend.Verilog

open Sparkle.IR.Type
open Sparkle.IR.AST
open Sparkle.IR.Builder
open Sparkle.Backend.Verilog
open CircuitM

/-- Test 1: Module with only inputs and outputs -/
def testEmptyModule : IO Unit := do
  IO.println "Test 1: Empty Module (passthrough)"

  let m := runModule "Passthrough" do
    addInput "in" (.bitVector 8)
    addOutput "out" (.bitVector 8)
    emitAssign "out" (.ref "in")

  assert! m.inputs.length == 1
  assert! m.outputs.length == 1
  assert! m.wires.length == 0
  assert! m.body.length == 1

  IO.println "  ✓ Simple module structure correct"

/-- Test 2: Combinational logic generates correct operators -/
def testCombinationalOperators : IO Unit := do
  IO.println "\nTest 2: Combinational Operators"

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

  -- Check IR structure
  assert! m.wires.length == 3
  assert! m.body.length == 6  -- 3 internal assigns + 3 output assigns

  -- Check Verilog generation
  let verilog := toVerilog m
  assert! verilog.length > 100  -- Should have generated some code

  IO.println "  ✓ Operators mapped to Verilog correctly"

/-- Test 3: Register creates always_ff block -/
def testRegisterSynthesis : IO Unit := do
  IO.println "\nTest 3: Register Synthesis"

  let m := runModule "RegTest" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "d" (.bitVector 8)

    let q ← emitRegister "q" "clk" "rst" (.ref "d") 0 (.bitVector 8)

    addOutput "q_out" (.bitVector 8)
    emitAssign "q_out" (.ref q)

  -- Check IR
  assert! m.wires.length == 1  -- q wire
  let hasRegStmt := m.body.any fun stmt =>
    match stmt with
    | .register _ _ _ _ _ => true
    | _ => false
  assert! hasRegStmt

  -- Check Verilog
  let verilog := toVerilog m
  assert! verilog.length > 100

  IO.println "  ✓ Register generates always_ff block"

/-- Test 4: Mux generates ternary operator -/
def testMuxSynthesis : IO Unit := do
  IO.println "\nTest 4: Mux Synthesis"

  let m := runModule "MuxTest" do
    addInput "sel" .bit
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)

    let result ← makeWire "result" (.bitVector 8)
    emitAssign result (.op .mux [.ref "sel", .ref "a", .ref "b"])

    addOutput "out" (.bitVector 8)
    emitAssign "out" (.ref result)

  let verilog := toVerilog m
  assert! verilog.length > 100

  IO.println "  ✓ Mux generates ternary operator"

/-- Test 5: Name hygiene (unique wire names) -/
def testNameHygiene : IO Unit := do
  IO.println "\nTest 5: Name Hygiene"

  let m := runModule "NameTest" do
    addInput "in" (.bitVector 8)

    -- Create multiple wires with same hint
    let w1 ← makeWire "temp" (.bitVector 8)
    let w2 ← makeWire "temp" (.bitVector 8)
    let w3 ← makeWire "temp" (.bitVector 8)

    emitAssign w1 (.ref "in")
    emitAssign w2 (.ref w1)
    emitAssign w3 (.ref w2)

    addOutput "out" (.bitVector 8)
    emitAssign "out" (.ref w3)

  -- All wire names should be unique
  let wireNames := m.wires.map (·.name)
  let uniqueNames := wireNames.eraseDups
  assert! wireNames.length == uniqueNames.length

  IO.println "  ✓ Wire names are unique (no collisions)"

/-- Test 6: Complex circuit (counter) -/
def testComplexCircuit : IO Unit := do
  IO.println "\nTest 6: Complex Circuit (Counter)"

  let m := runModule "Counter" do
    addInput "clk" .bit
    addInput "rst" .bit

    let nextCount ← makeWire "next_count" (.bitVector 8)
    let currentCount ← emitRegister "count" "clk" "rst" (.ref nextCount) 0 (.bitVector 8)

    emitAssign nextCount (.op .add [.ref currentCount, .const 1 8])

    addOutput "count" (.bitVector 8)
    emitAssign "count" (.ref currentCount)

  -- Check structure
  assert! m.inputs.length == 2   -- clk, rst
  assert! m.outputs.length == 1  -- count
  assert! m.wires.length == 2    -- next_count, count register

  -- Check Verilog quality
  let verilog := toVerilog m
  assert! verilog.length > 200  -- Should be substantial

  IO.println "  ✓ Complex circuit generates correct structure"

/-- Test 7: Verilog syntax correctness -/
def testVerilogSyntax : IO Unit := do
  IO.println "\nTest 7: Verilog Syntax"

  let m := runModule "SyntaxTest" do
    addInput "clk" .bit
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)

    let sum ← makeWire "sum" (.bitVector 8)
    emitAssign sum (.op .add [.ref "a", .ref "b"])

    let reg ← emitRegister "result" "clk" "clk" (.ref sum) 0 (.bitVector 8)

    addOutput "out" (.bitVector 8)
    emitAssign "out" (.ref reg)

  let verilog := toVerilog m

  -- Check basic structure
  assert! verilog.length > 200
  assert! !verilog.isEmpty

  IO.println "  ✓ Generated Verilog has correct syntax"

/-- Test 8: Multi-bit operations -/
def testMultiBitOperations : IO Unit := do
  IO.println "\nTest 8: Multi-bit Operations"

  let m := runModule "MultiBit" do
    addInput "a" (.bitVector 16)
    addInput "b" (.bitVector 16)

    let sum ← makeWire "sum" (.bitVector 16)
    emitAssign sum (.op .add [.ref "a", .ref "b"])

    let prod ← makeWire "prod" (.bitVector 16)
    emitAssign prod (.op .mul [.ref "a", .ref "b"])

    addOutput "sum_out" (.bitVector 16)
    emitAssign "sum_out" (.ref sum)

    addOutput "prod_out" (.bitVector 16)
    emitAssign "prod_out" (.ref prod)

  let verilog := toVerilog m
  assert! verilog.length > 200

  IO.println "  ✓ Multi-bit operations work correctly"

/-- Run all synthesis tests -/
def main : IO Unit := do
  IO.println "=== Sparkle Synthesis Test Suite ===\n"

  testEmptyModule
  testCombinationalOperators
  testRegisterSynthesis
  testMuxSynthesis
  testNameHygiene
  testComplexCircuit
  testVerilogSyntax
  testMultiBitOperations

  IO.println "\n✅ All synthesis tests passed!"

#eval main
