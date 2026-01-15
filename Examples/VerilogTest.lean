/-
  Verilog Backend Test

  Demonstrates Phase 4 functionality by generating SystemVerilog
  from the manually-constructed IR examples.
-/

import Sparkle.IR.Builder
import Sparkle.Backend.Verilog

open Sparkle.IR.Type
open Sparkle.IR.AST
open Sparkle.IR.Builder
open Sparkle.Backend.Verilog
open CircuitM

/-- Example 1: Half Adder -/
def halfAdder : Module :=
  runModule "HalfAdder" do
    addInput "a" .bit
    addInput "b" .bit

    let sumWire ← makeWire "sum" .bit
    emitAssign sumWire (Expr.xor (.ref "a") (.ref "b"))

    let carryWire ← makeWire "carry" .bit
    emitAssign carryWire (Expr.and (.ref "a") (.ref "b"))

    addOutput "sum" .bit
    emitAssign "sum" (.ref sumWire)

    addOutput "carry" .bit
    emitAssign "carry" (.ref carryWire)

/-- Example 2: 8-bit Register -/
def register8 : Module :=
  runModule "Register8" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "d" (.bitVector 8)

    let regOut ← emitRegister "q" "clk" "rst" (.ref "d") 0 (.bitVector 8)

    addOutput "q" (.bitVector 8)
    emitAssign "q" (.ref regOut)

/-- Example 3: 8-bit Counter -/
def counter8 : Module :=
  runModule "Counter8" do
    addInput "clk" .bit
    addInput "rst" .bit

    let nextCount ← makeWire "next_count" (.bitVector 8)
    let currentCount ← emitRegister "count" "clk" "rst" (.ref nextCount) 0 (.bitVector 8)

    emitAssign nextCount (Expr.add (.ref currentCount) (.const 1 8))

    addOutput "count" (.bitVector 8)
    emitAssign "count" (.ref currentCount)

/-- Example 4: 2-to-1 Mux -/
def mux2to1 : Module :=
  runModule "Mux2to1" do
    addInput "sel" .bit
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)

    let outWire ← makeWire "out" (.bitVector 8)
    emitAssign outWire (Expr.mux (.ref "sel") (.ref "a") (.ref "b"))

    addOutput "out" (.bitVector 8)
    emitAssign "out" (.ref outWire)

/-- Example 5: ALU (Arithmetic Logic Unit) -/
def alu4Bit : Module :=
  runModule "ALU4Bit" do
    addInput "a" (.bitVector 4)
    addInput "b" (.bitVector 4)
    addInput "op" (.bitVector 2)  -- 00=add, 01=sub, 10=and, 11=or

    -- Compute all operations
    let addResult ← makeWire "add_result" (.bitVector 4)
    emitAssign addResult (Expr.add (.ref "a") (.ref "b"))

    let subResult ← makeWire "sub_result" (.bitVector 4)
    emitAssign subResult (Expr.sub (.ref "a") (.ref "b"))

    let andResult ← makeWire "and_result" (.bitVector 4)
    emitAssign andResult (Expr.and (.ref "a") (.ref "b"))

    let orResult ← makeWire "or_result" (.bitVector 4)
    emitAssign orResult (Expr.or (.ref "a") (.ref "b"))

    -- Mux to select result based on op
    let sel01 ← makeWire "sel01" (.bitVector 4)
    let opBit0 ← makeWire "op_bit0" .bit
    emitAssign opBit0 (.op .and [.ref "op", .const 1 2])
    emitAssign sel01 (Expr.mux (.ref opBit0) (.ref subResult) (.ref addResult))

    let sel23 ← makeWire "sel23" (.bitVector 4)
    emitAssign sel23 (Expr.mux (.ref opBit0) (.ref orResult) (.ref andResult))

    let result ← makeWire "result" (.bitVector 4)
    let opBit1 ← makeWire "op_bit1" .bit
    emitAssign opBit1 (.op .and [.op .shr [.ref "op", .const 1 2], .const 1 2])
    emitAssign result (Expr.mux (.ref opBit1) (.ref sel23) (.ref sel01))

    addOutput "result" (.bitVector 4)
    emitAssign "result" (.ref result)

/-- Example 6: Accumulator with enable -/
def accumulator : Module :=
  runModule "Accumulator" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en" .bit
    addInput "data" (.bitVector 8)

    let accNext ← makeWire "acc_next" (.bitVector 8)
    let accCurrent ← emitRegister "acc" "clk" "rst" (.ref accNext) 0 (.bitVector 8)

    let sum ← makeWire "sum" (.bitVector 8)
    emitAssign sum (Expr.add (.ref accCurrent) (.ref "data"))
    emitAssign accNext (Expr.mux (.ref "en") (.ref sum) (.ref accCurrent))

    addOutput "acc" (.bitVector 8)
    emitAssign "acc" (.ref accCurrent)

/-- Main: Generate Verilog files -/
def main : IO Unit := do
  IO.println "=== Sparkle Phase 4: Verilog Code Generation ===\n"

  -- Display and save each module
  IO.println "1. Half Adder:"
  let halfAdderV := toVerilog halfAdder
  IO.println halfAdderV
  writeVerilogFile halfAdder "HalfAdder.sv"
  IO.println ""

  IO.println "2. 8-bit Register:"
  let register8V := toVerilog register8
  IO.println register8V
  writeVerilogFile register8 "Register8.sv"
  IO.println ""

  IO.println "3. 8-bit Counter:"
  let counter8V := toVerilog counter8
  IO.println counter8V
  writeVerilogFile counter8 "Counter8.sv"
  IO.println ""

  IO.println "4. 2-to-1 Mux:"
  let mux2to1V := toVerilog mux2to1
  IO.println mux2to1V
  writeVerilogFile mux2to1 "Mux2to1.sv"
  IO.println ""

  IO.println "5. 4-bit ALU:"
  let alu4BitV := toVerilog alu4Bit
  IO.println alu4BitV
  writeVerilogFile alu4Bit "ALU4Bit.sv"
  IO.println ""

  IO.println "6. Accumulator:"
  let accumulatorV := toVerilog accumulator
  IO.println accumulatorV
  writeVerilogFile accumulator "Accumulator.sv"
  IO.println ""

  IO.println "✓ Phase 4 Verilog generation complete!"
  IO.println "✓ Generated .sv files in current directory"

#eval main
