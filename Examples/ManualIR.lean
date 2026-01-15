/-
  Manual IR Construction Examples

  Demonstrates Phase 2 functionality by manually building hardware netlists
  using the CircuitM monad.
-/

import Sparkle.IR.Builder

open Sparkle.IR.Type
open Sparkle.IR.AST
open Sparkle.IR.Builder
open CircuitM

/-- Example 1: Half Adder -/
def halfAdder : Module :=
  runModule "HalfAdder" do
    -- Add inputs
    addInput "a" .bit
    addInput "b" .bit

    -- Create sum wire (a XOR b)
    let sumWire ← makeWire "sum" .bit
    emitAssign sumWire (Expr.xor (.ref "a") (.ref "b"))

    -- Create carry wire (a AND b)
    let carryWire ← makeWire "carry" .bit
    emitAssign carryWire (Expr.and (.ref "a") (.ref "b"))

    -- Add outputs
    addOutput "sum" .bit
    emitAssign "sum" (.ref sumWire)

    addOutput "carry" .bit
    emitAssign "carry" (.ref carryWire)

/-- Example 2: Full Adder (using half adders would require instantiation) -/
def fullAdder : Module :=
  runModule "FullAdder" do
    -- Inputs
    addInput "a" .bit
    addInput "b" .bit
    addInput "cin" .bit

    -- sum1 = a XOR b
    let sum1 ← makeWire "sum1" .bit
    emitAssign sum1 (Expr.xor (.ref "a") (.ref "b"))

    -- sum = sum1 XOR cin
    let sumWire ← makeWire "sum" .bit
    emitAssign sumWire (Expr.xor (.ref sum1) (.ref "cin"))

    -- carry1 = a AND b
    let carry1 ← makeWire "carry1" .bit
    emitAssign carry1 (Expr.and (.ref "a") (.ref "b"))

    -- carry2 = sum1 AND cin
    let carry2 ← makeWire "carry2" .bit
    emitAssign carry2 (Expr.and (.ref sum1) (.ref "cin"))

    -- cout = carry1 OR carry2
    let coutWire ← makeWire "cout" .bit
    emitAssign coutWire (Expr.or (.ref carry1) (.ref carry2))

    -- Outputs
    addOutput "sum" .bit
    emitAssign "sum" (.ref sumWire)

    addOutput "cout" .bit
    emitAssign "cout" (.ref coutWire)

/-- Example 3: 4-bit Adder -/
def adder4Bit : Module :=
  runModule "Adder4Bit" do
    -- Inputs
    addInput "a" (.bitVector 4)
    addInput "b" (.bitVector 4)

    -- Output wire for sum
    let sumWire ← makeWire "sum" (.bitVector 4)
    emitAssign sumWire (Expr.add (.ref "a") (.ref "b"))

    -- Output
    addOutput "sum" (.bitVector 4)
    emitAssign "sum" (.ref sumWire)

/-- Example 4: 2-to-1 Mux -/
def mux2to1 : Module :=
  runModule "Mux2to1" do
    -- Inputs
    addInput "sel" .bit
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)

    -- Mux logic: sel ? a : b
    let outWire ← makeWire "out" (.bitVector 8)
    emitAssign outWire (Expr.mux (.ref "sel") (.ref "a") (.ref "b"))

    -- Output
    addOutput "out" (.bitVector 8)
    emitAssign "out" (.ref outWire)

/-- Example 5: Register (D Flip-Flop) -/
def registerExample : Module :=
  runModule "Register8" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "d" (.bitVector 8)

    -- Register: outputs 0 at t=0, then follows input
    let regOut ← emitRegister "q" "clk" "rst" (.ref "d") 0 (.bitVector 8)

    -- Output
    addOutput "q" (.bitVector 8)
    emitAssign "q" (.ref regOut)

/-- Example 6: Counter (register with feedback) -/
def counter8Bit : Module :=
  runModule "Counter8" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit

    -- Create a wire for the next count value
    let nextCount ← makeWire "next_count" (.bitVector 8)

    -- Register to hold current count
    let currentCount ← emitRegister "count" "clk" "rst" (.ref nextCount) 0 (.bitVector 8)

    -- Increment: next_count = current_count + 1
    emitAssign nextCount (Expr.add (.ref currentCount) (.const 1 8))

    -- Output
    addOutput "count" (.bitVector 8)
    emitAssign "count" (.ref currentCount)

/-- Example 7: Accumulator with enable -/
def accumulator : Module :=
  runModule "Accumulator" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en" .bit
    addInput "data" (.bitVector 8)

    -- Wires
    let accNext ← makeWire "acc_next" (.bitVector 8)
    let accCurrent ← emitRegister "acc" "clk" "rst" (.ref accNext) 0 (.bitVector 8)

    -- Compute next value: if en then acc + data else acc
    let sum ← makeWire "sum" (.bitVector 8)
    emitAssign sum (Expr.add (.ref accCurrent) (.ref "data"))
    emitAssign accNext (Expr.mux (.ref "en") (.ref sum) (.ref accCurrent))

    -- Output
    addOutput "acc" (.bitVector 8)
    emitAssign "acc" (.ref accCurrent)

/-- Example 8: Comparison unit -/
def comparator : Module :=
  runModule "Comparator" do
    -- Inputs
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)

    -- Equality
    let eqWire ← makeWire "eq" .bit
    emitAssign eqWire (Expr.eq (.ref "a") (.ref "b"))

    -- Less than
    let ltWire ← makeWire "lt" .bit
    emitAssign ltWire (Expr.lt (.ref "a") (.ref "b"))

    -- Greater than
    let gtWire ← makeWire "gt" .bit
    emitAssign gtWire (Expr.op .gt [.ref "a", .ref "b"])

    -- Outputs
    addOutput "eq" .bit
    emitAssign "eq" (.ref eqWire)

    addOutput "lt" .bit
    emitAssign "lt" (.ref ltWire)

    addOutput "gt" .bit
    emitAssign "gt" (.ref gtWire)

/-- Main: Display all examples -/
def main : IO Unit := do
  IO.println "=== Sparkle Phase 2: Manual IR Examples ===\n"

  IO.println "1. Half Adder:"
  IO.println halfAdder
  IO.println ""

  IO.println "2. Full Adder:"
  IO.println fullAdder
  IO.println ""

  IO.println "3. 4-bit Adder:"
  IO.println adder4Bit
  IO.println ""

  IO.println "4. 2-to-1 Mux:"
  IO.println mux2to1
  IO.println ""

  IO.println "5. 8-bit Register:"
  IO.println registerExample
  IO.println ""

  IO.println "6. 8-bit Counter:"
  IO.println counter8Bit
  IO.println ""

  IO.println "7. Accumulator:"
  IO.println accumulator
  IO.println ""

  IO.println "8. Comparator:"
  IO.println comparator
  IO.println ""

  IO.println "✓ Phase 2 IR building complete!"

#eval main
