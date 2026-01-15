/-
  Sparkle-16 ALU (Arithmetic Logic Unit)

  Performs arithmetic and logical operations for the CPU.

  Operations:
  - 000: ADD (a + b)
  - 001: SUB (a - b)
  - 002: AND (a & b)
  - 011: (Reserved for future operations)

  Flags:
  - zero: Result is zero
  - (negative, carry, overflow could be added later)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.Backend.Verilog

namespace Sparkle16

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

/-- ALU Operation codes (3-bit) -/
inductive ALUOp where
  | ADD : ALUOp  -- 000
  | SUB : ALUOp  -- 001
  | AND : ALUOp  -- 010
  deriving Repr, BEq

def ALUOp.toNat : ALUOp → Nat
  | ADD => 0
  | SUB => 1
  | AND => 2

/--
  ALU Module

  Inputs:
  - opcode: 3-bit operation selector
  - a: 16-bit operand A
  - b: 16-bit operand B

  Outputs:
  - result: 16-bit result
  - zero: 1-bit zero flag (result == 0)
-/
def aluModule : Module :=
  runModule "ALU" do
    -- Inputs
    addInput "opcode" (.bitVector 3)
    addInput "a" (.bitVector 16)
    addInput "b" (.bitVector 16)

    -- Compute all operations in parallel (hardware does this naturally)
    -- ADD operation
    let addResult ← makeWire "add_result" (.bitVector 16)
    emitAssign addResult (.op .add [.ref "a", .ref "b"])

    -- SUB operation
    let subResult ← makeWire "sub_result" (.bitVector 16)
    emitAssign subResult (.op .sub [.ref "a", .ref "b"])

    -- AND operation
    let andResult ← makeWire "and_result" (.bitVector 16)
    emitAssign andResult (.op .and [.ref "a", .ref "b"])

    -- Select result based on opcode using mux tree
    -- First mux: select between ADD (000) and SUB (001)
    let addOrSub ← makeWire "add_or_sub" (.bitVector 16)
    let opcLsb ← makeWire "opc_lsb" .bit
    emitAssign opcLsb (.op .eq [
      .op .and [.ref "opcode", .const 1 3],  -- opcode[0]
      .const 1 3
    ])
    emitAssign addOrSub (.op .mux [
      .ref opcLsb,
      .ref subResult,
      .ref addResult
    ])

    -- Second mux: select between (ADD/SUB) and AND
    let opcBit1 ← makeWire "opc_bit1" .bit
    emitAssign opcBit1 (.op .eq [
      .op .and [.ref "opcode", .const 2 3],  -- opcode[1]
      .const 2 3
    ])

    let finalResult ← makeWire "final_result" (.bitVector 16)
    emitAssign finalResult (.op .mux [
      .ref opcBit1,
      .ref andResult,
      .ref addOrSub
    ])

    -- Compute zero flag (result == 0)
    let zeroFlag ← makeWire "zero_flag" .bit
    emitAssign zeroFlag (.op .eq [.ref finalResult, .const 0 16])

    -- Outputs
    addOutput "result" (.bitVector 16)
    addOutput "zero" .bit
    emitAssign "result" (.ref finalResult)
    emitAssign "zero" (.ref zeroFlag)

/-- Generate Verilog for the ALU -/
def generateALUVerilog : IO Unit := do
  let verilog := Sparkle.Backend.Verilog.toVerilog aluModule
  IO.println "=== ALU Module Verilog ==="
  IO.println verilog
  Sparkle.Backend.Verilog.writeVerilogFile aluModule "ALU.sv"

-- Main: Test and generate Verilog
def main : IO Unit := do
  IO.println "=== Sparkle-16 ALU Module ==="
  IO.println ""
  IO.println aluModule
  IO.println ""
  generateALUVerilog

#eval main

end Sparkle16
