/-
  Manual IR Construction for Memory

  Shows how to manually build memory primitives using the IR builder.
-/

import Sparkle.IR.Builder
import Sparkle.Backend.Verilog

open Sparkle.IR.AST
open Sparkle.IR.Builder
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

/-!
## Example: 256-byte RAM

Manually construct a simple RAM module using the IR builder.
-/

def build256ByteRAM : Module :=
  CircuitM.runModule "SimpleRAM" do
    -- Inputs
    CircuitM.addInput "clk" .bit
    CircuitM.addInput "write_addr" (.bitVector 8)
    CircuitM.addInput "write_data" (.bitVector 8)
    CircuitM.addInput "write_enable" .bit
    CircuitM.addInput "read_addr" (.bitVector 8)

    -- Output
    CircuitM.addOutput "read_data" (.bitVector 8)

    -- Emit memory primitive
    let rdataWire ← CircuitM.emitMemory "ram" 8 8 "clk"
      (.ref "write_addr")
      (.ref "write_data")
      (.ref "write_enable")
      (.ref "read_addr")

    -- Connect read data output
    CircuitM.emitAssign "read_data" (.ref rdataWire)

/-!
## Example: 8-register x 16-bit Register File
-/

def buildRegisterFile : Module :=
  CircuitM.runModule "RegisterFile" do
    -- Inputs
    CircuitM.addInput "clk" .bit
    CircuitM.addInput "write_reg" (.bitVector 3)   -- R0-R7
    CircuitM.addInput "write_data" (.bitVector 16)
    CircuitM.addInput "write_enable" .bit
    CircuitM.addInput "read_reg" (.bitVector 3)

    -- Output
    CircuitM.addOutput "read_data" (.bitVector 16)

    -- Emit register file memory
    let rdataWire ← CircuitM.emitMemory "regfile" 3 16 "clk"
      (.ref "write_reg")
      (.ref "write_data")
      (.ref "write_enable")
      (.ref "read_reg")

    -- Connect read data output
    CircuitM.emitAssign "read_data" (.ref rdataWire)

def main : IO Unit := do
  IO.println "=== Memory Manual IR Construction ==="
  IO.println ""

  -- Example 1: 256-byte RAM
  let ramModule := build256ByteRAM
  IO.println "Example 1: 256-byte RAM (8-bit address, 8-bit data)"
  IO.println "======================================================"
  IO.println (toVerilog ramModule)
  IO.println ""

  -- Example 2: Register File
  let regFileModule := buildRegisterFile
  IO.println "Example 2: Register File (8 registers x 16-bit)"
  IO.println "================================================="
  IO.println (toVerilog regFileModule)
  IO.println ""

  IO.println "✓ Both examples generated successfully!"
  IO.println ""
  IO.println "Key features:"
  IO.println "  • Synchronous writes (on clock edge when write_enable=1)"
  IO.println "  • Registered reads (1-cycle latency)"
  IO.println "  • Synthesizable to FPGA BRAM or ASIC SRAM"
