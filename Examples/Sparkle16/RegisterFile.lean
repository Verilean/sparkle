/-
  Sparkle-16 Register File

  8 general-purpose registers (R0-R7):
  - R0 is hardwired to 0 (cannot be written)
  - R1-R7 are writable 16-bit registers

  Interface:
  - Inputs: clk, rst, we (write enable), rd_addr, wr_addr, wr_data
  - Outputs: rd_data

  Implementation:
  - Single read port, single write port
  - Synchronous writes (on clock edge)
  - Asynchronous reads (combinational)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.Backend.Verilog

namespace Sparkle16

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

/--
  Register File Module

  8 registers with R0 hardwired to 0.

  Inputs:
  - clk: Clock signal
  - rst: Reset signal
  - we: Write enable (1 = write, 0 = no write)
  - rd_addr: Read address (3 bits, 0-7)
  - wr_addr: Write address (3 bits, 0-7)
  - wr_data: Write data (16 bits)

  Outputs:
  - rd_data: Read data (16 bits)
-/
def registerFileModule : Module :=
  runModule "RegisterFile" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "we" .bit
    addInput "rd_addr" (.bitVector 3)
    addInput "wr_addr" (.bitVector 3)
    addInput "wr_data" (.bitVector 16)

    -- Create 8 registers (R0-R7)
    -- R0 is special: always reads as 0, ignores writes
    -- R1-R7 are normal registers

    -- For each register R1-R7, create a register with conditional write
    let mut regWires : Array String := #[]

    -- R0: Just a constant 0 (no actual register)
    let r0Wire ← makeWire "r0" (.bitVector 16)
    emitAssign r0Wire (.const 0 16)
    regWires := regWires.push r0Wire

    -- R1-R7: Actual registers with write enable control
    for regIdx in [1:8] do
      -- Check if this register should be written
      -- writeThisReg = we && (wr_addr == regIdx)
      let addrMatchWire ← makeWire s!"wr_addr_eq_{regIdx}" .bit
      emitAssign addrMatchWire (.op .eq [
        .ref "wr_addr",
        .const regIdx 3
      ])

      let writeEnableWire ← makeWire s!"we_{regIdx}" .bit
      emitAssign writeEnableWire (.op .and [
        .ref "we",
        .ref addrMatchWire
      ])

      -- Register input: use mux to choose between current value and new value
      -- If writeEnable: use wr_data, else: keep current value (feedback)
      let regName := s!"r{regIdx}"

      -- We need to create a wire for the register's current output first
      let regOutWire ← makeWire s!"{regName}_q" (.bitVector 16)

      -- Mux for register input: writeEnable ? wr_data : current_value
      let regInputWire ← makeWire s!"{regName}_d" (.bitVector 16)
      emitAssign regInputWire (.op .mux [
        .ref writeEnableWire,
        .ref "wr_data",
        .ref regOutWire
      ])

      -- Create the register
      let regOut ← emitRegister regName "clk" "rst" (.ref regInputWire) 0 (.bitVector 16)

      -- Connect register output to the feedback wire
      emitAssign regOutWire (.ref regOut)

      regWires := regWires.push regOut

    -- Read mux: Select register based on rd_addr
    -- Build an 8-way mux tree

    -- Helper function to build nested muxes for 8 inputs
    -- Level 0: mux pairs (0-1, 2-3, 4-5, 6-7)
    let mux01 ← makeWire "mux_r0_r1" (.bitVector 16)
    let addr0 ← makeWire "addr_bit0_for_01" .bit
    emitAssign addr0 (.op .eq [
      .op .and [.ref "rd_addr", .const 1 3],
      .const 1 3
    ])
    emitAssign mux01 (.op .mux [
      .ref addr0,
      .ref (regWires[1]!),  -- R1
      .ref (regWires[0]!)   -- R0
    ])

    let mux23 ← makeWire "mux_r2_r3" (.bitVector 16)
    emitAssign mux23 (.op .mux [
      .ref addr0,
      .ref (regWires[3]!),  -- R3
      .ref (regWires[2]!)   -- R2
    ])

    let mux45 ← makeWire "mux_r4_r5" (.bitVector 16)
    emitAssign mux45 (.op .mux [
      .ref addr0,
      .ref (regWires[5]!),  -- R5
      .ref (regWires[4]!)   -- R4
    ])

    let mux67 ← makeWire "mux_r6_r7" (.bitVector 16)
    emitAssign mux67 (.op .mux [
      .ref addr0,
      .ref (regWires[7]!),  -- R7
      .ref (regWires[6]!)   -- R6
    ])

    -- Level 1: mux groups (0-3, 4-7)
    let mux03 ← makeWire "mux_r0_r3" (.bitVector 16)
    let addr1 ← makeWire "addr_bit1" .bit
    emitAssign addr1 (.op .eq [
      .op .and [.ref "rd_addr", .const 2 3],
      .const 2 3
    ])
    emitAssign mux03 (.op .mux [
      .ref addr1,
      .ref mux23,
      .ref mux01
    ])

    let mux47 ← makeWire "mux_r4_r7" (.bitVector 16)
    emitAssign mux47 (.op .mux [
      .ref addr1,
      .ref mux67,
      .ref mux45
    ])

    -- Level 2: final mux (0-7)
    let mux07 ← makeWire "mux_r0_r7" (.bitVector 16)
    let addr2 ← makeWire "addr_bit2" .bit
    emitAssign addr2 (.op .eq [
      .op .and [.ref "rd_addr", .const 4 3],
      .const 4 3
    ])
    emitAssign mux07 (.op .mux [
      .ref addr2,
      .ref mux47,
      .ref mux03
    ])

    -- Output
    addOutput "rd_data" (.bitVector 16)
    emitAssign "rd_data" (.ref mux07)

/-- Generate Verilog for the Register File -/
def generateRegFileVerilog : IO Unit := do
  let verilog := Sparkle.Backend.Verilog.toVerilog registerFileModule
  IO.println "=== Register File Verilog ==="
  IO.println verilog
  Sparkle.Backend.Verilog.writeVerilogFile registerFileModule "RegisterFile.sv"

-- Main: Test and generate Verilog
def main : IO Unit := do
  IO.println "=== Sparkle-16 Register File Module ==="
  IO.println ""
  IO.println "Features:"
  IO.println "- 8 registers (R0-R7)"
  IO.println "- R0 hardwired to 0"
  IO.println "- R1-R7 writable"
  IO.println "- Single read port, single write port"
  IO.println "- Synchronous write, asynchronous read"
  IO.println ""
  IO.println registerFileModule
  IO.println ""
  generateRegFileVerilog

#eval main

end Sparkle16
