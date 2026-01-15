/-
  Primitive Module Test

  Demonstrates how to use technology-specific primitives (blackbox modules)
  like SRAM, ROM, and clock gating cells that are provided by vendors.
-/

import Sparkle.IR.Builder
import Sparkle.Backend.Verilog

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Verilog
open CircuitM

/--
  Example 1: Using a single-port SRAM primitive

  This creates a module that instantiates a vendor-provided SRAM.
  The SRAM itself is declared as a primitive (not defined).
-/
def sramExample : Module :=
  runModule "SRAMExample" do
    -- Add module inputs
    addInput "clk" .bit
    addInput "we" .bit
    addInput "addr" (.bitVector 8)
    addInput "din" (.bitVector 32)

    -- Declare the SRAM primitive (this will be provided by vendor)
    -- 256 words (8-bit addr) x 32 bits wide
    let sramPrimitive := mkSRAMPrimitive "TSMC_SRAM_256x32" 8 32

    -- Create a wire for SRAM output
    let doutWire ← makeWire "sram_dout" (.bitVector 32)

    -- Instantiate the SRAM primitive
    emitInstance "TSMC_SRAM_256x32" "u_sram"
      [ ("clk",  .ref "clk")
      , ("we",   .ref "we")
      , ("addr", .ref "addr")
      , ("din",  .ref "din")
      , ("dout", .ref doutWire)
      ]

    -- Connect SRAM output to module output
    addOutput "dout" (.bitVector 32)
    emitAssign "dout" (.ref doutWire)

/--
  Example 2: Using a clock gating cell

  Clock gating is a power optimization technique where the clock is disabled
  when a circuit is idle. This example shows how to instantiate a vendor
  clock gating cell.
-/
def clockGateExample : Module :=
  runModule "ClockGateExample" do
    -- Module inputs
    addInput "clk" .bit
    addInput "enable" .bit
    addInput "data" (.bitVector 8)

    -- Declare the clock gate primitive
    let ckgtPrimitive := mkClockGatePrimitive "CKGT_X2"

    -- Create gated clock wire
    let gatedClk ← makeWire "gated_clk" .bit

    -- Instantiate clock gate
    emitInstance "CKGT_X2" "u_ckgt"
      [ ("clk",     .ref "clk")
      , ("en",      .ref "enable")
      , ("clk_out", .ref gatedClk)
      ]

    -- Use gated clock for a register
    let regOut ← emitRegister "data_reg" gatedClk "rst" (.ref "data") 0 (.bitVector 8)

    -- Add reset input (needed for register)
    addInput "rst" .bit

    -- Output the registered data
    addOutput "q" (.bitVector 8)
    emitAssign "q" (.ref regOut)

/--
  Example 3: Dual-port SRAM with separate read/write ports

  Some SRAMs have independent read and write ports for higher throughput.
-/
def dualPortSRAMExample : Module :=
  runModule "DualPortSRAMExample" do
    -- Module inputs
    addInput "clk" .bit
    addInput "we" .bit
    addInput "raddr" (.bitVector 8)
    addInput "waddr" (.bitVector 8)
    addInput "din" (.bitVector 32)

    -- Create wire for SRAM read output
    let doutWire ← makeWire "sram_dout" (.bitVector 32)

    -- Instantiate dual-port SRAM primitive
    emitInstance "TSMC_SRAM_DP_256x32" "u_sram_dp"
      [ ("clk",   .ref "clk")
      , ("we",    .ref "we")
      , ("raddr", .ref "raddr")
      , ("waddr", .ref "waddr")
      , ("din",   .ref "din")
      , ("dout",  .ref doutWire)
      ]

    -- Module outputs
    addOutput "dout" (.bitVector 32)
    emitAssign "dout" (.ref doutWire)

/--
  Example 4: ROM primitive for lookup tables

  ROMs are useful for storing constant data like sine wave tables,
  character fonts, or configuration data.
-/
def romExample : Module :=
  runModule "ROMExample" do
    -- Module inputs
    addInput "clk" .bit
    addInput "addr" (.bitVector 9)  -- 512 entries

    -- Create wire for ROM output
    let doutWire ← makeWire "rom_dout" (.bitVector 16)

    -- Instantiate ROM primitive (512 x 16-bit)
    emitInstance "TSMC_ROM_512x16" "u_rom"
      [ ("clk",  .ref "clk")
      , ("addr", .ref "addr")
      , ("dout", .ref doutWire)
      ]

    -- Module outputs
    addOutput "dout" (.bitVector 16)
    emitAssign "dout" (.ref doutWire)

/--
  Example 5: Complex design using multiple primitives

  This shows a realistic design that uses both SRAM and clock gating
  for a power-optimized memory controller.
-/
def complexPrimitiveExample : Module :=
  runModule "MemoryController" do
    -- Module interface
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "enable" .bit
    addInput "we" .bit
    addInput "addr" (.bitVector 8)
    addInput "din" (.bitVector 32)

    -- Clock gating for power saving
    let gatedClk ← makeWire "gated_clk" .bit
    emitInstance "CKGT_X2" "u_ckgt"
      [ ("clk",     .ref "clk")
      , ("en",      .ref "enable")
      , ("clk_out", .ref gatedClk)
      ]

    -- SRAM with gated clock
    let sramDout ← makeWire "sram_dout" (.bitVector 32)
    emitInstance "TSMC_SRAM_256x32" "u_sram"
      [ ("clk",  .ref gatedClk)  -- Use gated clock
      , ("we",   .ref "we")
      , ("addr", .ref "addr")
      , ("din",  .ref "din")
      , ("dout", .ref sramDout)
      ]

    -- Register the output (using gated clock)
    let regDout ← emitRegister "dout_reg" gatedClk "rst" (.ref sramDout) 0 (.bitVector 32)

    -- Module output
    addOutput "dout" (.bitVector 32)
    emitAssign "dout" (.ref regDout)

-- Main: Generate Verilog for all examples
def main : IO Unit := do
  IO.println "=== Primitive Module Examples ===\n"

  IO.println "1. Single-port SRAM Example:"
  IO.println "   - Declares TSMC_SRAM_256x32 as a primitive (blackbox)"
  IO.println "   - Instantiates the SRAM in SRAMExample module\n"
  IO.println (toVerilog sramExample)

  IO.println "\n2. Clock Gate Example:"
  IO.println "   - Uses CKGT_X2 clock gating cell for power optimization"
  IO.println "   - Gates clock based on enable signal\n"
  IO.println (toVerilog clockGateExample)

  IO.println "\n3. Dual-Port SRAM Example:"
  IO.println "   - Separate read and write ports for higher throughput\n"
  IO.println (toVerilog dualPortSRAMExample)

  IO.println "\n4. ROM Example:"
  IO.println "   - Read-only memory for constant data (LUTs, etc.)\n"
  IO.println (toVerilog romExample)

  IO.println "\n5. Complex Design with Multiple Primitives:"
  IO.println "   - Memory controller with clock gating and SRAM"
  IO.println "   - Power-optimized using gated clocks\n"
  IO.println (toVerilog complexPrimitiveExample)

  IO.println "\n✓ All primitive examples generated successfully!"
  IO.println "\nNote: Primitive modules (TSMC_SRAM_*, CKGT_*, TSMC_ROM_*) are blackboxes"
  IO.println "      that must be provided by your technology library."

#eval main
