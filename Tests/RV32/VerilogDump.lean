/-
  Dump RV32I SoC Verilog for simulation with iverilog.

  Generates SystemVerilog files from both CircuitM and Signal DSL:
    - rv32i_core.sv    (CircuitM: 4-stage pipeline)
    - rv32i_soc.sv     (CircuitM: top-level SoC)

  Signal DSL Verilog is generated at compile time via #synthesizeVerilog
  in each *Signal.lean file.
-/

import Examples.RV32.Core
import Examples.RV32.SoC

import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.Verilog

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Verilog
open Sparkle.Examples.RV32

def main : IO Unit := do
  let outDir := "hw/gen"
  IO.FS.createDirAll outDir

  -- Generate the Core module (sub-module instantiated by SoC)
  IO.FS.writeFile s!"{outDir}/rv32i_core.sv" (toVerilog Core.buildCore)

  -- Generate the SoC top-level module
  IO.FS.writeFile s!"{outDir}/rv32i_soc.sv" (toVerilog SoC.buildSoC)

  IO.println s!"RV32I Verilog generated in {outDir}/"
  IO.println s!"  - {outDir}/rv32i_core.sv"
  IO.println s!"  - {outDir}/rv32i_soc.sv"
