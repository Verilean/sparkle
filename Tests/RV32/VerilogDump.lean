/-
  Dump RV32I SoC Verilog for simulation with iverilog.

  Generates two SystemVerilog files:
    - rv32i_core.sv  (the 4-stage pipeline)
    - rv32i_soc.sv   (top-level SoC with memories, CLINT, CSR)
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
