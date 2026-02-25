/-
  RV32I SoC Verilog Synthesis

  The #synthesizeVerilog command lives here rather than in SoC.lean because
  rv32iSoC with an implicit {dom} parameter is compiled as a closed term
  (DomainConfig is erased at runtime) causing Signal.loop to be evaluated
  at module init → stack overflow. Keeping it separate means simulation
  executables don't import this module.

  TODO: rv32iSoC was removed from SoC.lean to fix module-init overflow.
  To restore synthesis, either:
  1. Define rv32iSoC here directly (uses Signal.memory for IMEM, not memoryWithInit)
  2. Parameterize rv32iSoCWithFirmwareBody to support both IMEM variants
-/
import Examples.RV32.SoC

-- open Sparkle.Core.Domain
-- open Sparkle.Examples.RV32.SoC

-- def rv32iSoCForSynth {dom : DomainConfig} : Signal dom (BitVec 32) :=
--   rv32iSoC dom

-- #synthesizeVerilog rv32iSoCForSynth
