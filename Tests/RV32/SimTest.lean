/-
  RV32I Lean4-native Simulation Test

  Runs the Signal DSL SoC with pre-loaded firmware using memoryWithInit.
  Simulates via Signal.atTime (pure Lean evaluation, no iverilog needed).

  Usage:
    lake env lean --run Tests/RV32/SimTest.lean [firmware.hex] [cycles]
-/

import Examples.RV32.SoC
import Sparkle.Utils.HexLoader

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.SoC
open Sparkle.Utils.HexLoader

def defaultDom : DomainConfig := {
  frequency := 50000000
  resetPolarity := .high
}

def main (args : List String) : IO Unit := do
  let hexPath := args.head? |>.getD "firmware/firmware.hex"
  let maxCycles := (args.get? 1 |>.bind String.toNat?) |>.getD 100

  -- Check if firmware file exists
  let exists ← System.FilePath.pathExists hexPath
  unless exists do
    IO.println s!"No firmware file found at {hexPath}, running with empty IMEM"
    -- Run with zeros (NOP = 0x00000013 is NOT zero, but IMEM reads zero initially)
    let emptyFirmware : BitVec 12 → BitVec 32 := fun _ => 0#32
    let soc := @rv32iSoCWithFirmware defaultDom emptyFirmware
    for cycle in [:maxCycles] do
      let pc := soc.atTime cycle
      IO.println s!"cycle {cycle}: PC = 0x{pc.toHex}"
    return

  IO.println s!"Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  IO.println s!"Loaded {firmware.size} words"
  let initFn := arrayToInitFn firmware

  IO.println s!"Running Lean4 simulation for {maxCycles} cycles..."
  let soc := @rv32iSoCWithFirmware defaultDom initFn
  let mut prevPC := 0#32
  let mut haltCount := 0
  for cycle in [:maxCycles] do
    let pc := soc.atTime cycle
    if cycle % 100 == 0 || cycle < 20 then
      IO.println s!"cycle {cycle}: PC = 0x{pc.toHex}"
    -- Detect halt (PC stuck for 10+ cycles)
    if pc == prevPC then
      haltCount := haltCount + 1
      if haltCount >= 10 then
        IO.println s!"Halt detected at cycle {cycle}: PC = 0x{pc.toHex}"
        return
    else
      haltCount := 0
    prevPC := pc

  IO.println s!"Simulation completed ({maxCycles} cycles)"
