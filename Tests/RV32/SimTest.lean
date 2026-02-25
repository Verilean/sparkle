/-
  RV32I Lean4-native Simulation Test

  Runs the Signal DSL SoC with pre-loaded firmware using memoryWithInit.
  Simulates via Signal.atTime (pure Lean evaluation, no iverilog needed).
  Uses Signal.loopMemo for memoized evaluation to avoid stack overflow.

  Usage:
    lake env lean --run Tests/RV32/SimTest.lean [firmware.hex] [cycles]
-/

import Examples.RV32.SoC
import Sparkle.Utils.HexLoader

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.SoC
open Sparkle.Utils.HexLoader

def defaultDom : DomainConfig := domain50MHz

def main (args : List String) : IO Unit := do
  let hexPath := args.head? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[1]? |>.bind String.toNat?) |>.getD 100

  -- Check if firmware file exists
  let fileExists ← System.FilePath.pathExists hexPath
  unless fileExists do
    IO.println s!"No firmware file found at {hexPath}, running with empty IMEM"
    let emptyFirmware : BitVec 12 → BitVec 32 := fun _ => 0#32
    let soc ← @rv32iSoCSimulate defaultDom emptyFirmware
    for cycle in [:maxCycles] do
      let pc := soc.atTime cycle
      IO.println s!"cycle {cycle}: PC = 0x{pc.toHex}"
    return

  IO.println s!"Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  IO.println s!"Loaded {firmware.size} words"
  let initFn := arrayToInitFn firmware

  IO.println s!"Running Lean4 simulation for {maxCycles} cycles..."
  let soc ← @rv32iSoCSimulateFull defaultDom initFn

  -- Extract signals from the 56-element state tuple
  let pcSig := projN! soc 56 0           -- PC
  let storeAddrSig := projN! soc 56 41   -- Previous store address (ALU result)
  let storeDataSig := projN! soc 56 42   -- Previous store data (ex_rs2)
  let storeEnSig := projN! soc 56 43     -- Previous store enable (idex_memWrite)
  -- Extra diagnostics
  let exwbAluSig := projN! soc 56 30     -- exwb_alu (should match prevStoreAddr)
  let idexMemWriteSig := projN! soc 56 9 -- idex_memWrite (EX stage store enable)
  let idexPcSig := projN! soc 56 26      -- idex_pc (PC of EX stage instruction)

  let mut prevPC := 0#32
  let mut haltCount := 0
  let mut uartLog : Array (BitVec 32) := #[]
  for cycle in [:maxCycles] do
    let pc := pcSig.atTime cycle

    -- Detect stores and check for UART writes
    if cycle > 0 then
      let storeEn := storeEnSig.atTime cycle
      if storeEn then
        let storeAddr := storeAddrSig.atTime cycle
        let storeData := storeDataSig.atTime cycle
        -- Debug: show all stores for cycles 28-50
        if cycle >= 28 && cycle <= 70 then
          let exwbAlu := exwbAluSig.atTime cycle
          let idexPc := idexPcSig.atTime cycle
          IO.println s!"  cycle {cycle} STORE: addr=0x{storeAddr.toHex} exwb=0x{exwbAlu.toHex} data=0x{storeData.toHex} exPC=0x{idexPc.toHex}"
        -- UART is at 0x10000000
        let addrHi := storeAddr.extractLsb' 24 8
        if addrHi == 0x10#8 then
          uartLog := uartLog.push storeData
          IO.println s!"  UART[{uartLog.size}]: 0x{storeData.toHex}"

    -- Print EX stage info for early cycles
    if cycle >= 28 && cycle <= 50 then
      let exwbAlu := exwbAluSig.atTime cycle
      let idexMW := idexMemWriteSig.atTime cycle
      let idexPc := idexPcSig.atTime cycle
      IO.println s!"cycle {cycle}: PC=0x{pc.toHex} EX_PC=0x{idexPc.toHex} ALU=0x{exwbAlu.toHex} memW={idexMW}"
    else if cycle < 28 || cycle % 5000 == 0 then
      IO.println s!"cycle {cycle}: PC = 0x{pc.toHex}"

    -- Detect halt (PC stuck for 10+ cycles)
    if pc == prevPC then
      haltCount := haltCount + 1
      if haltCount >= 10 then
        IO.println s!"Halt detected at cycle {cycle}: PC = 0x{pc.toHex}"
        IO.println s!"\n=== UART Output ({uartLog.size} words) ==="
        for val in uartLog do
          IO.println s!"  0x{val.toHex}"
        if uartLog.contains 0xCAFE0000#32 then
          IO.println "\n*** ALL TESTS PASSED ***"
        else if uartLog.contains 0xDEADDEAD#32 then
          IO.println "\n*** SOME TESTS FAILED ***"
        else
          IO.println "\n*** No pass/fail marker found ***"
        return
    else
      haltCount := 0
    prevPC := pc

  IO.println s!"Simulation completed ({maxCycles} cycles)"
  IO.println s!"\n=== UART Output ({uartLog.size} words) ==="
  for val in uartLog do
    IO.println s!"  0x{val.toHex}"
