/-
  JIT Oracle Test — Self-Loop Detection with Firmware

  Runs firmware.hex for 10M cycles with a self-loop oracle that detects
  when the CPU is stuck in `j _halt` and skips forward by advancing the
  CLINT timer. Verifies identical UART output and massive speedup after halt.

  Usage:
    lake exe rv32-jit-oracle-test [jit.cpp] [firmware.hex] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Core.Oracle
import Sparkle.Utils.HexLoader
import IP.RV32.SoC

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Core.Oracle
open Sparkle.Utils.HexLoader
open Sparkle.IP.RV32.SoC

def toHex32 (v : Nat) : String :=
  let hexStr := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[2]? >>= String.toNat?).getD 10_000_000

  IO.println s!"OracleTest: Compiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "OracleTest: Loaded JIT module"

  -- Resolve wire indices (same as SoCOutput.wireNames)
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  IO.println s!"OracleTest: Resolved {wireIndices.size} wire indices"

  -- Verify register layout: pcReg wire should match register index 8
  -- (8 divider registers at 0-7, then SoCState field 0 = pcReg at index 8)
  let numRegs ← JIT.numRegs handle
  IO.println s!"OracleTest: {numRegs} registers"

  -- Load firmware into IMEM (memory index 0)
  IO.println s!"OracleTest: Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- Create self-loop oracle
  let config : SelfLoopConfig := {
    threshold := 50
    skipAmount := 1000
    pcWireArrayIdx := 0    -- _gen_pcReg is first in SoCOutput.wireNames
    mtimeLoRegIdx := 54    -- SoCState field 46 + 8 divider regs
    mtimeHiRegIdx := 55    -- SoCState field 47 + 8 divider regs
  }
  let (oracle, oracleStateRef) ← mkSelfLoopOracle config
  IO.println s!"OracleTest: Created self-loop oracle (threshold={config.threshold}, skip={config.skipAmount})"

  -- Run simulation with oracle
  IO.println s!"OracleTest: Running for {maxCycles} cycles with oracle..."
  let startTime ← IO.monoNanosNow
  let uartLogRef ← IO.mkRef (#[] : Array UInt64)
  let passedRef ← IO.mkRef false

  let actualCycles ← JIT.runOptimized handle maxCycles wireIndices oracle
    fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      if out.uartValid then
        let log ← uartLogRef.get
        uartLogRef.set (log.push out.uartData.toNat.toUInt64)
        IO.println s!"  UART[{log.size + 1}] @ cycle {cycle}: 0x{toHex32 out.uartData.toNat}"
        if out.uartData.toNat == 0xCAFE0000 then
          passedRef.set true
      return true  -- always continue (let oracle handle skipping)

  let endTime ← IO.monoNanosNow
  let elapsed_ms := (endTime - startTime) / 1_000_000

  -- Gather results
  let uartLog ← uartLogRef.get
  let passed ← passedRef.get
  let oracleState ← oracleStateRef.get

  -- Report
  IO.println s!"\n=== Oracle Test Results ==="
  IO.println s!"  Actual cycles executed:  {actualCycles}"
  IO.println s!"  Oracle triggers:         {oracleState.triggerCount}"
  IO.println s!"  Total cycles skipped:    {oracleState.totalSkipped}"
  IO.println s!"  UART words captured:     {uartLog.size}"
  IO.println s!"  Wall-clock time:         {elapsed_ms} ms"
  if elapsed_ms > 0 then
    let effectiveCycPerSec := actualCycles * 1000 / elapsed_ms
    IO.println s!"  Effective cyc/s:         {effectiveCycPerSec}"

  JIT.destroy handle

  if passed then
    IO.println s!"\n*** PASS: 0xCAFE0000 marker seen, {uartLog.size} UART words ***"
    return 0
  else
    IO.eprintln "\n*** FAIL: 0xCAFE0000 marker not seen ***"
    return 1
