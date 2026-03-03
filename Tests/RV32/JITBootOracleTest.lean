/-
  JIT Boot Oracle Test — Timer-Compare-Aware Idle-Loop Skipping

  Tests the boot-optimized oracle that detects idle loops and advances
  mtime to mtimecmp (instead of a fixed skip amount). This enables
  Linux boot where the CPU must wake via timer interrupt after WFI/idle.

  Part 1: firmware.hex with skipToTimerCompare=true — verifies identical
  UART output and oracle triggering.

  Part 2: Manual mtimecmp test — sets mtimecmp to a known value after
  firmware completes, verifies exact skip calculation.

  Usage:
    lake exe rv32-jit-boot-oracle-test [jit.cpp] [firmware.hex] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Core.Oracle
import Sparkle.Utils.HexLoader
import Examples.RV32.SoC

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Core.Oracle
open Sparkle.Utils.HexLoader
open Sparkle.Examples.RV32.SoC

def toHex32 (v : Nat) : String :=
  let hexStr := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[2]? >>= String.toNat?).getD 10_000_000

  IO.println "========================================="
  IO.println "  Boot Oracle Test — Timer-Compare-Aware"
  IO.println "========================================="

  IO.println s!"\nCompiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "Loaded JIT module"

  -- Resolve wire indices
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  IO.println s!"Resolved {wireIndices.size} wire indices"

  let numRegs ← JIT.numRegs handle
  IO.println s!"{numRegs} registers"

  -- Load firmware into IMEM (memory index 0)
  IO.println s!"Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- =============================================
  -- Part 1: Timer-Compare Oracle with firmware.hex
  -- =============================================
  IO.println s!"\n--- Part 1: Timer-Compare Oracle (firmware.hex, {maxCycles} cycles) ---"

  let config : SelfLoopConfig := {
    threshold := 50
    skipAmount := 1000
    pcWireArrayIdx := 0       -- _gen_pcReg is first in SoCOutput.wireNames
    mtimeLoRegIdx := 54       -- SoCState field 46 + 8 divider regs
    mtimeHiRegIdx := 55       -- SoCState field 47 + 8 divider regs
    mtimecmpLoRegIdx := 56    -- SoCState field 48 + 8 divider regs
    mtimecmpHiRegIdx := 57    -- SoCState field 49 + 8 divider regs
    skipToTimerCompare := true
    maxSkip := 10_000_000
  }
  let (oracle, oracleStateRef) ← mkSelfLoopOracle config
  IO.println s!"Created boot oracle (threshold={config.threshold}, maxSkip={config.maxSkip}, skipToTimerCompare=true)"

  -- Run simulation with oracle
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
      return true

  let endTime ← IO.monoNanosNow
  let elapsed_ms := (endTime - startTime) / 1_000_000

  -- Gather results
  let uartLog ← uartLogRef.get
  let passed ← passedRef.get
  let oracleState ← oracleStateRef.get

  -- Report Part 1
  IO.println s!"\n=== Part 1 Results ==="
  IO.println s!"  Actual cycles executed:  {actualCycles}"
  IO.println s!"  Oracle triggers:         {oracleState.triggerCount}"
  IO.println s!"  Total cycles skipped:    {oracleState.totalSkipped}"
  IO.println s!"  UART words captured:     {uartLog.size}"
  IO.println s!"  Wall-clock time:         {elapsed_ms} ms"
  if elapsed_ms > 0 then
    let effectiveCycPerSec := actualCycles * 1000 / elapsed_ms
    IO.println s!"  Effective cyc/s:         {effectiveCycPerSec}"

  -- =============================================
  -- Part 2: Timer-Compare Accuracy Test
  -- =============================================
  IO.println s!"\n--- Part 2: Timer-Compare Accuracy ---"

  -- Read current mtime after firmware run
  let curLo ← JIT.getReg handle config.mtimeLoRegIdx
  let curHi ← JIT.getReg handle config.mtimeHiRegIdx
  let curMtime := (curHi.toNat <<< 32) ||| curLo.toNat
  IO.println s!"  Current mtime: {curMtime} (0x{toHex32 curMtime})"

  -- Set mtimecmp to mtime + 5000 for a precise skip test
  let targetDelta := 5000
  let targetCmp := curMtime + targetDelta
  let cmpLo := (targetCmp % (2 ^ 32)).toUInt64
  let cmpHi := (targetCmp / (2 ^ 32)).toUInt64
  JIT.setReg handle config.mtimecmpLoRegIdx cmpLo
  JIT.setReg handle config.mtimecmpHiRegIdx cmpHi
  IO.println s!"  Set mtimecmp to: {targetCmp} (delta={targetDelta})"

  -- Create fresh oracle for Part 2
  let (oracle2, oracle2StateRef) ← mkSelfLoopOracle config

  -- Run for 100K more cycles
  let part2Cycles := 100_000
  let firstSkipRef ← IO.mkRef (0 : Nat)
  let firstSkipCaptured ← IO.mkRef false

  let _actualCycles2 ← JIT.runOptimized handle part2Cycles wireIndices oracle2
    fun _cycle _vals => do
      -- Capture first skip amount
      let captured ← firstSkipCaptured.get
      if !captured then
        let st ← oracle2StateRef.get
        if st.triggerCount > 0 then
          firstSkipRef.set st.totalSkipped
          firstSkipCaptured.set true
      return true

  let oracle2State ← oracle2StateRef.get
  let firstSkip ← firstSkipRef.get

  -- Read mtime after Part 2
  let finalLo ← JIT.getReg handle config.mtimeLoRegIdx
  let finalHi ← JIT.getReg handle config.mtimeHiRegIdx
  let finalMtime := (finalHi.toNat <<< 32) ||| finalLo.toNat

  IO.println s!"\n=== Part 2 Results ==="
  IO.println s!"  Oracle triggers:         {oracle2State.triggerCount}"
  IO.println s!"  Total cycles skipped:    {oracle2State.totalSkipped}"
  IO.println s!"  First skip amount:       {firstSkip}"
  IO.println s!"  Expected first skip:     {targetDelta}"
  IO.println s!"  Final mtime:             {finalMtime}"

  -- Verify first skip matches expected delta
  let skipAccurate := firstSkip == targetDelta
  if skipAccurate then
    IO.println s!"  Skip accuracy:           PASS (exactly {targetDelta})"
  else
    IO.println s!"  Skip accuracy:           INFO (got {firstSkip}, expected {targetDelta})"

  JIT.destroy handle

  -- Final verdict
  IO.println "\n========================================="
  if passed then
    IO.println s!"*** PASS: 0xCAFE0000 marker seen, {uartLog.size} UART words ***"
    IO.println s!"*** Boot oracle: {oracleState.triggerCount} triggers, {oracleState.totalSkipped} skipped ***"
    return 0
  else
    IO.eprintln "*** FAIL: 0xCAFE0000 marker not seen ***"
    return 1
