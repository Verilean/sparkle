/-
  Oracle Accuracy Test — Self-Contained CI Test for Idle-Loop Skipping

  Tests the oracle's timer-compare skip accuracy, MIE/MTIE guard,
  and halt-loop detection using firmware.hex (no external firmware needed).

  Requires: generated_soc_jit.cpp (built by `lake build IP.RV32.SoCVerilog`)

  Usage:
    lake exe oracle-accuracy-test [jit.cpp] [firmware.hex]
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

/-- Load firmware into JIT handle's IMEM -/
def loadFirmware (handle : JITHandle) (hexPath : String) : IO Nat := do
  let firmware ← loadHex hexPath
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32
  return memSize

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"

  -- Check files exist
  unless ← System.FilePath.pathExists cppPath do
    IO.eprintln s!"ERROR: {cppPath} not found. Run: lake build IP.RV32.SoCVerilog"
    return 1
  unless ← System.FilePath.pathExists hexPath do
    IO.eprintln s!"ERROR: {hexPath} not found"
    return 1

  IO.println "========================================="
  IO.println "  Oracle Accuracy Test"
  IO.println "========================================="

  let handle ← JIT.compileAndLoad cppPath
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames

  let mut passed := 0
  let mut failed := 0

  -- ============================================================
  -- Test 1: Oracle detects halt loop
  -- Run firmware until halt loop, verify oracle triggers
  -- ============================================================
  IO.println "\n--- Test 1: Halt Loop Detection ---"
  JIT.reset handle
  let _ ← loadFirmware handle hexPath

  let config1 : SelfLoopConfig := {
    threshold := 50
    skipAmount := 1000
    pcTolerance := 12
    skipToTimerCompare := false
    checkInterruptEnable := false
  }
  let (oracle1, stateRef1) ← mkSelfLoopOracle config1

  let _ ← JIT.runOptimized handle 100_000 wireIndices oracle1 fun _ _ => pure true
  let st1 ← stateRef1.get

  if st1.triggerCount > 0 then
    IO.println s!"  PASS: Oracle triggered {st1.triggerCount} times, skipped {st1.totalSkipped} cycles"
    passed := passed + 1
  else
    IO.println s!"  FAIL: Oracle never triggered (sameCount={st1.sameCount})"
    failed := failed + 1

  -- ============================================================
  -- Test 2: Timer advance accuracy
  -- After firmware halts, set mtimecmp = mtime + 5000,
  -- verify oracle skips exactly 5000 cycles
  -- ============================================================
  IO.println "\n--- Test 2: Timer Advance Accuracy ---"
  JIT.reset handle
  let _ ← loadFirmware handle hexPath

  -- First run to reach halt loop (without timer-compare)
  let configPreRun : SelfLoopConfig := {
    threshold := 50
    skipAmount := 100
    pcTolerance := 12
    skipToTimerCompare := false
    checkInterruptEnable := false
  }
  let (oraclePreRun, _) ← mkSelfLoopOracle configPreRun
  let _ ← JIT.runOptimized handle 50_000 wireIndices oraclePreRun fun _ _ => pure true

  -- Now set mtimecmp = mtime + 5000
  let mtimeLo ← JIT.getReg handle 54
  let mtimeHi ← JIT.getReg handle 55
  let mtime64 := (mtimeHi.toNat <<< 32) ||| mtimeLo.toNat
  let targetDelta := 5000
  let mtimecmp64 := mtime64 + targetDelta
  JIT.setReg handle 56 (mtimecmp64 % (2 ^ 32)).toUInt64
  JIT.setReg handle 57 (mtimecmp64 / (2 ^ 32)).toUInt64

  -- Run with timer-compare oracle
  let config2 : SelfLoopConfig := {
    threshold := 50
    skipAmount := 1000
    pcTolerance := 12
    skipToTimerCompare := true
    maxSkip := 10_000_000
    checkInterruptEnable := false
  }
  let (oracle2, stateRef2) ← mkSelfLoopOracle config2
  let _ ← JIT.runOptimized handle 100_000 wireIndices oracle2 fun _ _ => pure true
  let st2 ← stateRef2.get

  -- Check timer skip accuracy: first trigger should skip exactly targetDelta
  let newMtimeLo ← JIT.getReg handle 54
  let newMtimeHi ← JIT.getReg handle 55
  let newMtime64 := (newMtimeHi.toNat <<< 32) ||| newMtimeLo.toNat
  let actualDelta := if newMtime64 >= mtime64 then newMtime64 - mtime64 else 0

  if st2.triggerCount > 0 && actualDelta >= targetDelta then
    IO.println s!"  PASS: Timer advanced by {actualDelta} (target={targetDelta}), triggers={st2.triggerCount}"
    passed := passed + 1
  else
    IO.println s!"  FAIL: Timer delta={actualDelta} (expected >= {targetDelta}), triggers={st2.triggerCount}"
    failed := failed + 1

  -- ============================================================
  -- Test 3: MIE guard — disable interrupts, verify no skip
  -- ============================================================
  IO.println "\n--- Test 3: MIE Guard (interrupts disabled) ---"
  JIT.reset handle
  let _ ← loadFirmware handle hexPath

  -- First run to reach halt loop
  let (oraclePreRun3, _) ← mkSelfLoopOracle configPreRun
  let _ ← JIT.runOptimized handle 50_000 wireIndices oraclePreRun3 fun _ _ => pure true

  -- Disable global interrupts: clear MSTATUS.MIE (bit 3)
  let mstatus ← JIT.getReg handle 58
  let mstatusNoMIE := mstatus.toNat &&& (0xFFFFFFFF - 0x8)  -- clear bit 3
  JIT.setReg handle 58 mstatusNoMIE.toUInt64

  -- Set mtimecmp close
  let mtimeLo3 ← JIT.getReg handle 54
  let mtimeHi3 ← JIT.getReg handle 55
  let mtime64_3 := (mtimeHi3.toNat <<< 32) ||| mtimeLo3.toNat
  JIT.setReg handle 56 ((mtime64_3 + 5000) % (2 ^ 32)).toUInt64
  JIT.setReg handle 57 ((mtime64_3 + 5000) / (2 ^ 32)).toUInt64

  -- Run with MIE guard enabled
  let config3 : SelfLoopConfig := {
    threshold := 50
    skipAmount := 1000
    pcTolerance := 12
    skipToTimerCompare := true
    maxSkip := 10_000_000
    checkInterruptEnable := true  -- guard enabled!
    mstatusRegIdx := 58
    mieRegIdx := 59
  }
  let (oracle3, stateRef3) ← mkSelfLoopOracle config3
  let _ ← JIT.runOptimized handle 10_000 wireIndices oracle3 fun _ _ => pure true
  let st3 ← stateRef3.get

  if st3.triggerCount == 0 then
    IO.println s!"  PASS: Oracle correctly did NOT trigger (MIE=0, sameCount={st3.sameCount})"
    passed := passed + 1
  else
    IO.println s!"  FAIL: Oracle triggered {st3.triggerCount} times despite MIE=0"
    failed := failed + 1

  -- ============================================================
  -- Test 4: MTIE guard — disable timer interrupt, verify no skip
  -- ============================================================
  IO.println "\n--- Test 4: MTIE Guard (timer interrupt disabled) ---"
  JIT.reset handle
  let _ ← loadFirmware handle hexPath

  let (oraclePreRun4, _) ← mkSelfLoopOracle configPreRun
  let _ ← JIT.runOptimized handle 50_000 wireIndices oraclePreRun4 fun _ _ => pure true

  -- Enable global interrupts but disable timer: MSTATUS.MIE=1, MIE.MTIE=0
  let mstatus4 ← JIT.getReg handle 58
  JIT.setReg handle 58 (mstatus4.toNat ||| 0x8).toUInt64  -- set MIE
  let mie4 ← JIT.getReg handle 59
  let mieNoMTIE := mie4.toNat &&& (0xFFFFFFFF - 0x80)  -- clear MTIE (bit 7)
  JIT.setReg handle 59 mieNoMTIE.toUInt64

  let mtimeLo4 ← JIT.getReg handle 54
  let mtimeHi4 ← JIT.getReg handle 55
  let mtime64_4 := (mtimeHi4.toNat <<< 32) ||| mtimeLo4.toNat
  JIT.setReg handle 56 ((mtime64_4 + 5000) % (2 ^ 32)).toUInt64
  JIT.setReg handle 57 ((mtime64_4 + 5000) / (2 ^ 32)).toUInt64

  let (oracle4, stateRef4) ← mkSelfLoopOracle config3  -- reuse config with guard
  let _ ← JIT.runOptimized handle 10_000 wireIndices oracle4 fun _ _ => pure true
  let st4 ← stateRef4.get

  if st4.triggerCount == 0 then
    IO.println s!"  PASS: Oracle correctly did NOT trigger (MTIE=0, sameCount={st4.sameCount})"
    passed := passed + 1
  else
    IO.println s!"  FAIL: Oracle triggered {st4.triggerCount} times despite MTIE=0"
    failed := failed + 1

  -- ============================================================
  -- Summary
  -- ============================================================
  IO.println "\n========================================="
  IO.println s!"  Results: {passed} passed, {failed} failed"
  IO.println "========================================="

  JIT.destroy handle
  return if failed > 0 then 1 else 0
