/-
  JIT Dynamic Warp Test — memsetWord + Direct JITHandle Oracle

  Tests two Phase 29 capabilities:
  1. `JIT.memsetWord` bulk memory fill: write 10 words, read back, verify
  2. Dynamic oracle: hand-written closure that receives JITHandle directly,
     reads registers dynamically, and advances CLINT timer via setReg.

  Usage:
    lake exe rv32-jit-dynamic-warp-test [jit.cpp] [firmware.hex] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Utils.HexLoader
import Examples.RV32.SoC

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Utils.HexLoader
open Sparkle.Examples.RV32.SoC

def toHex32 (v : Nat) : String :=
  let hexStr := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[2]? >>= String.toNat?).getD 10_000_000

  IO.println s!"DynamicWarpTest: Compiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "DynamicWarpTest: Loaded JIT module"

  -- ================================================================
  -- Part 1: memsetWord roundtrip test
  -- ================================================================
  IO.println "\n=== Part 1: memsetWord roundtrip ==="

  -- Fill DMEM (memory index 1) addresses 100–109 with 0xAB
  let memIdx : UInt32 := 1
  let baseAddr : UInt32 := 100
  let fillVal : UInt32 := 0xAB
  let fillCount : UInt32 := 10

  JIT.memsetWord handle memIdx baseAddr fillVal fillCount

  -- Read back and verify
  let mut memsetPassed := true
  for i in [:fillCount.toNat] do
    let addr := baseAddr + i.toUInt32
    let readVal ← JIT.getMem handle memIdx addr
    if readVal != fillVal then
      IO.eprintln s!"  FAIL: mem[{addr}] = 0x{toHex32 readVal.toNat}, expected 0x{toHex32 fillVal.toNat}"
      memsetPassed := false

  if memsetPassed then
    IO.println s!"  PASS: All {fillCount} words read back correctly (0x{toHex32 fillVal.toNat})"
  else
    IO.eprintln "  FAIL: memsetWord roundtrip failed"

  -- Reset for Part 2 (memsetWord test ran on fresh state)
  JIT.reset handle

  -- ================================================================
  -- Part 2: Dynamic oracle with direct JITHandle access
  -- ================================================================
  IO.println "\n=== Part 2: Dynamic oracle ==="

  -- Resolve wire indices
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  IO.println s!"DynamicWarpTest: Resolved {wireIndices.size} wire indices"

  -- Load firmware into IMEM (memory index 0)
  IO.println s!"DynamicWarpTest: Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- Oracle config: register indices for CLINT timer
  let mtimeLoRegIdx : UInt32 := 54   -- SoCState field 46 + 8 divider regs
  let mtimeHiRegIdx : UInt32 := 55   -- SoCState field 47 + 8 divider regs
  let pcTolerance : UInt64 := 12
  let threshold : Nat := 50
  let skipAmount : Nat := 1000

  -- Dynamic oracle state (manual, not mkSelfLoopOracle)
  let anchorRef ← IO.mkRef (0xFFFFFFFF_FFFFFFFF : UInt64)
  let countRef ← IO.mkRef (0 : Nat)
  let triggerCountRef ← IO.mkRef (0 : Nat)
  let totalSkippedRef ← IO.mkRef (0 : Nat)

  -- Hand-written oracle closure — demonstrates direct JITHandle access
  let dynamicOracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) :=
    fun h _cycle vals => do
      let pc := vals[0]?.getD 0
      let anchor ← anchorRef.get

      let pcDiff := if pc >= anchor then pc - anchor else anchor - pc
      if pcDiff <= pcTolerance then
        let cnt ← countRef.get
        let newCount := cnt + 1
        countRef.set newCount
        if newCount >= threshold then
          -- Demonstrate dynamic register read via JITHandle
          let _regVal ← JIT.getReg h mtimeLoRegIdx

          -- Read current timer, advance, write back (same as mkSelfLoopOracle)
          let oldLo ← JIT.getReg h mtimeLoRegIdx
          let oldHi ← JIT.getReg h mtimeHiRegIdx
          let sum := oldLo.toNat + skipAmount
          let newLo := (sum % (2 ^ 32)).toUInt64
          let carry : Nat := if sum >= 2 ^ 32 then 1 else 0
          let newHi := (oldHi.toNat + carry).toUInt64
          JIT.setReg h mtimeLoRegIdx newLo
          JIT.setReg h mtimeHiRegIdx newHi

          let tc ← triggerCountRef.get
          triggerCountRef.set (tc + 1)
          let ts ← totalSkippedRef.get
          totalSkippedRef.set (ts + skipAmount)

          return some skipAmount
        else
          return none
      else
        anchorRef.set pc
        countRef.set 0
        return none

  -- Run simulation
  IO.println s!"DynamicWarpTest: Running for {maxCycles} cycles with dynamic oracle..."
  let startTime ← IO.monoNanosNow
  let uartLogRef ← IO.mkRef (#[] : Array UInt64)
  let passedRef ← IO.mkRef false

  let actualCycles ← JIT.runOptimized handle maxCycles wireIndices dynamicOracle
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
  let triggerCount ← triggerCountRef.get
  let totalSkipped ← totalSkippedRef.get

  -- Report
  IO.println s!"\n=== Dynamic Warp Test Results ==="
  IO.println s!"  Part 1 (memsetWord):     {if memsetPassed then "PASS" else "FAIL"}"
  IO.println s!"  Actual cycles executed:  {actualCycles}"
  IO.println s!"  Oracle triggers:         {triggerCount}"
  IO.println s!"  Total cycles skipped:    {totalSkipped}"
  IO.println s!"  UART words captured:     {uartLog.size}"
  IO.println s!"  Wall-clock time:         {elapsed_ms} ms"
  if elapsed_ms > 0 then
    let effectiveCycPerSec := actualCycles * 1000 / elapsed_ms
    IO.println s!"  Effective cyc/s:         {effectiveCycPerSec}"

  JIT.destroy handle

  if passed && memsetPassed && triggerCount > 0 then
    IO.println s!"\n*** PASS: memsetWord OK, 0xCAFE0000 seen, {triggerCount} oracle triggers ***"
    return 0
  else
    if !memsetPassed then IO.eprintln "  FAIL reason: memsetWord roundtrip"
    if !passed then IO.eprintln "  FAIL reason: 0xCAFE0000 marker not seen"
    if triggerCount == 0 then IO.eprintln "  FAIL reason: oracle never triggered"
    return 1
