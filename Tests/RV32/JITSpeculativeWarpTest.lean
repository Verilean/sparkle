/-
  JIT Speculative Warp Test — Snapshot/Restore + Guard-and-Rollback

  Tests Phase 29 speculative simulation with rollback:
  1. Snapshot/Restore roundtrip — proves API correctness
  2. Successful speculative warp (guard passes, no rollback)
  3. Guard failure with rollback (guard fails, state restored)

  Usage:
    lake exe rv32-jit-speculative-warp-test [jit.cpp] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Examples.RV32.SoC

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Examples.RV32.SoC

def toHex32 (v : Nat) : String :=
  let hexStr := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr

/-- Inline RISC-V firmware: BSS-clear loop (7 instructions).
    Zeros 64 words starting at 0x80000000, then halts. -/
private def bssClearFirmware : Array UInt32 :=
  #[ 0x80000537  -- LUI x10, 0x80000
   , 0x04000593  -- ADDI x11, x0, 64
   , 0x00052023  -- SW x0, 0(x10)
   , 0x00450513  -- ADDI x10, x10, 4
   , 0xFFF58593  -- ADDI x11, x11, -1
   , 0xFE059AE3  -- BNE x11, x0, -12
   , 0x0000006F  -- JAL x0, 0 (halt)
   ]

/-- DMEM byte bank memory indices (memIdx 1-4). -/
private def dmemBankIndices : Array UInt32 := #[1, 2, 3, 4]

/-- Load BSS-clear firmware into IMEM (memIdx=0). -/
private def loadFirmware (handle : JITHandle) : IO Unit := do
  for i in [:bssClearFirmware.size] do
    JIT.setMem handle 0 i.toUInt32 bssClearFirmware[i]!

-- Register indices (SoCState field + 8 divider regs offset)
private def pcRegIdx : UInt32 := 8
private def mtimeLoRegIdx : UInt32 := 54
private def mtimeHiRegIdx : UInt32 := 55
private def mtimecmpLoIdx : UInt32 := 56
private def mtimecmpHiIdx : UInt32 := 57

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let maxCycles := (args[1]? >>= String.toNat?).getD 100_000

  IO.println s!"SpeculativeWarpTest: Compiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "SpeculativeWarpTest: Loaded JIT module"

  -- ================================================================
  -- Part 1: Snapshot/Restore Roundtrip
  -- ================================================================
  IO.println "\n=== Part 1: Snapshot/Restore Roundtrip ==="

  -- Load firmware and run 50 cycles
  loadFirmware handle
  for _ in [:50] do
    JIT.eval handle
    JIT.tick handle

  let pc50 ← JIT.getReg handle pcRegIdx
  IO.println s!"  PC after 50 cycles: 0x{toHex32 pc50.toNat}"

  -- Take snapshot
  let snap ← JIT.snapshot handle
  IO.println s!"  Snapshot taken (handle: 0x{toHex32 snap.toNat})"

  -- Run 50 more cycles
  for _ in [:50] do
    JIT.eval handle
    JIT.tick handle

  let pc100 ← JIT.getReg handle pcRegIdx
  IO.println s!"  PC after 100 cycles: 0x{toHex32 pc100.toNat}"

  -- Restore from snapshot
  JIT.restore handle snap
  let pcRestored ← JIT.getReg handle pcRegIdx
  IO.println s!"  PC after restore: 0x{toHex32 pcRestored.toNat}"

  -- Free snapshot
  JIT.freeSnapshot handle snap

  let part1Passed := pcRestored == pc50 && pc50 != pc100
  if part1Passed then
    IO.println s!"  PASS: PC restored to 0x{toHex32 pc50.toNat} (was 0x{toHex32 pc100.toNat})"
  else
    IO.eprintln s!"  FAIL: Expected PC=0x{toHex32 pc50.toNat}, got 0x{toHex32 pcRestored.toNat}"

  -- ================================================================
  -- Part 2: Successful Speculative Warp (Guard Passes)
  -- ================================================================
  IO.println "\n=== Part 2: Speculative Warp (Guard Passes) ==="

  -- Reset and reload
  JIT.reset handle
  loadFirmware handle

  -- Set mtimecmpLo to 0xFFFFFFFF (no interrupt possible)
  JIT.setReg handle mtimecmpLoIdx 0xFFFFFFFF
  JIT.setReg handle mtimecmpHiIdx 0xFFFFFFFF

  -- Pre-fill DMEM with non-zero values
  let numWords : UInt32 := 64
  let prefillValues : Array UInt32 := #[0xEF, 0xBE, 0xAD, 0xDE]
  for bankIdx in [:dmemBankIndices.size] do
    let bMemIdx := dmemBankIndices[bankIdx]!
    let fVal := prefillValues[bankIdx]!
    JIT.memsetWord handle bMemIdx 0 fVal numWords

  -- Resolve wires for oracle
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames

  -- Oracle config
  let pcTolerance : UInt64 := 12
  let threshold : Nat := 10
  let skipAmount : Nat := 256

  -- Oracle state
  let anchorRef ← IO.mkRef (0xFFFFFFFF_FFFFFFFF : UInt64)
  let countRef ← IO.mkRef (0 : Nat)
  let triggerCountRef ← IO.mkRef (0 : Nat)
  let rollbackCountRef ← IO.mkRef (0 : Nat)

  -- Speculative oracle with snapshot/guard/rollback
  let speculativeOracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) :=
    fun h _cycle vals => do
      let pc := vals[0]?.getD 0
      let anchor ← anchorRef.get
      let pcDiff := if pc >= anchor then pc - anchor else anchor - pc
      if pcDiff <= pcTolerance then
        let cnt ← countRef.get
        let newCount := cnt + 1
        countRef.set newCount
        if newCount >= threshold then
          -- Loop detected — take snapshot for rollback
          let s ← JIT.snapshot h

          -- Speculatively apply bulk updates
          for bankMemIdx in dmemBankIndices do
            JIT.memsetWord h bankMemIdx 0 0 numWords

          -- Advance mtime
          let oldLo ← JIT.getReg h mtimeLoRegIdx
          let oldHi ← JIT.getReg h mtimeHiRegIdx
          let sum := oldLo.toNat + skipAmount
          let newLo := (sum % (2 ^ 32)).toUInt64
          let carry : Nat := if sum >= 2 ^ 32 then 1 else 0
          let newHi := (oldHi.toNat + carry).toUInt64
          JIT.setReg h mtimeLoRegIdx newLo
          JIT.setReg h mtimeHiRegIdx newHi

          -- Guard check: mtime < mtimecmp?
          let mtimeLo ← JIT.getReg h mtimeLoRegIdx
          let mtimeHi ← JIT.getReg h mtimeHiRegIdx
          let mcmpLo ← JIT.getReg h mtimecmpLoIdx
          let mcmpHi ← JIT.getReg h mtimecmpHiIdx

          let mtime := (mtimeHi.toNat <<< 32) ||| mtimeLo.toNat
          let mcmp := (mcmpHi.toNat <<< 32) ||| mcmpLo.toNat

          if mtime < mcmp then
            -- Guard passed — free snapshot, accept speculative state
            JIT.freeSnapshot h s
            let tc ← triggerCountRef.get
            triggerCountRef.set (tc + 1)
            return some skipAmount
          else
            -- Guard failed — rollback!
            JIT.restore h s
            JIT.freeSnapshot h s
            let rc ← rollbackCountRef.get
            rollbackCountRef.set (rc + 1)
            return none
        else
          return none
      else
        anchorRef.set pc
        countRef.set 0
        return none

  -- Run simulation
  IO.println s!"  Running for {maxCycles} cycles with speculative oracle..."
  let actualCycles ← JIT.runOptimized handle maxCycles wireIndices speculativeOracle
    fun _cycle _vals => do return true

  -- Verify DMEM zeroed
  let mut dmemZeroed := true
  for bankIdx in [:dmemBankIndices.size] do
    let bMemIdx := dmemBankIndices[bankIdx]!
    for addr in [:numWords.toNat] do
      let val ← JIT.getMem handle bMemIdx addr.toUInt32
      if val != 0 then
        dmemZeroed := false

  let p2Triggers ← triggerCountRef.get
  let p2Rollbacks ← rollbackCountRef.get

  IO.println s!"  Actual cycles: {actualCycles}"
  IO.println s!"  Oracle triggers: {p2Triggers}"
  IO.println s!"  Rollbacks: {p2Rollbacks}"
  IO.println s!"  DMEM zeroed: {dmemZeroed}"

  let part2Passed := dmemZeroed && p2Triggers > 0 && p2Rollbacks == 0
  if part2Passed then
    IO.println "  PASS: Guard passed, no rollbacks, DMEM zeroed"
  else
    IO.eprintln "  FAIL: Speculative warp with passing guard"

  -- ================================================================
  -- Part 3: Guard Failure with Rollback
  -- ================================================================
  IO.println "\n=== Part 3: Guard Failure with Rollback ==="

  -- Reset and reload
  JIT.reset handle
  loadFirmware handle

  -- Set mtimecmpLo very low so interrupt fires quickly
  JIT.setReg handle mtimecmpLoIdx 5
  JIT.setReg handle mtimecmpHiIdx 0

  -- Pre-fill DMEM again
  for bankIdx in [:dmemBankIndices.size] do
    let bMemIdx := dmemBankIndices[bankIdx]!
    let fVal := prefillValues[bankIdx]!
    JIT.memsetWord handle bMemIdx 0 fVal numWords

  -- Reset oracle state
  anchorRef.set 0xFFFFFFFF_FFFFFFFF
  countRef.set 0
  let p3TriggerCountRef ← IO.mkRef (0 : Nat)
  let p3RollbackCountRef ← IO.mkRef (0 : Nat)

  -- Speculative oracle that should fail the guard
  let rollbackOracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) :=
    fun h _cycle vals => do
      let pc := vals[0]?.getD 0
      let anchor ← anchorRef.get
      let pcDiff := if pc >= anchor then pc - anchor else anchor - pc
      if pcDiff <= pcTolerance then
        let cnt ← countRef.get
        let newCount := cnt + 1
        countRef.set newCount
        if newCount >= threshold then
          -- Loop detected — take snapshot
          let s ← JIT.snapshot h

          -- Speculatively: bulk-zero DMEM + advance mtime by large amount
          for bankMemIdx in dmemBankIndices do
            JIT.memsetWord h bankMemIdx 0 0 numWords

          -- Large skip to trigger guard failure
          let largeSkip : Nat := 1000
          let oldLo ← JIT.getReg h mtimeLoRegIdx
          let oldHi ← JIT.getReg h mtimeHiRegIdx
          let sum := oldLo.toNat + largeSkip
          let newLo := (sum % (2 ^ 32)).toUInt64
          let carry : Nat := if sum >= 2 ^ 32 then 1 else 0
          let newHi := (oldHi.toNat + carry).toUInt64
          JIT.setReg h mtimeLoRegIdx newLo
          JIT.setReg h mtimeHiRegIdx newHi

          -- Guard check: mtime < mtimecmp?
          let mtimeLo ← JIT.getReg h mtimeLoRegIdx
          let mtimeHi ← JIT.getReg h mtimeHiRegIdx
          let mcmpLo ← JIT.getReg h mtimecmpLoIdx
          let mcmpHi ← JIT.getReg h mtimecmpHiIdx

          let mtime := (mtimeHi.toNat <<< 32) ||| mtimeLo.toNat
          let mcmp := (mcmpHi.toNat <<< 32) ||| mcmpLo.toNat

          if mtime < mcmp then
            JIT.freeSnapshot h s
            let tc ← p3TriggerCountRef.get
            p3TriggerCountRef.set (tc + 1)
            return some largeSkip
          else
            -- Guard failed — rollback
            JIT.restore h s
            JIT.freeSnapshot h s
            let rc ← p3RollbackCountRef.get
            p3RollbackCountRef.set (rc + 1)
            -- Reset loop detection to prevent infinite rollback loop
            countRef.set 0
            return none
        else
          return none
      else
        anchorRef.set pc
        countRef.set 0
        return none

  IO.println s!"  Running for {maxCycles} cycles with rollback oracle..."
  let p3ActualCycles ← JIT.runOptimized handle maxCycles wireIndices rollbackOracle
    fun _cycle _vals => do return true

  let p3Triggers ← p3TriggerCountRef.get
  let p3Rollbacks ← p3RollbackCountRef.get

  IO.println s!"  Actual cycles: {p3ActualCycles}"
  IO.println s!"  Oracle triggers (guard passed): {p3Triggers}"
  IO.println s!"  Rollbacks (guard failed): {p3Rollbacks}"

  let part3Passed := p3Rollbacks > 0
  if part3Passed then
    IO.println s!"  PASS: {p3Rollbacks} rollback(s) detected"
  else
    IO.eprintln "  FAIL: Expected at least one rollback"

  -- ================================================================
  -- Final Report
  -- ================================================================
  IO.println s!"\n=== Speculative Warp Test Results ==="
  IO.println s!"  Part 1 (Snapshot/Restore):  {if part1Passed then "PASS" else "FAIL"}"
  IO.println s!"  Part 2 (Guard Passes):      {if part2Passed then "PASS" else "FAIL"}"
  IO.println s!"  Part 3 (Guard Rollback):    {if part3Passed then "PASS" else "FAIL"}"

  JIT.destroy handle

  if part1Passed && part2Passed && part3Passed then
    IO.println "\n*** ALL PARTS PASSED ***"
    return 0
  else
    IO.eprintln "\n*** SOME PARTS FAILED ***"
    return 1
