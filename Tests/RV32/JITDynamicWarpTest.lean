/-
  JIT Dynamic Warp Test — memsetWord + BSS-Clear Speculative Warp

  Tests two Phase 29 capabilities:
  1. `JIT.memsetWord` bulk memory fill: write 10 words, read back, verify
  2. BSS-clear speculative warp: inline firmware simulating a BSS-clear loop,
     oracle detects the loop, bulk-zeros all 4 DMEM byte banks via memsetWord,
     advances CLINT timer, and skips cycles — demonstrating high effective cyc/s.

  Usage:
    lake exe rv32-jit-dynamic-warp-test [jit.cpp] [max_cycles]
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
    Zeros 64 words starting at 0x80000000, then halts.

    Word 0: LUI   x10, 0x80000       -- a0 = 0x80000000 (DRAM base)
    Word 1: ADDI  x11, x0, 64        -- a1 = 64 (words to clear)
    Word 2: SW    x0, 0(x10)          -- *a0 = 0  (loop body)
    Word 3: ADDI  x10, x10, 4         -- a0 += 4
    Word 4: ADDI  x11, x11, -1        -- a1 -= 1
    Word 5: BNE   x11, x0, -12        -- if a1 != 0, goto Word 2
    Word 6: JAL   x0, 0               -- halt (self-loop) -/
private def bssClearFirmware : Array UInt32 :=
  #[ 0x80000537  -- LUI x10, 0x80000
   , 0x04000593  -- ADDI x11, x0, 64
   , 0x00052023  -- SW x0, 0(x10)
   , 0x00450513  -- ADDI x10, x10, 4
   , 0xFFF58593  -- ADDI x11, x11, -1
   , 0xFE059AE3  -- BNE x11, x0, -12
   , 0x0000006F  -- JAL x0, 0 (halt)
   ]

/-- DMEM byte bank memory indices.
    The SoC uses 4 separate byte-wide Signal.memory banks for DMEM:
      memIdx 1 = byte0 (bits 7:0)
      memIdx 2 = byte1 (bits 15:8)
      memIdx 3 = byte2 (bits 23:16)
      memIdx 4 = byte3 (bits 31:24)
    IMEM is memIdx 0. -/
private def dmemBankIndices : Array UInt32 := #[1, 2, 3, 4]

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let maxCycles := (args[1]? >>= String.toNat?).getD 100_000

  IO.println s!"DynamicWarpTest: Compiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "DynamicWarpTest: Loaded JIT module"

  -- ================================================================
  -- Part 1: memsetWord roundtrip test
  -- ================================================================
  IO.println "\n=== Part 1: memsetWord roundtrip ==="

  -- Fill DMEM byte bank 0 (memory index 1) addresses 100–109 with 0xAB
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

  -- ================================================================
  -- Part 2: BSS-Clear Speculative Warp
  -- ================================================================
  IO.println "\n=== Part 2: BSS-Clear Speculative Warp ==="

  -- Reset for Part 2 (clear Part 1 state)
  JIT.reset handle

  -- 2a. Load inline firmware into IMEM (memIdx=0)
  IO.println "  Loading BSS-clear firmware (7 instructions)..."
  for i in [:bssClearFirmware.size] do
    let word := bssClearFirmware[i]!
    JIT.setMem handle 0 i.toUInt32 word

  -- 2b. Pre-fill DMEM byte banks with non-zero values at addrs 0-63
  --     Each bank gets a different byte so we can verify individual banks
  IO.println "  Pre-filling DMEM byte banks at addrs 0-63..."
  let prefillValues : Array UInt32 := #[0xEF, 0xBE, 0xAD, 0xDE]
  let numWords : UInt32 := 64

  for bankIdx in [:dmemBankIndices.size] do
    let bMemIdx := dmemBankIndices[bankIdx]!
    let fVal := prefillValues[bankIdx]!
    JIT.memsetWord handle bMemIdx 0 fVal numWords

  -- Verify pre-fill
  let mut prefillOk := true
  for bankIdx in [:dmemBankIndices.size] do
    let bMemIdx := dmemBankIndices[bankIdx]!
    let expected := prefillValues[bankIdx]!
    for addr in [:numWords.toNat] do
      let val ← JIT.getMem handle bMemIdx addr.toUInt32
      if val != expected then
        prefillOk := false
  if prefillOk then
    IO.println "  Pre-fill verified (0xDEADBEEF across 4 banks × 64 words)"
  else
    IO.eprintln "  WARNING: Pre-fill verification failed"

  -- 2c. Resolve wires for oracle (need _gen_pcReg at index 0)
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  IO.println s!"  Resolved {wireIndices.size} wire indices"

  -- 2d. Oracle config
  let pcRegIdx : UInt32 := 8       -- SoCState field 0 (pcReg), offset by 8 divider regs
  let mtimeLoRegIdx : UInt32 := 54 -- SoCState field 46 + 8 divider regs
  let mtimeHiRegIdx : UInt32 := 55 -- SoCState field 47 + 8 divider regs
  let pcTolerance : UInt64 := 12   -- Covers 4-instruction loop (0x08..0x14)
  let threshold : Nat := 10
  let skipAmount : Nat := 256      -- 64 iterations × ~4 cyc/iter

  -- Oracle state
  let anchorRef ← IO.mkRef (0xFFFFFFFF_FFFFFFFF : UInt64)
  let countRef ← IO.mkRef (0 : Nat)
  let triggerCountRef ← IO.mkRef (0 : Nat)
  let totalSkippedRef ← IO.mkRef (0 : Nat)

  -- BSS-clear oracle: detects the BSS-clear loop, bulk-zeros DMEM, skips cycles
  let bssClearOracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) :=
    fun h _cycle vals => do
      let pc := vals[0]?.getD 0
      let anchor ← anchorRef.get

      let pcDiff := if pc >= anchor then pc - anchor else anchor - pc
      if pcDiff <= pcTolerance then
        let cnt ← countRef.get
        let newCount := cnt + 1
        countRef.set newCount
        if newCount >= threshold then
          -- BSS-clear loop detected!

          -- Demonstrate dynamic register read (pcReg)
          let _pcVal ← JIT.getReg h pcRegIdx

          -- Bulk-zero all 4 DMEM byte banks at addresses 0-63
          for bankMemIdx in dmemBankIndices do
            JIT.memsetWord h bankMemIdx 0 0 numWords

          -- Advance CLINT timer
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

  -- 2e. Run simulation
  IO.println s!"  Running for {maxCycles} cycles with BSS-clear oracle..."
  let startTime ← IO.monoNanosNow

  let actualCycles ← JIT.runOptimized handle maxCycles wireIndices bssClearOracle
    fun _cycle _vals => do
      return true  -- always continue (oracle handles loop detection)

  let endTime ← IO.monoNanosNow
  let elapsed_ms := (endTime - startTime) / 1_000_000

  -- 2f. Verify DMEM byte banks are zeroed at addresses 0-63
  let mut dmemZeroed := true
  let mut nonZeroCount : Nat := 0
  for bankIdx in [:dmemBankIndices.size] do
    let bMemIdx := dmemBankIndices[bankIdx]!
    for addr in [:numWords.toNat] do
      let val ← JIT.getMem handle bMemIdx addr.toUInt32
      if val != 0 then
        dmemZeroed := false
        nonZeroCount := nonZeroCount + 1
        if nonZeroCount <= 5 then
          IO.eprintln s!"  FAIL: bank {bankIdx} addr {addr} = 0x{toHex32 val.toNat} (expected 0)"

  -- 2g. Read final PC (informational — CPU may not have reached halt
  --     since oracle skips without ticking)
  let finalPC ← JIT.getReg handle pcRegIdx

  -- Gather results
  let triggerCount ← triggerCountRef.get
  let totalSkipped ← totalSkippedRef.get

  -- ================================================================
  -- Report
  -- ================================================================
  IO.println s!"\n=== Dynamic Warp Test Results ==="
  IO.println s!"  Part 1 (memsetWord):       {if memsetPassed then "PASS" else "FAIL"}"
  IO.println s!"  Part 2 (BSS-clear warp):"
  IO.println s!"    DMEM zeroed:             {if dmemZeroed then "PASS" else s!"FAIL ({nonZeroCount} non-zero)"}"
  IO.println s!"    Oracle triggers:         {triggerCount}"
  IO.println s!"    Total cycles skipped:    {totalSkipped}"
  IO.println s!"    Actual cycle count:      {actualCycles}"
  IO.println s!"    Final PC:                0x{toHex32 finalPC.toNat}"
  IO.println s!"    Wall-clock time:         {elapsed_ms} ms"
  if elapsed_ms > 0 then
    let effectiveCycPerSec := actualCycles * 1000 / elapsed_ms
    IO.println s!"    Effective cyc/s:         {effectiveCycPerSec}"

  JIT.destroy handle

  let part2Passed := dmemZeroed && triggerCount > 0

  if memsetPassed && part2Passed then
    IO.println s!"\n*** PASS: memsetWord OK, DMEM zeroed, {triggerCount} oracle triggers ***"
    return 0
  else
    if !memsetPassed then IO.eprintln "  FAIL reason: memsetWord roundtrip"
    if !dmemZeroed then IO.eprintln "  FAIL reason: DMEM not fully zeroed"
    if triggerCount == 0 then IO.eprintln "  FAIL reason: oracle never triggered"
    return 1
