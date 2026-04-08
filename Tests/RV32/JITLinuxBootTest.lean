/-
  JIT Linux Boot Test — OpenSBI + Linux 6.6 on Sparkle RV32IMA SoC

  Loads OpenSBI fw_jump.bin + DTB + Linux kernel Image into DRAM via JIT,
  boots with timer-compare oracle, and monitors UART text output.

  Prerequisites:
    cd firmware/opensbi && bash setup.sh

  Usage:
    lake exe rv32-jit-linux-boot-test [jit.cpp] [max_cycles]
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
  let maxCycles := (args[1]? >>= String.toNat?).getD 100_000_000

  -- Firmware paths (configurable via env vars)
  let bootHex ← do
    match ← IO.getEnv "SPARKLE_BOOT_HEX" with
    | some p => pure p
    | none   => pure "firmware/opensbi/boot.hex"
  let opensbiPath ← do
    match ← IO.getEnv "SPARKLE_OPENSBI_BIN" with
    | some p => pure p
    | none   => pure "/tmp/opensbi/build/platform/generic/firmware/fw_jump.bin"
  let dtbPath ← do
    match ← IO.getEnv "SPARKLE_DTB" with
    | some p => pure p
    | none   => pure "firmware/opensbi/sparkle-soc.dtb"
  let kernelPath ← do
    match ← IO.getEnv "SPARKLE_KERNEL_IMAGE" with
    | some p => pure p
    | none   => pure "/tmp/linux/arch/riscv/boot/Image"

  IO.println "============================================="
  IO.println "  JIT Linux Boot Test — OpenSBI + Linux 6.6"
  IO.println "============================================="

  -- Check firmware files exist
  for (name, path) in [("boot.hex", bootHex), ("OpenSBI", opensbiPath),
                        ("DTB", dtbPath), ("Linux Image", kernelPath)] do
    unless ← System.FilePath.pathExists path do
      IO.eprintln s!"ERROR: {name} not found at: {path}"
      IO.eprintln "Run: cd firmware/opensbi && bash setup.sh"
      return 1

  -- Compile and load JIT
  IO.println s!"\nCompiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "Loaded JIT module"

  -- Resolve wire indices
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  IO.println s!"Resolved {wireIndices.size} wire indices"

  -- Load boot.hex into IMEM (memory index 0)
  IO.println s!"\nLoading {bootHex} into IMEM..."
  let firmware ← loadHex bootHex
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32
  IO.println s!"  {memSize} words loaded into IMEM"

  -- Load OpenSBI fw_jump.bin into DRAM @ 0x80000000 → word addr 0x000000
  IO.println s!"Loading {opensbiPath} into DRAM @ 0x000000..."
  let opensbiWords ← loadBinaryToDRAM handle opensbiPath 0x000000
  IO.println s!"  {opensbiWords} words loaded"

  -- Load Linux kernel into DRAM @ 0x80400000 → word addr 0x100000
  -- DRAM is 8M words (32MB). Kernel at word 0x100000 can use up to 7M words (28MB).
  IO.println s!"Loading {kernelPath} into DRAM @ 0x100000..."
  let kernelBytes ← IO.FS.readBinFile kernelPath
  let kernelTotalWords := (kernelBytes.size + 3) / 4
  let kernelWords ← loadBinaryToDRAM handle kernelPath 0x100000
  IO.println s!"  {kernelWords} words loaded (file: {kernelTotalWords} words, {kernelBytes.size} bytes)"
  if kernelWords < kernelTotalWords then
    IO.println s!"  WARNING: Kernel truncated! {kernelTotalWords - kernelWords} words did not fit in DRAM"

  -- Load DTB into DRAM @ 0x80F00000 → word addr 0x3C0000
  -- MUST be loaded AFTER kernel — kernel at 0x100000 extends to 0x800000 and overlaps DTB region
  IO.println s!"Loading {dtbPath} into DRAM @ 0x3C0000..."
  let dtbWords ← loadBinaryToDRAM handle dtbPath 0x3C0000
  IO.println s!"  {dtbWords} words loaded"

  -- Verify DRAM loading by reading back first 8 words from ifetch byte lanes
  IO.println "\n--- Memory Readback Verification ---"
  IO.println "First 8 words from DRAM ifetch byte lanes (should match OpenSBI entry):"
  let opensbiBytes ← IO.FS.readBinFile opensbiPath
  for i in [:8] do
    let b0 ← JIT.getMem handle 7  i.toUInt32
    let b1 ← JIT.getMem handle 8  i.toUInt32
    let b2 ← JIT.getMem handle 9  i.toUInt32
    let b3 ← JIT.getMem handle 10 i.toUInt32
    let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
    -- Compare with actual file bytes
    let fb0 := if h : 4*i < opensbiBytes.size then opensbiBytes[4*i].toNat else 0
    let fb1 := if h : 4*i+1 < opensbiBytes.size then opensbiBytes[4*i+1].toNat else 0
    let fb2 := if h : 4*i+2 < opensbiBytes.size then opensbiBytes[4*i+2].toNat else 0
    let fb3 := if h : 4*i+3 < opensbiBytes.size then opensbiBytes[4*i+3].toNat else 0
    let fileWord := (fb3 <<< 24) ||| (fb2 <<< 16) ||| (fb1 <<< 8) ||| fb0
    let match_ := if word == fileWord then "OK" else "MISMATCH"
    IO.println s!"  word[{i}]: ifetch=0x{toHex32 word} file=0x{toHex32 fileWord} {match_}"

  IO.println "\nFirst 8 words from DRAM data byte lanes:"
  for i in [:8] do
    let b0 ← JIT.getMem handle 1 i.toUInt32
    let b1 ← JIT.getMem handle 2 i.toUInt32
    let b2 ← JIT.getMem handle 3 i.toUInt32
    let b3 ← JIT.getMem handle 4 i.toUInt32
    let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
    IO.println s!"  word[{i}]: data=0x{toHex32 word}"

  -- Verify DTB at word address 0x3C0000
  IO.println "\nFirst 4 words from DTB region (DRAM data @ 0x3C0000, should match DTB header):"
  let dtbBytes ← IO.FS.readBinFile dtbPath
  for i in [:4] do
    let addr := (0x3C0000 + i).toUInt32
    let b0 ← JIT.getMem handle 1 addr
    let b1 ← JIT.getMem handle 2 addr
    let b2 ← JIT.getMem handle 3 addr
    let b3 ← JIT.getMem handle 4 addr
    let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
    let fb0 := if h : 4*i < dtbBytes.size then dtbBytes[4*i].toNat else 0
    let fb1 := if h : 4*i+1 < dtbBytes.size then dtbBytes[4*i+1].toNat else 0
    let fb2 := if h : 4*i+2 < dtbBytes.size then dtbBytes[4*i+2].toNat else 0
    let fb3 := if h : 4*i+3 < dtbBytes.size then dtbBytes[4*i+3].toNat else 0
    let fileWord := (fb3 <<< 24) ||| (fb2 <<< 16) ||| (fb1 <<< 8) ||| fb0
    let match_ := if word == fileWord then "OK" else "MISMATCH"
    IO.println s!"  dtb[{i}]: data=0x{toHex32 word} file=0x{toHex32 fileWord} {match_}"

  IO.println "\nFirst 4 words from IMEM:"
  for i in [:4] do
    let word ← JIT.getMem handle 0 i.toUInt32
    IO.println s!"  imem[{i}]: 0x{toHex32 word.toNat}"

  let uartBytesRef ← IO.mkRef (#[] : Array UInt8)
  let uartLineRef ← IO.mkRef ("" : String)

  -- Create boot oracle with timer-compare skipping
  let config : SelfLoopConfig := {
    threshold := 200
    skipAmount := 1000
    pcWireArrayIdx := 0
    mtimeLoRegIdx := 54
    mtimeHiRegIdx := 55
    mtimecmpLoRegIdx := 56
    mtimecmpHiRegIdx := 57
    skipToTimerCompare := true
    maxSkip := 10_000_000
    pcTolerance := 8
  }
  let (oracle, oracleStateRef) ← mkSelfLoopOracle config

  -- The self-loop oracle uses threshold=50, so only loops executing the same PC
  -- for 50+ consecutive cycles get skipped.  OpenSBI's productive init loops have
  -- varying PCs and won't trigger.  The WFI idle loop is the target for skipping.
  IO.println s!"\nOracle active from cycle 0 (threshold={config.threshold}, maxSkip={config.maxSkip})"

  -- Early-cycle PC trace (first 20 cycles)
  IO.println "\n--- Early-Cycle PC Trace ---"
  let earlyTraceRef ← IO.mkRef (#[] : Array (Nat × Nat))
  let _traceRun ← JIT.runOptimized handle 20 wireIndices
    (fun _ _ _ => pure none)
    fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      let trace ← earlyTraceRef.get
      earlyTraceRef.set (trace.push (cycle, out.pc.toNat))
      return true
  let earlyTrace ← earlyTraceRef.get
  for (c, pc) in earlyTrace do
    IO.println s!"  cycle {c}: PC=0x{toHex32 pc}"

  -- Reset JIT for main run (reload memories)
  JIT.reset handle
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32
  let _opensbiWords2 ← loadBinaryToDRAM handle opensbiPath 0x000000
  let _kernelWords2 ← loadBinaryToDRAM handle kernelPath 0x100000
  let _dtbWords2 ← loadBinaryToDRAM handle dtbPath 0x3C0000

  -- Run simulation
  IO.println s!"\nRunning JIT Linux boot for {maxCycles} cycles...\n"
  let startTime ← IO.monoNanosNow

  let actualCycles ← JIT.runOptimized handle maxCycles wireIndices oracle
    fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      if out.uartValid then
        let byte := (out.uartData.toNat % 256).toUInt8
        let bytes ← uartBytesRef.get
        uartBytesRef.set (bytes.push byte)
        -- Accumulate line, print on newline
        let ch := Char.ofNat byte.toNat
        if ch == '\n' then
          let line ← uartLineRef.get
          IO.println line
          uartLineRef.set ""
        else
          let line ← uartLineRef.get
          uartLineRef.set (line.push ch)
      -- Periodically report PC for progress
      if cycle < 1_000_000 then
        if cycle % 100_000 == 0 then
          IO.println s!"  [cycle {cycle}] PC=0x{toHex32 out.pc.toNat}"
          -- Print timer state at 100K for diagnostics
          if cycle == 100_000 then
            let mtimeLo ← JIT.getReg handle 54
            let mtimeHi ← JIT.getReg handle 55
            let mtimecmpLo ← JIT.getReg handle 56
            let mtimecmpHi ← JIT.getReg handle 57
            let mstatusReg ← JIT.getReg handle 58
            let mieReg ← JIT.getReg handle 59
            IO.println s!"    mtime=0x{toHex32 mtimeHi.toNat}{toHex32 mtimeLo.toNat}"
            IO.println s!"    mtimecmp=0x{toHex32 mtimecmpHi.toNat}{toHex32 mtimecmpLo.toNat}"
            IO.println s!"    mstatus=0x{toHex32 mstatusReg.toNat} mie=0x{toHex32 mieReg.toNat}"
      else if cycle % 1_000_000 == 0 then
        IO.println s!"  [cycle {cycle}] PC=0x{toHex32 out.pc.toNat}"
        -- Print timer state at 3M, 5M, 10M for post-kernel diagnostics
        if cycle == 3_000_000 || cycle == 5_000_000 || cycle == 10_000_000 then
          let mtimeLo ← JIT.getReg handle 54
          let mtimeHi ← JIT.getReg handle 55
          let mtimecmpLo ← JIT.getReg handle 56
          let mtimecmpHi ← JIT.getReg handle 57
          let mstatusReg ← JIT.getReg handle 58
          let mieReg ← JIT.getReg handle 59
          IO.println s!"    mtime=0x{toHex32 mtimeHi.toNat}{toHex32 mtimeLo.toNat}"
          IO.println s!"    mtimecmp=0x{toHex32 mtimecmpHi.toNat}{toHex32 mtimecmpLo.toNat}"
          IO.println s!"    mstatus=0x{toHex32 mstatusReg.toNat} mie=0x{toHex32 mieReg.toNat}"
      return true

  let endTime ← IO.monoNanosNow
  let elapsed_ms := (endTime - startTime) / 1_000_000

  -- Flush any remaining partial line
  let remainingLine ← uartLineRef.get
  if !remainingLine.isEmpty then
    IO.println remainingLine

  -- Gather results
  let uartBytes ← uartBytesRef.get
  let oracleState ← oracleStateRef.get

  -- Report
  IO.println "\n============================================="
  IO.println "  JIT Linux Boot Results"
  IO.println "============================================="
  IO.println s!"  Cycles executed:   {actualCycles}"
  IO.println s!"  Oracle triggers:   {oracleState.triggerCount}"
  IO.println s!"  Total skipped:     {oracleState.totalSkipped}"
  IO.println s!"  UART bytes:        {uartBytes.size}"
  IO.println s!"  Wall-clock time:   {elapsed_ms} ms"
  if elapsed_ms > 0 then
    let effectiveCycPerSec := actualCycles * 1000 / elapsed_ms
    IO.println s!"  Effective cyc/s:   {effectiveCycPerSec}"

  JIT.destroy handle
  return 0
