/-
  BitNetLinuxTest — end-to-end "Linux on Sparkle SoC drives the BitNet
  MMIO peripheral via /dev/bitnet0" smoke test.

  Boots the modified Linux 6.6 image (which now contains the in-tree
  `sparkle-bitnet` driver and an initramfs `/init` that exercises 8
  golden vectors against `/dev/bitnet0`) on the Sparkle JIT runner.
  Captures UART output, asserts that:

    1. The driver bound to its DT node:
         "sparkle-bitnet 40000000.bitnet: registered as /dev/bitnet0"
    2. The userspace test passed:
         "BITNET PASS"

  Prerequisites — run once:
    cd firmware/opensbi && bash setup.sh
        (clones Linux 6.6, applies the sparkle-bitnet patch, builds
         a kernel image with CONFIG_SPARKLE_BITNET=y +
         CONFIG_INITRAMFS_SOURCE=usr/initramfs.cpio.gz)
    lake build IP.RV32.SoCVerilog
        (regenerates verilator/generated_soc_jit.cpp)

  Run:
    lake exe bitnet-linux-test [jit.cpp] [max_cycles]

  Returns 0 on PASS, non-zero on missing marker.
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

private def hex32 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

def main (args : List String) : IO UInt32 := do
  let cppPath    := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let maxCycles  := (args[1]? >>= String.toNat?).getD 60_000_000

  let bootHex     ← (·.getD "firmware/opensbi/boot.hex") <$>
                     IO.getEnv "SPARKLE_BOOT_HEX"
  let opensbiPath ← (·.getD "/tmp/opensbi/build/platform/generic/firmware/fw_jump.bin") <$>
                     IO.getEnv "SPARKLE_OPENSBI_BIN"
  let dtbPath     ← (·.getD "firmware/opensbi/sparkle-soc.dtb") <$>
                     IO.getEnv "SPARKLE_DTB"
  let kernelPath  ← (·.getD "/tmp/linux/arch/riscv/boot/Image") <$>
                     IO.getEnv "SPARKLE_KERNEL_IMAGE"

  IO.println "═════════════════════════════════════════════════════════"
  IO.println "  BitNet Linux Driver Test (sparkle,bitnet-v1a)"
  IO.println "═════════════════════════════════════════════════════════"

  for (name, path) in [("boot.hex", bootHex), ("OpenSBI", opensbiPath),
                        ("DTB", dtbPath), ("Linux Image", kernelPath)] do
    unless ← System.FilePath.pathExists path do
      IO.eprintln s!"ERROR: {name} not found at: {path}"
      IO.eprintln "Run: cd firmware/opensbi && bash setup.sh"
      return 2

  IO.println s!"\nCompiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames

  -- Load IMEM (boot.hex)
  let firmware ← loadHex bootHex
  let imemSize := min firmware.size (1 <<< 12)
  for i in [:imemSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- Load DRAM
  let _ ← loadBinaryToDRAM handle opensbiPath 0x000000
  let _ ← loadBinaryToDRAM handle kernelPath  0x100000
  let _ ← loadBinaryToDRAM handle dtbPath     0x3C0000

  -- Self-loop oracle (same config as the existing JITLinuxBootTest).
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
  let (oracle, _oracleStateRef) ← mkSelfLoopOracle config

  let uartBytesRef ← IO.mkRef (#[] : Array UInt8)
  let uartLineRef  ← IO.mkRef ("" : String)
  let registeredRef ← IO.mkRef false
  let passRef ← IO.mkRef false
  let failRef ← IO.mkRef false

  IO.println s!"\nRunning Linux boot for up to {maxCycles} cycles..."
  let startTime ← IO.monoNanosNow
  let _ ← JIT.runOptimized handle maxCycles wireIndices oracle
    fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      if out.uartValid then
        let byte := (out.uartData.toNat % 256).toUInt8
        uartBytesRef.modify (·.push byte)
        let ch := Char.ofNat byte.toNat
        if ch == '\n' then
          let line ← uartLineRef.get
          IO.println line
          if (line.splitOn "sparkle-bitnet").length > 1 &&
             (line.splitOn "registered").length > 1 then
            registeredRef.set true
          if (line.splitOn "BITNET PASS").length > 1 then
            passRef.set true
          if (line.splitOn "BITNET FAIL").length > 1 then
            failRef.set true
          uartLineRef.set ""
        else
          uartLineRef.modify (·.push ch)
      let p ← passRef.get
      if p then return false
      let f ← failRef.get
      if f then return false
      if cycle % 1_000_000 == 0 && cycle > 0 then
        IO.println s!"  [cycle {cycle}] PC=0x{hex32 out.pc.toNat}"
      return true

  let endTime ← IO.monoNanosNow
  let elapsedMs := (endTime - startTime) / 1_000_000
  let registered ← registeredRef.get
  let pass ← passRef.get
  let fail ← failRef.get

  let rem ← uartLineRef.get
  if !rem.isEmpty then IO.println rem

  let yn (b : Bool) : String := if b then "YES" else "no"
  IO.println "\n─────────────────────────────────────────────────────────"
  IO.println s!"  driver registered:    {yn registered}"
  IO.println s!"  userspace BITNET PASS: {yn pass}"
  IO.println s!"  userspace BITNET FAIL: {yn fail}"
  IO.println s!"  wall-clock:           {elapsedMs} ms"
  IO.println "─────────────────────────────────────────────────────────"

  JIT.destroy handle

  if pass && registered then
    IO.println "\n✅ BitNet Linux driver test: PASS"
    return 0
  else
    IO.eprintln "\n❌ BitNet Linux driver test: FAIL"
    if !registered then
      IO.eprintln "    missing  'sparkle-bitnet … registered'  marker"
    if !pass then
      IO.eprintln "    missing  'BITNET PASS'  marker"
    if fail then
      IO.eprintln "    saw      'BITNET FAIL'  marker"
    return 1
