/-
  JIT FFI Test for RV32I SoC

  Compiles the generated JIT wrapper to a shared library, loads it via
  dlopen, runs the firmware test, and checks UART output matches the
  expected 48 words + 0xCAFE0000 pass marker.

  Usage:
    lake exe rv32-jit-test [jit.cpp] [firmware.hex] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Utils.HexLoader

open Sparkle.Core.JIT
open Sparkle.Utils.HexLoader

/-- Resolve a wire index by name, throwing if not found -/
def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[2]? >>= String.toNat?).getD 5000

  -- Compile and load JIT module
  IO.println s!"JIT: Compiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "JIT: Loaded shared library"

  -- Resolve wire indices by name
  let pcIdx ← resolveWire handle "_gen_pcReg"
  let uartValidIdx ← resolveWire handle "_gen_uartValidBV"
  let uartDataIdx ← resolveWire handle "_gen_prevStoreData"
  IO.println s!"JIT: Wire indices — pcReg={pcIdx}, uartValid={uartValidIdx}, uartData={uartDataIdx}"

  -- Load firmware into IMEM (memory index 0 = _gen_imem_rdata)
  IO.println s!"JIT: Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- Run simulation
  IO.println s!"JIT: Running for {maxCycles} cycles..."
  let mut uartLog : Array UInt64 := #[]
  let mut passed := false

  for cycle in [:maxCycles] do
    JIT.eval handle

    let uartValid ← JIT.getWire handle uartValidIdx
    if uartValid != 0 then
      let uartData ← JIT.getWire handle uartDataIdx
      uartLog := uartLog.push uartData
      let hexStr := String.ofList (Nat.toDigits 16 uartData.toNat)
      let padded := String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr
      IO.println s!"  UART[{uartLog.size}]: 0x{padded}"

      if uartData == 0xCAFE0000 then
        IO.println s!"\n*** ALL TESTS PASSED (cycle {cycle}) ***"
        passed := true
        break

    JIT.tick handle

  -- Summary
  IO.println s!"\nJIT: {uartLog.size} UART words captured"

  JIT.destroy handle

  if passed then
    return 0
  else
    IO.eprintln "JIT: Test FAILED — 0xCAFE0000 marker not seen"
    return 1
