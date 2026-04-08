/-
  JITLoop Test for RV32I SoC

  Tests the loopMemoJIT and JIT.run APIs using named output wires.

  Part 1: Signal API — uses loopMemoJIT → Signal dom SoCOutput,
          reads PC and UART via SoCOutput struct accessors.

  Part 2: Streaming API — uses rv32iSoCJITRun with per-cycle callback,
          O(1) memory for long simulations.

  Both use `JIT.getWire` with named output wires (stable, immune to DCE).

  Usage:
    lake exe rv32-jit-loop-test [jit.cpp] [firmware.hex] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Utils.HexLoader
import IP.RV32.SoC

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Utils.HexLoader
open Sparkle.IP.RV32.SoC

def toHex32 (v : Nat) : String :=
  let hexStr := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[2]? >>= String.toNat?).getD 5000

  IO.println s!"JITLoop: Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath

  -- ================================================================
  -- Part 1: Signal API test (loopMemoJIT → Signal dom SoCOutput)
  -- ================================================================
  IO.println "\n=== Part 1: Signal API (loopMemoJIT via named output wires) ==="
  let soc ← rv32iSoCJITSimulate (dom := defaultDomain)
    (jitCppPath := cppPath) (firmware := firmware)

  -- Read output wires via SoCOutput struct at selected timesteps
  for cycle in [0, 10, 100, 1000] do
    let out := soc.atTime cycle
    IO.println s!"  cycle {cycle}: PC = 0x{toHex32 out.pc.toNat}"

  -- Run UART detection via Signal API
  let mut uartCount1 : Nat := 0
  let mut passed1 := false
  for cycle in [:maxCycles] do
    let out := soc.atTime cycle
    if out.uartValid then
      uartCount1 := uartCount1 + 1
      IO.println s!"  UART[{uartCount1}]: 0x{toHex32 out.uartData.toNat}"
      if out.uartData.toNat == 0xCAFE0000 then
        IO.println s!"  *** Part 1 PASSED (cycle {cycle}) ***"
        passed1 := true
        break

  if !passed1 then
    IO.eprintln "  Part 1 FAILED — 0xCAFE0000 marker not seen"
    return 1

  -- ================================================================
  -- Part 2: Streaming API test (rv32iSoCJITRun)
  -- ================================================================
  IO.println "\n=== Part 2: Streaming API (rv32iSoCJITRun) ==="
  let uartLogRef ← IO.mkRef (#[] : Array UInt64)
  let passedRef ← IO.mkRef false

  rv32iSoCJITRun
    (jitCppPath := cppPath)
    (firmware := firmware)
    (cycles := maxCycles)
    (callback := fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      if out.uartValid then
        let log ← uartLogRef.get
        uartLogRef.set (log.push out.uartData.toNat.toUInt64)
        IO.println s!"  UART[{log.size + 1}]: 0x{toHex32 out.uartData.toNat}"
        if out.uartData.toNat == 0xCAFE0000 then
          IO.println s!"  *** Part 2 PASSED (cycle {cycle}) ***"
          passedRef.set true
          return false  -- stop
      return true)  -- continue

  let uartLog ← uartLogRef.get
  let passed2 ← passedRef.get

  IO.println s!"\nJITLoop: Part 1: {uartCount1} UART words, Part 2: {uartLog.size} UART words"

  if passed1 && passed2 then
    IO.println "\n*** ALL TESTS PASSED ***"
    return 0
  else
    IO.eprintln "JITLoop: Test FAILED"
    return 1
