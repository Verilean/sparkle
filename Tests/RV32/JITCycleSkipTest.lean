/-
  JIT Cycle-Skip Test — Register Snapshot/Restore Roundtrip

  Proves that the register read/write API works correctly:
  1. Run normally for 100 cycles
  2. Snapshot all registers via JIT.getReg
  3. Note the PC at cycle 101 as reference
  4. Reset simulation
  5. Restore all registers + reload firmware
  6. Run 1 cycle from restored state
  7. Verify PC matches the reference

  Usage:
    lake exe rv32-jit-cycle-skip-test [jit.cpp] [firmware.hex]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Utils.HexLoader

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Utils.HexLoader

/-- Resolve a wire index by name, throwing if not found -/
def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let hexPath := args[1]? |>.getD "firmware/firmware.hex"

  -- Compile and load JIT module
  IO.println s!"CycleSkip: Compiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "CycleSkip: Loaded shared library"

  -- Resolve wire index for pcReg
  let pcIdx ← resolveWire handle "_gen_pcReg"
  IO.println s!"CycleSkip: pcReg wire index = {pcIdx}"

  -- Query register count
  let numRegs ← JIT.numRegs handle
  IO.println s!"CycleSkip: {numRegs} registers found"

  -- Query memory count (for firmware reload)
  -- Memory 0 = IMEM, others are DMEM byte banks

  -- Load firmware into IMEM (memory index 0)
  IO.println s!"CycleSkip: Loading firmware from {hexPath}..."
  let firmware ← loadHex hexPath
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- Phase 1: Run 100 cycles normally
  IO.println "CycleSkip: Running 100 cycles..."
  for _ in [:100] do
    JIT.eval handle
    JIT.tick handle

  -- Read PC after 100 ticks (eval to get combinational output)
  JIT.eval handle
  let pcAt100 ← JIT.getWire handle pcIdx
  IO.println s!"CycleSkip: PC at cycle 100 = 0x{String.ofList (Nat.toDigits 16 pcAt100.toNat)}"

  -- Snapshot all registers
  IO.println s!"CycleSkip: Snapshotting {numRegs} registers..."
  let mut regSnapshot : Array UInt64 := #[]
  for i in [:numRegs.toNat] do
    let val ← JIT.getReg handle i.toUInt32
    regSnapshot := regSnapshot.push val

  -- Also snapshot DMEM (4 byte-bank memories, indices 1-4)
  -- Each bank has 2^12 = 4096 entries
  let numDmemBanks := 4
  let dmemSize : Nat := 1 <<< 12
  let mut dmemSnapshot : Array (Array UInt32) := #[]
  for bank in [:numDmemBanks] do
    let mut bankData : Array UInt32 := #[]
    for addr in [:dmemSize] do
      let val ← JIT.getMem handle (bank + 1).toUInt32 addr.toUInt32
      bankData := bankData.push val
    dmemSnapshot := dmemSnapshot.push bankData

  -- Phase 2: Run 1 more cycle to get reference PC at cycle 101
  JIT.tick handle
  JIT.eval handle
  let pcAt101 ← JIT.getWire handle pcIdx
  IO.println s!"CycleSkip: PC at cycle 101 (reference) = 0x{String.ofList (Nat.toDigits 16 pcAt101.toNat)}"

  -- Phase 3: Reset and restore
  IO.println "CycleSkip: Resetting simulation..."
  JIT.reset handle

  -- Reload firmware into IMEM
  IO.println "CycleSkip: Reloading firmware..."
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32

  -- Restore DMEM
  IO.println "CycleSkip: Restoring DMEM..."
  for bank in [:numDmemBanks] do
    let bankData := dmemSnapshot[bank]!
    for addr in [:dmemSize] do
      JIT.setMem handle (bank + 1).toUInt32 addr.toUInt32 bankData[addr]!

  -- Restore all registers
  IO.println "CycleSkip: Restoring registers..."
  for i in [:numRegs.toNat] do
    JIT.setReg handle i.toUInt32 regSnapshot[i]!

  -- Phase 4: Run 1 cycle from restored state
  -- Must eval first to recompute _next from restored registers (reset doesn't clear _next)
  JIT.eval handle   -- recompute _next from restored cycle-100 state
  JIT.tick handle   -- apply _next → registers now at cycle 101
  JIT.eval handle   -- read wires reflecting cycle 101 state
  let pcRestored ← JIT.getWire handle pcIdx
  IO.println s!"CycleSkip: PC after restore+eval+tick+eval (actual) = 0x{String.ofList (Nat.toDigits 16 pcRestored.toNat)}"

  -- Verify
  if pcRestored == pcAt101 then
    IO.println s!"\n*** PASS: Register snapshot/restore roundtrip works ***"
    IO.println s!"    Reference PC = 0x{String.ofList (Nat.toDigits 16 pcAt101.toNat)}"
    IO.println s!"    Restored  PC = 0x{String.ofList (Nat.toDigits 16 pcRestored.toNat)}"
    JIT.destroy handle
    return 0
  else
    IO.eprintln s!"\n*** FAIL: PC mismatch after restore ***"
    IO.eprintln s!"    Expected PC = 0x{String.ofList (Nat.toDigits 16 pcAt101.toNat)}"
    IO.eprintln s!"    Got      PC = 0x{String.ofList (Nat.toDigits 16 pcRestored.toNat)}"
    -- Print a few register values for debugging
    IO.eprintln s!"    Registers snapshot:"
    for i in [:min 10 numRegs.toNat] do
      let name ← JIT.regName handle i.toUInt32
      IO.eprintln s!"      [{i}] {name} = 0x{String.ofList (Nat.toDigits 16 regSnapshot[i]!.toNat)}"
    JIT.destroy handle
    return 1
