/-
  Simple Memory Example

  Demonstrates the use of synchronous memory primitives (RAM/BRAM).
  This example shows a 256-byte memory with write and read operations.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
## Example 1: Simple 256-byte Memory

A basic memory with:
- 256 locations (8-bit address)
- 8-bit data width
- Synchronous write
- Registered read (1-cycle latency)
-/

def simpleRAM
    (writeAddr : Signal defaultDomain (BitVec 8))
    (writeData : Signal defaultDomain (BitVec 8))
    (writeEnable : Signal defaultDomain Bool)
    (readAddr : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.memory writeAddr writeData writeEnable readAddr

-- Simulate a simple memory access pattern
def memoryTest : IO Unit := do
  -- Test signal: write to address 0x10, then read from it
  let writeAddr : Signal defaultDomain (BitVec 8) := ⟨fun t =>
    if t == 0 then 0x10#8 else 0#8⟩

  let writeData : Signal defaultDomain (BitVec 8) := ⟨fun t =>
    if t == 0 then 0x42#8 else 0#8⟩

  let writeEnable : Signal defaultDomain Bool := ⟨fun t =>
    t == 0⟩  -- Only write at t=0

  let readAddr : Signal defaultDomain (BitVec 8) := ⟨fun t =>
    if t >= 1 then 0x10#8 else 0#8⟩

  let readData := simpleRAM writeAddr writeData writeEnable readAddr

  IO.println "=== Simple Memory Test ==="
  IO.println ""
  IO.println "Memory: 256 bytes (8-bit address, 8-bit data)"
  IO.println "Operation: Write 0x42 to address 0x10 at t=0"
  IO.println "           Read from address 0x10 at t=1+"
  IO.println ""

  -- Show first few cycles
  for t in [0:5] do
    IO.println (s!"t={t}: write_en={writeEnable.atTime t}, " ++
               s!"write_addr=0x{writeAddr.atTime t}, " ++
               s!"write_data=0x{writeData.atTime t}, " ++
               s!"read_addr=0x{readAddr.atTime t}, " ++
               s!"read_data=0x{readData.atTime t}")

  IO.println ""
  IO.println "Note: Read data has 1-cycle latency (registered read)"
  IO.println "      t=0: Write 0x42 to 0x10"
  IO.println "      t=1: Read address set to 0x10"
  IO.println "      t=2: Read data shows 0x42 (1-cycle delay)"

/-!
## Example 2: Register File (CPU Registers)

A small register file with:
- 8 registers (3-bit address: R0-R7)
- 16-bit data width
- Useful for CPU implementations
-/

def registerFile
    (writeReg : Signal defaultDomain (BitVec 3))
    (writeData : Signal defaultDomain (BitVec 16))
    (writeEnable : Signal defaultDomain Bool)
    (readReg : Signal defaultDomain (BitVec 3))
    : Signal defaultDomain (BitVec 16) :=
  Signal.memory writeReg writeData writeEnable readReg

def registerFileTest : IO Unit := do
  -- Test: Write to R3 (register 3), then read from it
  let writeReg : Signal defaultDomain (BitVec 3) := ⟨fun t =>
    if t == 0 then 3#3 else 0#3⟩

  let writeData : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if t == 0 then 0x1234#16 else 0#16⟩

  let writeEnable : Signal defaultDomain Bool := ⟨fun t =>
    t == 0⟩

  let readReg : Signal defaultDomain (BitVec 3) := ⟨fun t =>
    if t >= 1 then 3#3 else 0#3⟩

  let readData := registerFile writeReg writeData writeEnable readReg

  IO.println "=== Register File Test ==="
  IO.println ""
  IO.println "Register File: 8 registers x 16-bit (R0-R7)"
  IO.println "Operation: Write 0x1234 to R3 at t=0"
  IO.println "           Read from R3 at t=1+"
  IO.println ""

  for t in [0:5] do
    IO.println (s!"t={t}: write_en={writeEnable.atTime t}, " ++
               s!"write_reg=R{writeReg.atTime t}, " ++
               s!"write_data=0x{writeData.atTime t}, " ++
               s!"read_reg=R{readReg.atTime t}, " ++
               s!"read_data=0x{readData.atTime t}")

def main : IO Unit := do
  memoryTest
  IO.println ""
  registerFileTest
