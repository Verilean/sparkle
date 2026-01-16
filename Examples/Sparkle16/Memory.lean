/-
  Sparkle-16 Memory Interface

  Provides both simulation-level memory (for testing) and
  synthesis-level memory (using vendor SRAM primitives).

  Memory Model:
  - Separate instruction and data memory (Harvard architecture)
  - 256 words of 16-bit memory (8-bit address space)
  - Synchronous read (1 cycle latency)
  - Synchronous write
-/

import Sparkle.Core.Signal
import Sparkle.IR.Builder
import Sparkle.Backend.Verilog

namespace Sparkle16

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Memory size (256 words) -/
def memorySize : Nat := 256

/-- Memory word (16 bits) -/
abbrev MemWord := BitVec 16

/-- Memory address (8 bits, addressing 256 words) -/
abbrev MemAddr := BitVec 8

/-
  Simulation-Level Memory

  For testing and simulation, we use a functional array model.
-/

/-- Memory state for simulation -/
structure SimMemory where
  data : Array MemWord
  deriving Repr

namespace SimMemory

/-- Create empty memory (all zeros) -/
def empty : SimMemory :=
  { data := Array.mkArray memorySize 0 }

/-- Load memory from list of words -/
def fromList (words : List MemWord) : SimMemory :=
  let arr := Array.mkArray memorySize 0
  let loaded := words.foldl (fun (acc : Array MemWord × Nat) w =>
    let (arr, idx) := acc
    if idx < memorySize then
      (arr.set! idx w, idx + 1)
    else
      (arr, idx)
  ) (arr, 0)
  { data := loaded.1 }

/-- Read from memory (synchronous) -/
def read (mem : SimMemory) (addr : MemAddr) : MemWord :=
  let idx := addr.toNat % memorySize
  mem.data[idx]!

/-- Write to memory (synchronous) -/
def write (mem : SimMemory) (addr : MemAddr) (value : MemWord) : SimMemory :=
  let idx := addr.toNat % memorySize
  { data := mem.data.set! idx value }

/-- Check if address is in bounds -/
def isValidAddr (addr : MemAddr) : Bool :=
  addr.toNat < memorySize

end SimMemory

/-
  Signal-Level Memory for Synthesis

  Uses Signal.loop to model sequential memory behavior.
-/

/-- Memory read operation (for synthesis) -/
def memRead {dom : DomainConfig} (mem : Signal dom (Array MemWord))
    (addr : Signal dom MemAddr) : Signal dom MemWord :=
  (fun m a =>
    let idx := a.toNat % memorySize
    m[idx]!) <$> mem <*> addr

/-- Memory write operation (for synthesis) -/
def memWrite {dom : DomainConfig} (mem : Signal dom (Array MemWord))
    (we : Signal dom Bool) (addr : Signal dom MemAddr)
    (data : Signal dom MemWord) : Signal dom (Array MemWord) :=
  (fun m w a d =>
    if w then
      let idx := a.toNat % memorySize
      m.set! idx d
    else
      m
  ) <$> mem <*> we <*> addr <*> data

/-
  Hardware Memory Module (Using IR Builder)

  For actual synthesis, we can use vendor SRAM primitives.
-/

/-- Instruction Memory Module (Read-Only) -/
def instructionMemoryModule : Module :=
  runModule "InstructionMemory" do
    -- Inputs
    addInput "clk" .bit
    addInput "addr" (.bitVector 8)

    -- For synthesis, instantiate SRAM primitive
    -- For simulation, would need behavioral model
    let dataOut ← makeWire "instr_data" (.bitVector 16)

    -- Option 1: Use vendor SRAM primitive (from Phase 6)
    emitInstance "SRAM_256x16" "imem"
      [ ("clk", .ref "clk")
      , ("we", .const 0 1)  -- Read-only
      , ("addr", .ref "addr")
      , ("din", .const 0 16)
      , ("dout", .ref dataOut)
      ]

    -- Outputs
    addOutput "instr" (.bitVector 16)
    emitAssign "instr" (.ref dataOut)

/-- Data Memory Module (Read/Write) -/
def dataMemoryModule : Module :=
  runModule "DataMemory" do
    -- Inputs
    addInput "clk" .bit
    addInput "we" .bit  -- Write enable
    addInput "addr" (.bitVector 8)
    addInput "din" (.bitVector 16)

    -- Instantiate SRAM primitive
    let dataOut ← makeWire "data_out" (.bitVector 16)

    emitInstance "SRAM_256x16" "dmem"
      [ ("clk", .ref "clk")
      , ("we", .ref "we")
      , ("addr", .ref "addr")
      , ("din", .ref "din")
      , ("dout", .ref dataOut)
      ]

    -- Outputs
    addOutput "dout" (.bitVector 16)
    emitAssign "dout" (.ref dataOut)

/-- Generate Verilog for memory modules -/
def generateMemoryVerilog : IO Unit := do
  IO.println "=== Instruction Memory Module ==="
  let iMemVerilog := Sparkle.Backend.Verilog.toVerilog instructionMemoryModule
  IO.println iMemVerilog
  Sparkle.Backend.Verilog.writeVerilogFile instructionMemoryModule "InstructionMemory.sv"

  IO.println "\n=== Data Memory Module ==="
  let dMemVerilog := Sparkle.Backend.Verilog.toVerilog dataMemoryModule
  IO.println dMemVerilog
  Sparkle.Backend.Verilog.writeVerilogFile dataMemoryModule "DataMemory.sv"

-- Main: Test memory modules
def main : IO Unit := do
  IO.println "=== Sparkle-16 Memory Modules ===\n"

  IO.println "Features:"
  IO.println "- Harvard architecture (separate instruction/data memory)"
  IO.println "- 256 words × 16 bits"
  IO.println "- Instruction memory: Read-only"
  IO.println "- Data memory: Read/Write"
  IO.println "- Uses vendor SRAM primitives for synthesis"
  IO.println ""

  -- Test simulation memory
  IO.println "Testing simulation memory:"
  let mem := SimMemory.empty
  let mem := mem.write 0x10 0x1234
  let mem := mem.write 0x20 0x5678
  IO.println s!"Read from 0x10: {mem.read 0x10}"
  IO.println s!"Read from 0x20: {mem.read 0x20}"
  IO.println s!"Read from 0x00: {mem.read 0x00}"
  IO.println ""

  -- Generate hardware modules
  generateMemoryVerilog
  IO.println "\n✓ Memory modules generated successfully!"

#eval main

end Sparkle16
