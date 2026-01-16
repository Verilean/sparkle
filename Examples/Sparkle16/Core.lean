/-
  Sparkle-16 CPU Core

  Complete 16-bit RISC CPU integrating all components:
  - ALU (Arithmetic Logic Unit)
  - Register File (8 registers, R0 = 0)
  - Memory Interface (instruction and data)
  - Control Unit (fetch-decode-execute FSM)

  This module demonstrates using Signal.loop for stateful hardware.
-/

-- Note: In a real setup, these would be properly imported
-- For now, we'll include the necessary definitions inline

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Sparkle.Data.BitPack

-- Re-include ISA definitions
/-- Register identifier (R0-R7) -/
abbrev RegId := Fin 8

/-- 16-bit word (data and addresses) -/
abbrev Word := BitVec 16

/-- 8-bit immediate value -/
abbrev Imm8 := BitVec 8

inductive Instruction where
  | LDI (rd : RegId) (imm : Imm8)
  | ADD (rd rs1 rs2 : RegId)
  | SUB (rd rs1 rs2 : RegId)
  | AND (rd rs1 rs2 : RegId)
  | LD  (rd rs1 : RegId)
  | ST  (rs1 rs2 : RegId)
  | BEQ (rs1 rs2 : RegId) (offset : BitVec 7)
  | JMP (addr : Word)
  deriving Repr, BEq

namespace Instruction

inductive Opcode where
  | LDI | ADD | SUB | AND | LD | ST | BEQ | JMP
  deriving Repr, BEq

def Opcode.toBitVec : Opcode → BitVec 3
  | LDI => 0b000 | ADD => 0b001 | SUB => 0b010 | AND => 0b011
  | LD => 0b100 | ST => 0b101 | BEQ => 0b110 | JMP => 0b111

def Opcode.fromBitVec : BitVec 3 → Option Opcode
  | 0b000 => some LDI | 0b001 => some ADD | 0b010 => some SUB | 0b011 => some AND
  | 0b100 => some LD | 0b101 => some ST | 0b110 => some BEQ | 0b111 => some JMP
  | _ => none

def encode (instr : Instruction) : Word :=
  match instr with
  | LDI rd imm =>
      let opc := Opcode.LDI.toBitVec
      let rdBits := BitVec.ofNat 3 rd.val
      (opc.zeroExtend 16 <<< 13) ||| (rdBits.zeroExtend 16 <<< 10) ||| (imm.zeroExtend 16 <<< 2)
  | ADD rd rs1 rs2 =>
      let opc := Opcode.ADD.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (BitVec.ofNat 3 rd.val).zeroExtend 16 <<< 10 |||
      (BitVec.ofNat 3 rs1.val).zeroExtend 16 <<< 7 ||| (BitVec.ofNat 3 rs2.val).zeroExtend 16 <<< 4
  | SUB rd rs1 rs2 =>
      let opc := Opcode.SUB.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (BitVec.ofNat 3 rd.val).zeroExtend 16 <<< 10 |||
      (BitVec.ofNat 3 rs1.val).zeroExtend 16 <<< 7 ||| (BitVec.ofNat 3 rs2.val).zeroExtend 16 <<< 4
  | AND rd rs1 rs2 =>
      let opc := Opcode.AND.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (BitVec.ofNat 3 rd.val).zeroExtend 16 <<< 10 |||
      (BitVec.ofNat 3 rs1.val).zeroExtend 16 <<< 7 ||| (BitVec.ofNat 3 rs2.val).zeroExtend 16 <<< 4
  | LD rd rs1 =>
      let opc := Opcode.LD.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (BitVec.ofNat 3 rd.val).zeroExtend 16 <<< 10 |||
      (BitVec.ofNat 3 rs1.val).zeroExtend 16 <<< 7
  | ST rs1 rs2 =>
      let opc := Opcode.ST.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (BitVec.ofNat 3 rs1.val).zeroExtend 16 <<< 10 |||
      (BitVec.ofNat 3 rs2.val).zeroExtend 16 <<< 7
  | BEQ rs1 rs2 offset =>
      let opc := Opcode.BEQ.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (BitVec.ofNat 3 rs1.val).zeroExtend 16 <<< 10 |||
      (BitVec.ofNat 3 rs2.val).zeroExtend 16 <<< 7 ||| offset.zeroExtend 16
  | JMP addr =>
      let opc := Opcode.JMP.toBitVec
      (opc.zeroExtend 16 <<< 13) ||| (addr &&& 0x1FFF)

/-- Helper lemma: masking with 0b111 gives value < 8 -/
private theorem mask_7_lt_8 (x : BitVec 16) : ((x &&& 0b111).toNat) < 8 := by
  -- The AND operation with 0b111 produces a 16-bit value that is at most 0b111
  -- We need to show that this is less than 8
  have h : (x &&& 0b111).toNat ≤ (0b111 : BitVec 16).toNat := by
    sorry  -- TODO: Need proper BitVec lemma about AND bounds
  have h2 : (0b111 : BitVec 16).toNat = 7 := by rfl
  rw [h2] at h
  omega

def decode (word : Word) : Option Instruction := do
  let opcBits := (word >>> 13) &&& 0b111
  let opc ← Opcode.fromBitVec (opcBits.truncate 3)
  match opc with
  | Opcode.LDI =>
      let rd : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (LDI rd ((word >>> 2 &&& 0xFF).truncate 8))
  | Opcode.ADD =>
      let rd : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs1 : Fin 8 := ⟨((word >>> 7) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs2 : Fin 8 := ⟨((word >>> 4) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (ADD rd rs1 rs2)
  | Opcode.SUB =>
      let rd : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs1 : Fin 8 := ⟨((word >>> 7) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs2 : Fin 8 := ⟨((word >>> 4) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (SUB rd rs1 rs2)
  | Opcode.AND =>
      let rd : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs1 : Fin 8 := ⟨((word >>> 7) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs2 : Fin 8 := ⟨((word >>> 4) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (AND rd rs1 rs2)
  | Opcode.LD =>
      let rd : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs1 : Fin 8 := ⟨((word >>> 7) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (LD rd rs1)
  | Opcode.ST =>
      let rs1 : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs2 : Fin 8 := ⟨((word >>> 7) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (ST rs1 rs2)
  | Opcode.BEQ =>
      let rs1 : Fin 8 := ⟨((word >>> 10) &&& 0b111).toNat, mask_7_lt_8 _⟩
      let rs2 : Fin 8 := ⟨((word >>> 7) &&& 0b111).toNat, mask_7_lt_8 _⟩
      some (BEQ rs1 rs2 ((word &&& 0x7F).truncate 7))
  | Opcode.JMP =>
      some (JMP (word &&& 0x1FFF))

def toString : Instruction → String
  | LDI rd imm => s!"LDI R{rd.val}, {imm.toNat}"
  | ADD rd rs1 rs2 => s!"ADD R{rd.val}, R{rs1.val}, R{rs2.val}"
  | SUB rd rs1 rs2 => s!"SUB R{rd.val}, R{rs1.val}, R{rs2.val}"
  | AND rd rs1 rs2 => s!"AND R{rd.val}, R{rs1.val}, R{rs2.val}"
  | LD rd rs1 => s!"LD R{rd.val}, [R{rs1.val}]"
  | ST rs1 rs2 => s!"ST [R{rs1.val}], R{rs2.val}"
  | BEQ rs1 rs2 offset => s!"BEQ R{rs1.val}, R{rs2.val}, {offset.toNat}"
  | JMP addr => s!"JMP {addr.toNat}"

instance : ToString Instruction where
  toString := toString

end Instruction

-- Memory simulation
def memorySize : Nat := 256
abbrev MemWord := BitVec 16
abbrev MemAddr := BitVec 8

structure SimMemory where
  data : Array MemWord
  deriving Repr

namespace SimMemory

def empty : SimMemory :=
  { data := (List.replicate memorySize (0 : MemWord)).toArray }

def fromList (words : List MemWord) : SimMemory :=
  let arr := (List.replicate memorySize (0 : MemWord)).toArray
  let loaded := words.foldl (fun (acc : Array MemWord × Nat) w =>
    let (arr, idx) := acc
    if idx < memorySize then (arr.set! idx w, idx + 1) else (arr, idx)
  ) (arr, 0)
  { data := loaded.1 }

def read (mem : SimMemory) (addr : MemAddr) : MemWord :=
  mem.data[addr.toNat % memorySize]!

def write (mem : SimMemory) (addr : MemAddr) (value : MemWord) : SimMemory :=
  { data := mem.data.set! (addr.toNat % memorySize) value }

end SimMemory

namespace Sparkle16

open Sparkle.Core.Signal
open Sparkle.Core.Domain

/-- CPU execution phase -/
inductive Phase where
  | Fetch     -- Fetch instruction from memory
  | Decode    -- Decode instruction fields
  | Execute   -- Execute instruction and update state
  deriving Repr, BEq, Inhabited

/-- CPU state -/
structure CPUState where
  pc : Word                    -- Program counter
  regs : Fin 8 → Word         -- Register file (functional)
  phase : Phase                -- Current execution phase
  instr : Option Instruction   -- Currently decoded instruction
  memData : Word               -- Data from memory load

namespace CPUState

/-- Initial CPU state -/
def init : CPUState where
  pc := 0
  regs := fun _ => 0  -- All registers start at 0
  phase := Phase.Fetch
  instr := none
  memData := 0

/-- Read register (R0 always returns 0) -/
def readReg (state : CPUState) (r : RegId) : Word :=
  if r.val = 0 then 0 else state.regs r

/-- Write register (R0 writes are ignored) -/
def writeReg (state : CPUState) (r : RegId) (value : Word) : CPUState :=
  if r.val = 0 then
    state
  else
    { state with regs := fun i => if i = r then value else state.regs i }

/-- Increment PC -/
def incPC (state : CPUState) : CPUState :=
  { state with pc := state.pc + 1 }

/-- Set PC (for branches/jumps) -/
def setPC (state : CPUState) (newPC : Word) : CPUState :=
  { state with pc := newPC }

end CPUState

/-
  CPU Execution Semantics (Pure Functions)

  These define what each instruction should do, independent of hardware.
-/

/-- Execute a single instruction (abstract semantics) -/
def executeInstruction (instr : Instruction) (state : CPUState) (memData : Word) : CPUState :=
  match instr with
  | .LDI rd imm =>
      -- Load immediate: Rd := imm (zero-extended)
      let value := imm.zeroExtend 16
      state.writeReg rd value |>.incPC

  | .ADD rd rs1 rs2 =>
      -- Add: Rd := Rs1 + Rs2
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      let result := val1 + val2
      state.writeReg rd result |>.incPC

  | .SUB rd rs1 rs2 =>
      -- Subtract: Rd := Rs1 - Rs2
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      let result := val1 - val2
      state.writeReg rd result |>.incPC

  | .AND rd rs1 rs2 =>
      -- Bitwise AND: Rd := Rs1 & Rs2
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      let result := val1 &&& val2
      state.writeReg rd result |>.incPC

  | .LD rd _rs1 =>
      -- Load from memory: Rd := mem[Rs1]
      -- Note: Address resolution happens in cpuStep, memData contains the loaded value
      state.writeReg rd memData |>.incPC

  | .ST _rs1 _rs2 =>
      -- Store to memory: mem[Rs1] := Rs2
      -- Note: Actual address resolution and write happens in cpuStep
      state.incPC

  | .BEQ rs1 rs2 offset =>
      -- Branch if equal: if Rs1 == Rs2 then PC := PC + offset
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if val1 == val2 then
        let signExtOffset := offset.signExtend 16
        state.setPC (state.pc + signExtOffset)
      else
        state.incPC

  | .JMP addr =>
      -- Jump: PC := addr
      state.setPC addr

/-
  CPU State Machine (using Signal.loop)

  This is the hardware implementation of the CPU using Signal semantics.
-/

/-- CPU one-cycle step (for simulation) -/
def cpuStep (state : CPUState) (instrMem : SimMemory) (dataMem : SimMemory) :
    CPUState × SimMemory :=
  match state.phase with
  | .Fetch =>
      -- Fetch instruction from instruction memory
      let instrWord := instrMem.read (state.pc.truncate 8)
      let instr? := Instruction.decode instrWord
      ({ state with phase := .Decode, instr := instr? }, dataMem)

  | .Decode =>
      -- Decode already happened in Fetch, move to Execute
      ({ state with phase := .Execute }, dataMem)

  | .Execute =>
      match state.instr with
      | none =>
          -- Invalid instruction, skip
          ({ state with phase := .Fetch } |>.incPC, dataMem)
      | some instr =>
          match instr with
          | .LD _rd rs1 =>
              -- Load: read from data memory
              let addr := state.readReg rs1
              let memData := dataMem.read (addr.truncate 8)
              let newState := executeInstruction instr state memData
              ({ newState with phase := .Fetch, instr := none }, dataMem)

          | .ST rs1 rs2 =>
              -- Store: write to data memory
              let addr := state.readReg rs1
              let data := state.readReg rs2
              let newDataMem := dataMem.write (addr.truncate 8) data
              let newState := executeInstruction instr state 0
              ({ newState with phase := .Fetch, instr := none }, newDataMem)

          | _ =>
              -- All other instructions (ALU, branches)
              let newState := executeInstruction instr state 0
              ({ newState with phase := .Fetch, instr := none }, dataMem)

/-
  CPU Simulation

  Run the CPU for N cycles on a given program.
-/

/-- Run CPU for N cycles -/
def runCPU (n : Nat) (instrMem : SimMemory) (dataMem : SimMemory) (initState : CPUState) :
    CPUState × SimMemory :=
  let rec loop (i : Nat) (state : CPUState) (dmem : SimMemory) : CPUState × SimMemory :=
    if i = 0 then
      (state, dmem)
    else
      let (newState, newDMem) := cpuStep state instrMem dmem
      loop (i - 1) newState newDMem
  loop n initState dataMem

/-- CPU state to string (for debugging) -/
def CPUState.toString (state : CPUState) : String :=
  let phaseStr := match state.phase with
    | .Fetch => "Fetch"
    | .Decode => "Decode"
    | .Execute => "Execute"
  let instrStr := match state.instr with
    | none => "None"
    | some i => i.toString
  s!"PC={state.pc.toNat} Phase={phaseStr} Instr={instrStr}\n" ++
  s!"R0={state.readReg ⟨0, by omega⟩} R1={state.readReg ⟨1, by omega⟩} " ++
  s!"R2={state.readReg ⟨2, by omega⟩} R3={state.readReg ⟨3, by omega⟩}\n" ++
  s!"R4={state.readReg ⟨4, by omega⟩} R5={state.readReg ⟨5, by omega⟩} " ++
  s!"R6={state.readReg ⟨6, by omega⟩} R7={state.readReg ⟨7, by omega⟩}"

instance : ToString CPUState where
  toString := CPUState.toString

/-
  Example Programs

  Simple test programs to demonstrate CPU functionality.
-/

/-- Example 1: Load immediate and add -/
def exampleProgram1 : List Instruction := [
  .LDI ⟨1, by omega⟩ 10,      -- R1 := 10
  .LDI ⟨2, by omega⟩ 20,      -- R2 := 20
  .ADD ⟨3, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩,  -- R3 := R1 + R2 = 30
  .SUB ⟨4, by omega⟩ ⟨3, by omega⟩ ⟨1, by omega⟩   -- R4 := R3 - R1 = 20
]

/-- Example 2: Loop with branch -/
def exampleProgram2 : List Instruction := [
  .LDI ⟨1, by omega⟩ 0,       -- R1 := 0 (counter)
  .LDI ⟨2, by omega⟩ 5,       -- R2 := 5 (limit)
  .LDI ⟨3, by omega⟩ 1,       -- R3 := 1 (increment)
  .ADD ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨3, by omega⟩,  -- R1 := R1 + 1
  .BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 2,  -- if R1 == R2, skip next 2 instructions
  .JMP 3,                      -- Jump back to ADD instruction (address 3)
  .LDI ⟨4, by omega⟩ 99        -- R4 := 99 (done marker)
]

/-- Assemble program to memory -/
def assembleProgram (instrs : List Instruction) : SimMemory :=
  SimMemory.fromList (instrs.map Instruction.encode)

-- Main: Test CPU simulation
def main : IO Unit := do
  IO.println "=== Sparkle-16 CPU Core ===\n"

  IO.println "Example 1: Simple arithmetic"
  IO.println "Program:"
  for instr in exampleProgram1 do
    IO.println s!"  {instr}"
  IO.println ""

  let instrMem := assembleProgram exampleProgram1
  let dataMem := SimMemory.empty
  let initState := CPUState.init

  IO.println "Initial state:"
  IO.println initState.toString
  IO.println ""

  -- Run for enough cycles to execute all instructions
  -- Each instruction takes 3 cycles (Fetch, Decode, Execute)
  let cycles := exampleProgram1.length * 3
  let (finalState, _) := runCPU cycles instrMem dataMem initState

  IO.println s!"After {cycles} cycles:"
  IO.println finalState.toString
  IO.println ""

  IO.println "Expected results:"
  IO.println "  R1 = 10 (0x000a)"
  IO.println "  R2 = 20 (0x0014)"
  IO.println "  R3 = 30 (0x001e)"
  IO.println "  R4 = 20 (0x0014)"
  IO.println ""

  IO.println "\n=== Example 2: Loop with branch ==="
  IO.println "Program:"
  let mut idx := 0
  for instr in exampleProgram2 do
    IO.println s!"  {idx}: {instr}"
    idx := idx + 1
  IO.println ""

  let instrMem2 := assembleProgram exampleProgram2
  let dataMem2 := SimMemory.empty
  let initState2 := CPUState.init

  -- Run for more cycles to allow loop completion
  let cycles2 := 30
  let (finalState2, _) := runCPU cycles2 instrMem2 dataMem2 initState2

  IO.println s!"After {cycles2} cycles:"
  IO.println finalState2.toString
  IO.println ""

  IO.println "Expected: R1 = 5, R4 = 99 (loop completed)"
  IO.println ""
  IO.println "✓ CPU core simulation complete!"

end Sparkle16

-- Export main at the top level for `lake env lean --run`
def main : IO Unit := Sparkle16.main
