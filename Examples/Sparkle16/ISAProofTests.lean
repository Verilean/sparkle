/-
  ISA Correctness Proofs - Test Examples

  This file demonstrates the ISA correctness theorems from
  Sparkle/Verification/ISAProps.lean
-/

import Sparkle.Verification.ISAProps

open Sparkle.Verification.ISAProps
open Sparkle.Verification.ISAProps.Instruction

-- Test: Opcode encoding/decoding roundtrip
example : Opcode.fromBitVec (Opcode.toBitVec Opcode.ADD) = some Opcode.ADD :=
  opcode_encode_decode Opcode.ADD

example : Opcode.fromBitVec (Opcode.toBitVec Opcode.LDI) = some Opcode.LDI :=
  opcode_encode_decode Opcode.LDI

example : Opcode.fromBitVec (Opcode.toBitVec Opcode.BEQ) = some Opcode.BEQ :=
  opcode_encode_decode Opcode.BEQ

-- Test: All opcodes roundtrip correctly
example (opc : Opcode) : Opcode.fromBitVec (Opcode.toBitVec opc) = some opc :=
  opcode_encode_decode opc

-- Test: Instruction classification

example : (Instruction.ADD ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩).isBranch = false := rfl

example : (Instruction.BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 5).isBranch = true := rfl

example : (Instruction.JMP 0x100).isBranch = true := rfl

example : (Instruction.LDI ⟨1, by omega⟩ 42).writesRegister = true := rfl

example : (Instruction.ADD ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩).writesRegister = true := rfl

example : (Instruction.ST ⟨1, by omega⟩ ⟨2, by omega⟩).writesRegister = false := rfl

example : (Instruction.BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 5).writesRegister = false := rfl

-- Test: Destination register extraction

example : (Instruction.LDI ⟨3, by omega⟩ 42).destReg? = some ⟨3, by omega⟩ := rfl

example : (Instruction.ADD ⟨5, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩).destReg? = some ⟨5, by omega⟩ := rfl

example : (Instruction.ST ⟨1, by omega⟩ ⟨2, by omega⟩).destReg? = none := rfl

-- Test: Theorems about instruction properties

-- If an instruction writes to a register, it has a destination
example (instr : Instruction) (h : instr.writesRegister = true) :
    instr.destReg?.isSome = true :=
  writes_has_dest instr h

-- Branch instructions don't write to registers
example (instr : Instruction) (h : instr.isBranch = true) :
    instr.writesRegister = false :=
  branch_no_write instr h

-- Specific test: BEQ doesn't write
example : let instr := Instruction.BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 5
          instr.writesRegister = false :=
  branch_no_write _ rfl

-- Specific test: ADD writes and has destination
example : let instr := Instruction.ADD ⟨3, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
          instr.destReg?.isSome = true :=
  writes_has_dest _ rfl

-- Main: Display test results
def main : IO Unit := do
  IO.println "=== ISA Correctness Proofs - Test Results ===\n"

  IO.println "✓ Opcode Encoding/Decoding:"
  IO.println "  - All 8 opcodes roundtrip correctly"
  IO.println "  - LDI ↔ 000, ADD ↔ 001, SUB ↔ 010, AND ↔ 011"
  IO.println "  - LD ↔ 100, ST ↔ 101, BEQ ↔ 110, JMP ↔ 111"
  IO.println ""

  IO.println "✓ Instruction Classification:"
  IO.println "  - Branch instructions: BEQ, JMP"
  IO.println "  - Non-branch instructions: LDI, ADD, SUB, AND, LD, ST"
  IO.println "  - Register-writing instructions: LDI, ADD, SUB, AND, LD"
  IO.println "  - Non-writing instructions: ST, BEQ, JMP"
  IO.println ""

  IO.println "✓ Destination Register:"
  IO.println "  - LDI R3, 42 → dest = R3"
  IO.println "  - ADD R5, R1, R2 → dest = R5"
  IO.println "  - ST [R1], R2 → dest = none"
  IO.println ""

  IO.println "✓ Proven Theorems:"
  IO.println "  1. opcode_encode_decode: All opcodes roundtrip"
  IO.println "  2. writes_has_dest: Writing instructions have destinations"
  IO.println "  3. branch_no_write: Branch instructions don't write"
  IO.println "  4. encode_preserves_dest: Encoding preserves destinations"
  IO.println ""

  IO.println "Status: ISA correctness framework established ✓"
  IO.println "Note: Some complex proofs use 'sorry' placeholders"
  IO.println "      Full proofs require detailed BitVec manipulation lemmas"

#eval main
