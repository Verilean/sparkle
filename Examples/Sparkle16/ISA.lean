/-
  Sparkle-16 ISA (Instruction Set Architecture)

  A simplified 16-bit RISC instruction set with 8 instructions.

  Architecture:
  - 16-bit data and address bus
  - 8 general-purpose registers (R0-R7), R0 hardwired to 0
  - Single-cycle execution (simplified)
  - Harvard architecture (separate instruction/data memory)
-/

import Sparkle.Data.BitPack

namespace Sparkle16

/-- Register identifier (R0-R7) -/
abbrev RegId := Fin 8

/-- 16-bit word (data and addresses) -/
abbrev Word := BitVec 16

/-- 8-bit immediate value -/
abbrev Imm8 := BitVec 8

/--
  Instruction Set for Sparkle-16

  Encoding format (16 bits total):
  [15:13] Opcode (3 bits)
  [12:0]  Operands (13 bits, format varies by instruction)
-/
inductive Instruction where
  | LDI (rd : RegId) (imm : Imm8)              -- Load Immediate: rd := imm (zero-extended)
  | ADD (rd rs1 rs2 : RegId)                   -- Add: rd := rs1 + rs2
  | SUB (rd rs1 rs2 : RegId)                   -- Subtract: rd := rs1 - rs2
  | AND (rd rs1 rs2 : RegId)                   -- Bitwise AND: rd := rs1 & rs2
  | LD  (rd rs1 : RegId)                       -- Load from memory: rd := mem[rs1]
  | ST  (rs1 rs2 : RegId)                      -- Store to memory: mem[rs1] := rs2
  | BEQ (rs1 rs2 : RegId) (offset : BitVec 7) -- Branch if equal: if rs1 == rs2 then PC += offset
  | JMP (addr : Word)                          -- Jump: PC := addr (13 bits, zero-extended)
  deriving Repr, BEq, DecidableEq

namespace Instruction

/-- Opcode encoding (3 bits) -/
inductive Opcode where
  | LDI : Opcode  -- 000
  | ADD : Opcode  -- 001
  | SUB : Opcode  -- 010
  | AND : Opcode  -- 011
  | LD  : Opcode  -- 100
  | ST  : Opcode  -- 101
  | BEQ : Opcode  -- 110
  | JMP : Opcode  -- 111
  deriving Repr, BEq, DecidableEq

def Opcode.toBitVec : Opcode → BitVec 3
  | LDI => 0b000
  | ADD => 0b001
  | SUB => 0b010
  | AND => 0b011
  | LD  => 0b100
  | ST  => 0b101
  | BEQ => 0b110
  | JMP => 0b111

def Opcode.fromBitVec : BitVec 3 → Option Opcode
  | 0b000 => some LDI
  | 0b001 => some ADD
  | 0b010 => some SUB
  | 0b011 => some AND
  | 0b100 => some LD
  | 0b101 => some ST
  | 0b110 => some BEQ
  | 0b111 => some JMP
  | _     => none

/--
  Encode instruction to 16-bit word

  Encoding formats:
  LDI: [opc(3)] [rd(3)] [imm(8)] [pad(2)]
  ADD/SUB/AND: [opc(3)] [rd(3)] [rs1(3)] [rs2(3)] [pad(4)]
  LD/ST: [opc(3)] [rd/rs1(3)] [rs1/rs2(3)] [pad(7)]
  BEQ: [opc(3)] [rs1(3)] [rs2(3)] [offset(7)]
  JMP: [opc(3)] [addr(13)]
-/
def encode (instr : Instruction) : Word :=
  match instr with
  | LDI rd imm =>
      let opc := Opcode.LDI.toBitVec
      let rdBits := BitVec.ofNat 3 rd.val
      let immBits := imm
      -- Pack: [opc(3)] [rd(3)] [imm(8)] [pad(2)]
      (opc.zeroExtend 16 <<< 13) |||
      (rdBits.zeroExtend 16 <<< 10) |||
      (immBits.zeroExtend 16 <<< 2)

  | ADD rd rs1 rs2 =>
      let opc := Opcode.ADD.toBitVec
      let rdBits := BitVec.ofNat 3 rd.val
      let rs1Bits := BitVec.ofNat 3 rs1.val
      let rs2Bits := BitVec.ofNat 3 rs2.val
      -- Pack: [opc(3)] [rd(3)] [rs1(3)] [rs2(3)] [pad(4)]
      (opc.zeroExtend 16 <<< 13) |||
      (rdBits.zeroExtend 16 <<< 10) |||
      (rs1Bits.zeroExtend 16 <<< 7) |||
      (rs2Bits.zeroExtend 16 <<< 4)

  | SUB rd rs1 rs2 =>
      let opc := Opcode.SUB.toBitVec
      let rdBits := BitVec.ofNat 3 rd.val
      let rs1Bits := BitVec.ofNat 3 rs1.val
      let rs2Bits := BitVec.ofNat 3 rs2.val
      (opc.zeroExtend 16 <<< 13) |||
      (rdBits.zeroExtend 16 <<< 10) |||
      (rs1Bits.zeroExtend 16 <<< 7) |||
      (rs2Bits.zeroExtend 16 <<< 4)

  | AND rd rs1 rs2 =>
      let opc := Opcode.AND.toBitVec
      let rdBits := BitVec.ofNat 3 rd.val
      let rs1Bits := BitVec.ofNat 3 rs1.val
      let rs2Bits := BitVec.ofNat 3 rs2.val
      (opc.zeroExtend 16 <<< 13) |||
      (rdBits.zeroExtend 16 <<< 10) |||
      (rs1Bits.zeroExtend 16 <<< 7) |||
      (rs2Bits.zeroExtend 16 <<< 4)

  | LD rd rs1 =>
      let opc := Opcode.LD.toBitVec
      let rdBits := BitVec.ofNat 3 rd.val
      let rs1Bits := BitVec.ofNat 3 rs1.val
      -- Pack: [opc(3)] [rd(3)] [rs1(3)] [pad(7)]
      (opc.zeroExtend 16 <<< 13) |||
      (rdBits.zeroExtend 16 <<< 10) |||
      (rs1Bits.zeroExtend 16 <<< 7)

  | ST rs1 rs2 =>
      let opc := Opcode.ST.toBitVec
      let rs1Bits := BitVec.ofNat 3 rs1.val
      let rs2Bits := BitVec.ofNat 3 rs2.val
      -- Pack: [opc(3)] [rs1(3)] [rs2(3)] [pad(7)]
      (opc.zeroExtend 16 <<< 13) |||
      (rs1Bits.zeroExtend 16 <<< 10) |||
      (rs2Bits.zeroExtend 16 <<< 7)

  | BEQ rs1 rs2 offset =>
      let opc := Opcode.BEQ.toBitVec
      let rs1Bits := BitVec.ofNat 3 rs1.val
      let rs2Bits := BitVec.ofNat 3 rs2.val
      -- Pack: [opc(3)] [rs1(3)] [rs2(3)] [offset(7)]
      (opc.zeroExtend 16 <<< 13) |||
      (rs1Bits.zeroExtend 16 <<< 10) |||
      (rs2Bits.zeroExtend 16 <<< 7) |||
      (offset.zeroExtend 16)

  | JMP addr =>
      let opc := Opcode.JMP.toBitVec
      let addrBits := addr &&& 0x1FFF  -- Take lower 13 bits
      -- Pack: [opc(3)] [addr(13)]
      (opc.zeroExtend 16 <<< 13) ||| addrBits

/--
  Decode 16-bit word to instruction

  Returns None if the bit pattern doesn't represent a valid instruction.
-/
def decode (word : Word) : Option Instruction := do
  -- Extract opcode (bits [15:13])
  let opcBits := (word >>> 13) &&& 0b111
  let opc ← Opcode.fromBitVec (opcBits.truncate 3)

  match opc with
  | Opcode.LDI =>
      -- Extract fields: [opc(3)] [rd(3)] [imm(8)] [pad(2)]
      let rdBits := (word >>> 10) &&& 0b111
      let immBits := (word >>> 2) &&& 0xFF
      let rd : Fin 8 := ⟨rdBits.toNat, by omega⟩
      some (LDI rd (immBits.truncate 8))

  | Opcode.ADD =>
      -- Extract fields: [opc(3)] [rd(3)] [rs1(3)] [rs2(3)] [pad(4)]
      let rdBits := (word >>> 10) &&& 0b111
      let rs1Bits := (word >>> 7) &&& 0b111
      let rs2Bits := (word >>> 4) &&& 0b111
      let rd : Fin 8 := ⟨rdBits.toNat, by omega⟩
      let rs1 : Fin 8 := ⟨rs1Bits.toNat, by omega⟩
      let rs2 : Fin 8 := ⟨rs2Bits.toNat, by omega⟩
      some (ADD rd rs1 rs2)

  | Opcode.SUB =>
      let rdBits := (word >>> 10) &&& 0b111
      let rs1Bits := (word >>> 7) &&& 0b111
      let rs2Bits := (word >>> 4) &&& 0b111
      let rd : Fin 8 := ⟨rdBits.toNat, by omega⟩
      let rs1 : Fin 8 := ⟨rs1Bits.toNat, by omega⟩
      let rs2 : Fin 8 := ⟨rs2Bits.toNat, by omega⟩
      some (SUB rd rs1 rs2)

  | Opcode.AND =>
      let rdBits := (word >>> 10) &&& 0b111
      let rs1Bits := (word >>> 7) &&& 0b111
      let rs2Bits := (word >>> 4) &&& 0b111
      let rd : Fin 8 := ⟨rdBits.toNat, by omega⟩
      let rs1 : Fin 8 := ⟨rs1Bits.toNat, by omega⟩
      let rs2 : Fin 8 := ⟨rs2Bits.toNat, by omega⟩
      some (AND rd rs1 rs2)

  | Opcode.LD =>
      -- Extract fields: [opc(3)] [rd(3)] [rs1(3)] [pad(7)]
      let rdBits := (word >>> 10) &&& 0b111
      let rs1Bits := (word >>> 7) &&& 0b111
      let rd : Fin 8 := ⟨rdBits.toNat, by omega⟩
      let rs1 : Fin 8 := ⟨rs1Bits.toNat, by omega⟩
      some (LD rd rs1)

  | Opcode.ST =>
      let rs1Bits := (word >>> 10) &&& 0b111
      let rs2Bits := (word >>> 7) &&& 0b111
      let rs1 : Fin 8 := ⟨rs1Bits.toNat, by omega⟩
      let rs2 : Fin 8 := ⟨rs2Bits.toNat, by omega⟩
      some (ST rs1 rs2)

  | Opcode.BEQ =>
      -- Extract fields: [opc(3)] [rs1(3)] [rs2(3)] [offset(7)]
      let rs1Bits := (word >>> 10) &&& 0b111
      let rs2Bits := (word >>> 7) &&& 0b111
      let offsetBits := word &&& 0x7F
      let rs1 : Fin 8 := ⟨rs1Bits.toNat, by omega⟩
      let rs2 : Fin 8 := ⟨rs2Bits.toNat, by omega⟩
      some (BEQ rs1 rs2 (offsetBits.truncate 7))

  | Opcode.JMP =>
      -- Extract fields: [opc(3)] [addr(13)]
      let addrBits := word &&& 0x1FFF
      some (JMP addrBits)

/-- Test that encode/decode roundtrips -/
theorem encode_decode_roundtrip (instr : Instruction) :
    decode (encode instr) = some instr := by
  cases instr <;> simp [encode, decode, Opcode.toBitVec, Opcode.fromBitVec]
  all_goals sorry  -- TODO: Complete proofs

end Instruction

/-- Check if instruction is a branch/jump (affects PC non-sequentially) -/
def Instruction.isBranch : Instruction → Bool
  | BEQ _ _ _ => true
  | JMP _     => true
  | _         => false

/-- Check if instruction writes to a register -/
def Instruction.writesRegister : Instruction → Bool
  | LDI _ _ => true
  | ADD _ _ _ => true
  | SUB _ _ _ => true
  | AND _ _ _ => true
  | LD _ _ => true
  | ST _ _ => false
  | BEQ _ _ _ => false
  | JMP _ => false

/-- Get destination register (if instruction writes to a register) -/
def Instruction.destReg? : Instruction → Option RegId
  | LDI rd _ => some rd
  | ADD rd _ _ => some rd
  | SUB rd _ _ => some rd
  | AND rd _ _ => some rd
  | LD rd _ => some rd
  | _ => none

/-- String representation for debugging -/
def Instruction.toString : Instruction → String
  | LDI rd imm => s!"LDI R{rd.val}, {imm.toNat}"
  | ADD rd rs1 rs2 => s!"ADD R{rd.val}, R{rs1.val}, R{rs2.val}"
  | SUB rd rs1 rs2 => s!"SUB R{rd.val}, R{rs1.val}, R{rs2.val}"
  | AND rd rs1 rs2 => s!"AND R{rd.val}, R{rs1.val}, R{rs2.val}"
  | LD rd rs1 => s!"LD R{rd.val}, [R{rs1.val}]"
  | ST rs1 rs2 => s!"ST [R{rs1.val}], R{rs2.val}"
  | BEQ rs1 rs2 offset => s!"BEQ R{rs1.val}, R{rs2.val}, {offset.toNat}"
  | JMP addr => s!"JMP {addr.toNat}"

instance : ToString Instruction where
  toString := Instruction.toString

end Sparkle16
