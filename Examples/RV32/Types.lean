/-
  RV32I Types

  Defines the instruction formats, opcodes, ALU operations, and control signals
  for the RISC-V RV32I base integer instruction set (unprivileged).
-/

namespace Sparkle.Examples.RV32

-- ============================================================================
-- Constants
-- ============================================================================

/-- Instruction width (32 bits) -/
def xlen : Nat := 32

/-- Register file address width (5 bits for x0-x31) -/
def regAddrBits : Nat := 5

/-- Number of registers -/
def numRegs : Nat := 32

/-- Instruction memory address width (10 bits = 1024 words) -/
def imemAddrBits : Nat := 10

/-- Data memory address width (10 bits = 1024 words) -/
def dmemAddrBits : Nat := 10

-- ============================================================================
-- RV32I Opcodes (bits [6:0])
-- ============================================================================

/-- RV32I major opcodes -/
inductive Opcode where
  | LUI    : Opcode   -- 0110111 Load Upper Immediate
  | AUIPC  : Opcode   -- 0010111 Add Upper Immediate to PC
  | JAL    : Opcode   -- 1101111 Jump And Link
  | JALR   : Opcode   -- 1100111 Jump And Link Register
  | BRANCH : Opcode   -- 1100011 Branch (BEQ, BNE, BLT, BGE, BLTU, BGEU)
  | LOAD   : Opcode   -- 0000011 Load (LB, LH, LW, LBU, LHU)
  | STORE  : Opcode   -- 0100011 Store (SB, SH, SW)
  | ALUI   : Opcode   -- 0010011 ALU Immediate (ADDI, SLTI, etc.)
  | ALU    : Opcode   -- 0110011 ALU Register (ADD, SUB, etc.)
  | FENCE  : Opcode   -- 0001111 Memory ordering
  | SYSTEM : Opcode   -- 1110011 ECALL / EBREAK
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode opcode to 7-bit value -/
def Opcode.toBitVec7 : Opcode -> BitVec 7
  | .LUI    => 0b0110111#7
  | .AUIPC  => 0b0010111#7
  | .JAL    => 0b1101111#7
  | .JALR   => 0b1100111#7
  | .BRANCH => 0b1100011#7
  | .LOAD   => 0b0000011#7
  | .STORE  => 0b0100011#7
  | .ALUI   => 0b0010011#7
  | .ALU    => 0b0110011#7
  | .FENCE  => 0b0001111#7
  | .SYSTEM => 0b1110011#7

/-- Decode 7-bit value to opcode (returns none for invalid) -/
def Opcode.fromBitVec7 (v : BitVec 7) : Option Opcode :=
  if v == 0b0110111#7 then some .LUI
  else if v == 0b0010111#7 then some .AUIPC
  else if v == 0b1101111#7 then some .JAL
  else if v == 0b1100111#7 then some .JALR
  else if v == 0b1100011#7 then some .BRANCH
  else if v == 0b0000011#7 then some .LOAD
  else if v == 0b0100011#7 then some .STORE
  else if v == 0b0010011#7 then some .ALUI
  else if v == 0b0110011#7 then some .ALU
  else if v == 0b0001111#7 then some .FENCE
  else if v == 0b1110011#7 then some .SYSTEM
  else none

-- ============================================================================
-- ALU Operations
-- ============================================================================

/-- ALU operation enumeration -/
inductive ALUOp where
  | ADD  : ALUOp   -- Addition
  | SUB  : ALUOp   -- Subtraction
  | AND  : ALUOp   -- Bitwise AND
  | OR   : ALUOp   -- Bitwise OR
  | XOR  : ALUOp   -- Bitwise XOR
  | SLL  : ALUOp   -- Shift Left Logical
  | SRL  : ALUOp   -- Shift Right Logical
  | SRA  : ALUOp   -- Shift Right Arithmetic
  | SLT  : ALUOp   -- Set Less Than (signed)
  | SLTU : ALUOp   -- Set Less Than (unsigned)
  | PASS : ALUOp   -- Pass through B operand (for LUI)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode ALU operation to 4-bit control signal -/
def ALUOp.toBitVec4 : ALUOp -> BitVec 4
  | .ADD  => 0x0#4
  | .SUB  => 0x1#4
  | .AND  => 0x2#4
  | .OR   => 0x3#4
  | .XOR  => 0x4#4
  | .SLL  => 0x5#4
  | .SRL  => 0x6#4
  | .SRA  => 0x7#4
  | .SLT  => 0x8#4
  | .SLTU => 0x9#4
  | .PASS => 0xA#4

/-- Decode 4-bit control signal to ALU operation -/
def ALUOp.fromBitVec4 (v : BitVec 4) : ALUOp :=
  if v == 0x0#4 then .ADD
  else if v == 0x1#4 then .SUB
  else if v == 0x2#4 then .AND
  else if v == 0x3#4 then .OR
  else if v == 0x4#4 then .XOR
  else if v == 0x5#4 then .SLL
  else if v == 0x6#4 then .SRL
  else if v == 0x7#4 then .SRA
  else if v == 0x8#4 then .SLT
  else if v == 0x9#4 then .SLTU
  else .PASS

-- ============================================================================
-- Branch Function Codes (funct3)
-- ============================================================================

/-- Branch funct3 codes -/
inductive BranchOp where
  | BEQ  : BranchOp  -- 000
  | BNE  : BranchOp  -- 001
  | BLT  : BranchOp  -- 100
  | BGE  : BranchOp  -- 101
  | BLTU : BranchOp  -- 110
  | BGEU : BranchOp  -- 111
  deriving Repr, BEq, DecidableEq

/-- Encode branch op to funct3 -/
def BranchOp.toBitVec3 : BranchOp -> BitVec 3
  | .BEQ  => 0b000#3
  | .BNE  => 0b001#3
  | .BLT  => 0b100#3
  | .BGE  => 0b101#3
  | .BLTU => 0b110#3
  | .BGEU => 0b111#3

-- ============================================================================
-- Instruction Format Types
-- ============================================================================

/-- RV32I instruction format type -/
inductive InstrFormat where
  | R : InstrFormat  -- Register-Register (ADD, SUB, ...)
  | I : InstrFormat  -- Immediate (ADDI, LOAD, JALR)
  | S : InstrFormat  -- Store
  | B : InstrFormat  -- Branch
  | U : InstrFormat  -- Upper immediate (LUI, AUIPC)
  | J : InstrFormat  -- Jump (JAL)
  deriving Repr, BEq, DecidableEq

/-- Determine format from opcode -/
def InstrFormat.fromOpcode : Opcode -> InstrFormat
  | .ALU    => .R
  | .ALUI   => .I
  | .LOAD   => .I
  | .JALR   => .I
  | .STORE  => .S
  | .BRANCH => .B
  | .LUI    => .U
  | .AUIPC  => .U
  | .JAL    => .J
  | .FENCE  => .I
  | .SYSTEM => .I

-- ============================================================================
-- Control Signals (Pure Lean specification)
-- ============================================================================

/-- Control signals produced by the decoder -/
structure ControlSignals where
  aluOp       : ALUOp    -- ALU operation
  aluSrcB     : Bool     -- false = register, true = immediate
  regWrite    : Bool     -- Write to register file
  memRead     : Bool     -- Read from data memory
  memWrite    : Bool     -- Write to data memory
  memToReg    : Bool     -- false = ALU result, true = memory data
  branch      : Bool     -- Instruction is a branch
  jump        : Bool     -- Instruction is JAL or JALR
  auipc       : Bool     -- ALU src A = PC (for AUIPC)
  deriving Repr, BEq

-- ============================================================================
-- Immediate Extraction (Pure Lean specification)
-- ============================================================================

/-- Extract I-type immediate: inst[31:20] sign-extended to 32 bits -/
def extractImmI (inst : BitVec 32) : BitVec 32 :=
  let imm12 := (inst >>> 20).truncate 12
  imm12.signExtend 32

/-- Extract S-type immediate: {inst[31:25], inst[11:7]} sign-extended -/
def extractImmS (inst : BitVec 32) : BitVec 32 :=
  let hi := (inst >>> 25).truncate 7
  let lo := (inst >>> 7).truncate 5
  let imm12 : BitVec 12 := hi ++ lo
  imm12.signExtend 32

/-- Extract B-type immediate: {inst[31], inst[7], inst[30:25], inst[11:8], 0}
    sign-extended to 32 bits -/
def extractImmB (inst : BitVec 32) : BitVec 32 :=
  let bit12  := (inst >>> 31).truncate 1   -- inst[31]
  let bit11  := (inst >>> 7).truncate 1    -- inst[7]
  let hi6    := (inst >>> 25).truncate 6   -- inst[30:25]
  let lo4    := (inst >>> 8).truncate 4    -- inst[11:8]
  let imm13 : BitVec 13 := bit12 ++ bit11 ++ hi6 ++ lo4 ++ (0#1)
  imm13.signExtend 32

/-- Extract U-type immediate: inst[31:12] << 12 -/
def extractImmU (inst : BitVec 32) : BitVec 32 :=
  let hi20 := (inst >>> 12).truncate 20
  (hi20 ++ (0#12) : BitVec 32)

/-- Extract J-type immediate: {inst[31], inst[19:12], inst[20], inst[30:21], 0}
    sign-extended to 32 bits -/
def extractImmJ (inst : BitVec 32) : BitVec 32 :=
  let bit20   := (inst >>> 31).truncate 1   -- inst[31]
  let bits19_12 := (inst >>> 12).truncate 8 -- inst[19:12]
  let bit11   := (inst >>> 20).truncate 1   -- inst[20]
  let bits10_1 := (inst >>> 21).truncate 10 -- inst[30:21]
  let imm21 : BitVec 21 := bit20 ++ bits19_12 ++ bit11 ++ bits10_1 ++ (0#1)
  imm21.signExtend 32

-- ============================================================================
-- Field Extraction Helpers
-- ============================================================================

/-- Extract opcode field (bits [6:0]) -/
def extractOpcode (inst : BitVec 32) : BitVec 7 :=
  inst.truncate 7

/-- Extract rd field (bits [11:7]) -/
def extractRd (inst : BitVec 32) : BitVec 5 :=
  (inst >>> 7).truncate 5

/-- Extract funct3 field (bits [14:12]) -/
def extractFunct3 (inst : BitVec 32) : BitVec 3 :=
  (inst >>> 12).truncate 3

/-- Extract rs1 field (bits [19:15]) -/
def extractRs1 (inst : BitVec 32) : BitVec 5 :=
  (inst >>> 15).truncate 5

/-- Extract rs2 field (bits [24:20]) -/
def extractRs2 (inst : BitVec 32) : BitVec 5 :=
  (inst >>> 20).truncate 5

/-- Extract funct7 field (bits [31:25]) -/
def extractFunct7 (inst : BitVec 32) : BitVec 7 :=
  (inst >>> 25).truncate 7

-- ============================================================================
-- Reference ALU (Pure Lean specification for verification)
-- ============================================================================

/-- Pure Lean ALU computation for verification reference -/
def aluCompute (op : ALUOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .ADD  => a + b
  | .SUB  => a - b
  | .AND  => a &&& b
  | .OR   => a ||| b
  | .XOR  => a ^^^ b
  | .SLL  => a <<< (b.truncate 5)
  | .SRL  => a >>> (b.truncate 5)
  | .SRA  => BitVec.ofInt 32 (a.toInt / (2 ^ (b.truncate 5).toNat))
  | .SLT  => if a.toInt < b.toInt then 1#32 else 0#32
  | .SLTU => if a.toNat < b.toNat then 1#32 else 0#32
  | .PASS => b

-- ============================================================================
-- Reference Decoder (Pure Lean specification)
-- ============================================================================

/-- Decode ALU operation from opcode, funct3, funct7 -/
def decodeALUOp (opcode : BitVec 7) (funct3 : BitVec 3) (funct7 : BitVec 7) : ALUOp :=
  let isALU  := opcode == Opcode.toBitVec7 .ALU
  let isALUI := opcode == Opcode.toBitVec7 .ALUI
  if isALU || isALUI then
    match funct3.toNat with
    | 0 => -- ADD/SUB
      if isALU && funct7 == 0b0100000#7 then .SUB else .ADD
    | 1 => .SLL
    | 2 => .SLT
    | 3 => .SLTU
    | 4 => .XOR
    | 5 => -- SRL/SRA
      if funct7 == 0b0100000#7 then .SRA else .SRL
    | 6 => .OR
    | 7 => .AND
    | _ => .ADD  -- unreachable
  else if opcode == Opcode.toBitVec7 .LUI then
    .PASS
  else
    .ADD  -- Default for LOAD, STORE, AUIPC, JAL, JALR (address calc)

/-- Full decode to control signals -/
def decodeControlSignals (inst : BitVec 32) : ControlSignals :=
  let opcode := extractOpcode inst
  match Opcode.fromBitVec7 opcode with
  | some .ALU => {
      aluOp := decodeALUOp opcode (extractFunct3 inst) (extractFunct7 inst)
      aluSrcB := false, regWrite := true, memRead := false
      memWrite := false, memToReg := false, branch := false
      jump := false, auipc := false
    }
  | some .ALUI => {
      aluOp := decodeALUOp opcode (extractFunct3 inst) (extractFunct7 inst)
      aluSrcB := true, regWrite := true, memRead := false
      memWrite := false, memToReg := false, branch := false
      jump := false, auipc := false
    }
  | some .LOAD => {
      aluOp := .ADD, aluSrcB := true, regWrite := true
      memRead := true, memWrite := false, memToReg := true
      branch := false, jump := false, auipc := false
    }
  | some .STORE => {
      aluOp := .ADD, aluSrcB := true, regWrite := false
      memRead := false, memWrite := true, memToReg := false
      branch := false, jump := false, auipc := false
    }
  | some .BRANCH => {
      aluOp := .SUB, aluSrcB := false, regWrite := false
      memRead := false, memWrite := false, memToReg := false
      branch := true, jump := false, auipc := false
    }
  | some .LUI => {
      aluOp := .PASS, aluSrcB := true, regWrite := true
      memRead := false, memWrite := false, memToReg := false
      branch := false, jump := false, auipc := false
    }
  | some .AUIPC => {
      aluOp := .ADD, aluSrcB := true, regWrite := true
      memRead := false, memWrite := false, memToReg := false
      branch := false, jump := false, auipc := true
    }
  | some .JAL => {
      aluOp := .ADD, aluSrcB := true, regWrite := true
      memRead := false, memWrite := false, memToReg := false
      branch := false, jump := true, auipc := true
    }
  | some .JALR => {
      aluOp := .ADD, aluSrcB := true, regWrite := true
      memRead := false, memWrite := false, memToReg := false
      branch := false, jump := true, auipc := false
    }
  | _ => {
      aluOp := .ADD, aluSrcB := false, regWrite := false
      memRead := false, memWrite := false, memToReg := false
      branch := false, jump := false, auipc := false
    }

-- ============================================================================
-- Reference Branch Evaluator
-- ============================================================================

/-- Evaluate branch condition given funct3 and two register values -/
def evalBranch (funct3 : BitVec 3) (rs1Val rs2Val : BitVec 32) : Bool :=
  match funct3.toNat with
  | 0 => rs1Val == rs2Val              -- BEQ
  | 1 => rs1Val != rs2Val              -- BNE
  | 4 => rs1Val.toInt < rs2Val.toInt   -- BLT
  | 5 => rs1Val.toInt >= rs2Val.toInt  -- BGE
  | 6 => rs1Val.toNat < rs2Val.toNat   -- BLTU
  | 7 => rs1Val.toNat >= rs2Val.toNat  -- BGEU
  | _ => false

-- ============================================================================
-- Pipeline Stage State Types (for verification)
-- ============================================================================

/-- IF/ID pipeline register state -/
structure IF_ID_Reg where
  pc   : BitVec 32
  inst : BitVec 32
  deriving Repr, BEq

/-- ID/EX pipeline register state -/
structure ID_EX_Reg where
  pc       : BitVec 32
  rs1Val   : BitVec 32
  rs2Val   : BitVec 32
  imm      : BitVec 32
  rd       : BitVec 5
  funct3   : BitVec 3
  ctrl     : ControlSignals
  deriving Repr, BEq

/-- EX/MEM pipeline register (combined EX/MEM + WB) -/
structure EX_WB_Reg where
  aluResult : BitVec 32
  memRData  : BitVec 32
  rd        : BitVec 5
  ctrl      : ControlSignals
  deriving Repr, BEq

end Sparkle.Examples.RV32
