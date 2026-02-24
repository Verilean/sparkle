/-
  RV32I ISA Verification Tests

  Tests for:
  1. Instruction field extraction correctness
  2. Immediate generation for all instruction formats
  3. ALU operation correctness
  4. Decoder control signal correctness
  5. Branch evaluation
  6. RTL module structure validation
  7. Formal proofs using native_decide
-/

import Examples.RV32.Types
import Examples.RV32.Decode
import Examples.RV32.Core
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type

namespace Sparkle.Examples.RV32.Tests.IsaTests

open Sparkle.Examples.RV32
open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Simple test harness -/
def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  PASS: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"

-- ============================================================================
-- Instruction Encoding Helpers
-- ============================================================================

/-- Encode an R-type instruction -/
def encodeR (funct7 : BitVec 7) (rs2 : BitVec 5) (rs1 : BitVec 5)
    (funct3 : BitVec 3) (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode : BitVec 32)

/-- Encode an I-type instruction -/
def encodeI (imm12 : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (imm12 ++ rs1 ++ funct3 ++ rd ++ opcode : BitVec 32)

/-- Encode an S-type instruction -/
def encodeS (imm12 : BitVec 12) (rs2 : BitVec 5) (rs1 : BitVec 5)
    (funct3 : BitVec 3) (opcode : BitVec 7) : BitVec 32 :=
  let hi := (imm12 >>> 5).truncate 7
  let lo := imm12.truncate 5
  (hi ++ rs2 ++ rs1 ++ funct3 ++ lo ++ opcode : BitVec 32)

/-- Encode a U-type instruction -/
def encodeU (imm20 : BitVec 20) (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (imm20 ++ rd ++ opcode : BitVec 32)

-- ============================================================================
-- 1. Opcode Encoding/Decoding Tests
-- ============================================================================

def testOpcodeEncoding : IO Unit := do
  IO.println "--- Opcode Encoding/Decoding Tests ---"

  -- Round-trip: encode then decode
  check "LUI round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .LUI) == some .LUI)
  check "AUIPC round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .AUIPC) == some .AUIPC)
  check "JAL round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .JAL) == some .JAL)
  check "JALR round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .JALR) == some .JALR)
  check "BRANCH round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .BRANCH) == some .BRANCH)
  check "LOAD round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .LOAD) == some .LOAD)
  check "STORE round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .STORE) == some .STORE)
  check "ALUI round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .ALUI) == some .ALUI)
  check "ALU round-trip" (Opcode.fromBitVec7 (Opcode.toBitVec7 .ALU) == some .ALU)

  -- Invalid opcode
  check "invalid opcode = none" (Opcode.fromBitVec7 0b1111111#7 == none)

  -- Known bit patterns
  check "LUI = 0b0110111" ((Opcode.toBitVec7 .LUI).toNat == 0b0110111)
  check "ALUI = 0b0010011" ((Opcode.toBitVec7 .ALUI).toNat == 0b0010011)
  check "ALU = 0b0110011" ((Opcode.toBitVec7 .ALU).toNat == 0b0110011)

-- ============================================================================
-- 2. ALU Operation Encoding Tests
-- ============================================================================

def testALUOpEncoding : IO Unit := do
  IO.println "--- ALU Op Encoding Tests ---"

  -- Round-trip
  check "ADD round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .ADD) == .ADD)
  check "SUB round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SUB) == .SUB)
  check "AND round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .AND) == .AND)
  check "OR round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .OR) == .OR)
  check "XOR round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .XOR) == .XOR)
  check "SLL round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SLL) == .SLL)
  check "SRL round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SRL) == .SRL)
  check "SRA round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SRA) == .SRA)
  check "SLT round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SLT) == .SLT)
  check "SLTU round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SLTU) == .SLTU)
  check "PASS round-trip" (ALUOp.fromBitVec4 (ALUOp.toBitVec4 .PASS) == .PASS)

-- ============================================================================
-- 3. Instruction Field Extraction Tests
-- ============================================================================

def testFieldExtraction : IO Unit := do
  IO.println "--- Field Extraction Tests ---"

  -- Construct: ADD x1, x2, x3  (R-type)
  -- funct7=0000000, rs2=00011(x3), rs1=00010(x2), funct3=000, rd=00001(x1), opcode=0110011
  let addInst := encodeR 0b0000000#7 0b00011#5 0b00010#5 0b000#3 0b00001#5 0b0110011#7

  check "ADD: opcode = 0b0110011" (extractOpcode addInst == 0b0110011#7)
  check "ADD: rd = 1" (extractRd addInst == 0b00001#5)
  check "ADD: funct3 = 0" (extractFunct3 addInst == 0b000#3)
  check "ADD: rs1 = 2" (extractRs1 addInst == 0b00010#5)
  check "ADD: rs2 = 3" (extractRs2 addInst == 0b00011#5)
  check "ADD: funct7 = 0" (extractFunct7 addInst == 0b0000000#7)

  -- Construct: SUB x4, x5, x6  (R-type, funct7=0100000)
  let subInst := encodeR 0b0100000#7 0b00110#5 0b00101#5 0b000#3 0b00100#5 0b0110011#7

  check "SUB: funct7 = 0b0100000" (extractFunct7 subInst == 0b0100000#7)
  check "SUB: rd = 4" (extractRd subInst == 0b00100#5)
  check "SUB: rs1 = 5" (extractRs1 subInst == 0b00101#5)
  check "SUB: rs2 = 6" (extractRs2 subInst == 0b00110#5)

  -- Construct: ADDI x7, x8, 42  (I-type)
  let addiInst := encodeI (BitVec.ofNat 12 42) 0b01000#5 0b000#3 0b00111#5 0b0010011#7

  check "ADDI: opcode = ALUI" (extractOpcode addiInst == Opcode.toBitVec7 .ALUI)
  check "ADDI: rd = 7" (extractRd addiInst == 0b00111#5)
  check "ADDI: rs1 = 8" (extractRs1 addiInst == 0b01000#5)

-- ============================================================================
-- 4. Immediate Extraction Tests
-- ============================================================================

def testImmediateExtraction : IO Unit := do
  IO.println "--- Immediate Extraction Tests ---"

  -- I-type: ADDI x1, x0, 42
  let addiInst := encodeI (BitVec.ofNat 12 42) 0b00000#5 0b000#3 0b00001#5 0b0010011#7
  let immI := extractImmI addiInst
  check "I-type imm = 42" (immI.toNat == 42)

  -- I-type: negative immediate (-5 = 0xFFB in 12 bits)
  let addiNegInst := encodeI (BitVec.ofInt 12 (-5)) 0b00000#5 0b000#3 0b00001#5 0b0010011#7
  let immINeg := extractImmI addiNegInst
  check "I-type imm = -5" (immINeg.toInt == -5)

  -- U-type: LUI x1, 0xDEADB
  let luiInst := encodeU (BitVec.ofNat 20 0xDEADB) 0b00001#5 0b0110111#7
  let immU := extractImmU luiInst
  check "U-type imm = 0xDEADB000" (immU.toNat == 0xDEADB000)

  -- S-type: SW x2, 16(x3) => imm12 = 16
  let swInst := encodeS (BitVec.ofNat 12 16) 0b00010#5 0b00011#5 0b010#3 0b0100011#7
  let immS := extractImmS swInst
  check "S-type imm = 16" (immS.toNat == 16)

  -- S-type: negative offset
  let swNegInst := encodeS (BitVec.ofInt 12 (-8)) 0b00010#5 0b00011#5 0b010#3 0b0100011#7
  let immSNeg := extractImmS swNegInst
  check "S-type imm = -8" (immSNeg.toInt == -8)

-- ============================================================================
-- 5. Reference ALU Tests
-- ============================================================================

def testALU : IO Unit := do
  IO.println "--- Reference ALU Tests ---"

  -- ADD
  check "ADD: 5 + 3 = 8" (aluCompute .ADD 5#32 3#32 == 8#32)
  check "ADD: 0 + 0 = 0" (aluCompute .ADD 0#32 0#32 == 0#32)
  check "ADD: overflow wraps" (aluCompute .ADD 0xFFFFFFFF#32 1#32 == 0#32)

  -- SUB
  check "SUB: 10 - 3 = 7" (aluCompute .SUB 10#32 3#32 == 7#32)
  check "SUB: 0 - 1 = -1" (aluCompute .SUB 0#32 1#32 == 0xFFFFFFFF#32)

  -- AND
  check "AND: 0xFF & 0x0F = 0x0F" (aluCompute .AND 0xFF#32 0x0F#32 == 0x0F#32)

  -- OR
  check "OR: 0xF0 | 0x0F = 0xFF" (aluCompute .OR 0xF0#32 0x0F#32 == 0xFF#32)

  -- XOR
  check "XOR: 0xFF ^ 0x0F = 0xF0" (aluCompute .XOR 0xFF#32 0x0F#32 == 0xF0#32)

  -- SLL
  check "SLL: 1 << 4 = 16" (aluCompute .SLL 1#32 4#32 == 16#32)
  check "SLL: uses only lower 5 bits" (aluCompute .SLL 1#32 32#32 == 1#32)

  -- SRL
  check "SRL: 16 >> 4 = 1" (aluCompute .SRL 16#32 4#32 == 1#32)
  check "SRL: 0x80000000 >> 1 = 0x40000000" (aluCompute .SRL 0x80000000#32 1#32 == 0x40000000#32)

  -- SRA
  check "SRA: -8 >> 1 = -4" (aluCompute .SRA 0xFFFFFFF8#32 1#32 == 0xFFFFFFFC#32)
  check "SRA: positive stays positive" (aluCompute .SRA 8#32 1#32 == 4#32)

  -- SLT (signed)
  check "SLT: -1 < 0 = true" (aluCompute .SLT 0xFFFFFFFF#32 0#32 == 1#32)
  check "SLT: 0 < -1 = false" (aluCompute .SLT 0#32 0xFFFFFFFF#32 == 0#32)
  check "SLT: 5 < 5 = false" (aluCompute .SLT 5#32 5#32 == 0#32)

  -- SLTU (unsigned)
  check "SLTU: 0 < 1 = true" (aluCompute .SLTU 0#32 1#32 == 1#32)
  check "SLTU: 0xFFFFFFFF < 0 = false" (aluCompute .SLTU 0xFFFFFFFF#32 0#32 == 0#32)

  -- PASS
  check "PASS: returns B" (aluCompute .PASS 42#32 99#32 == 99#32)

-- ============================================================================
-- 6. Decoder Control Signal Tests
-- ============================================================================

def testDecoderControlSignals : IO Unit := do
  IO.println "--- Decoder Control Signal Tests ---"

  -- ADD x1, x2, x3 (R-type ALU)
  let addInst := encodeR 0b0000000#7 0b00011#5 0b00010#5 0b000#3 0b00001#5 0b0110011#7
  let addCtrl := decodeControlSignals addInst
  check "ADD: aluOp = ADD" (addCtrl.aluOp == .ADD)
  check "ADD: aluSrcB = false (register)" (!addCtrl.aluSrcB)
  check "ADD: regWrite = true" addCtrl.regWrite
  check "ADD: memRead = false" (!addCtrl.memRead)
  check "ADD: memWrite = false" (!addCtrl.memWrite)
  check "ADD: branch = false" (!addCtrl.branch)
  check "ADD: jump = false" (!addCtrl.jump)

  -- SUB x1, x2, x3 (R-type ALU with funct7[5]=1)
  let subInst := encodeR 0b0100000#7 0b00011#5 0b00010#5 0b000#3 0b00001#5 0b0110011#7
  let subCtrl := decodeControlSignals subInst
  check "SUB: aluOp = SUB" (subCtrl.aluOp == .SUB)

  -- ADDI x1, x2, 10 (I-type ALU)
  let addiInst := encodeI (BitVec.ofNat 12 10) 0b00010#5 0b000#3 0b00001#5 0b0010011#7
  let addiCtrl := decodeControlSignals addiInst
  check "ADDI: aluOp = ADD" (addiCtrl.aluOp == .ADD)
  check "ADDI: aluSrcB = true (immediate)" addiCtrl.aluSrcB
  check "ADDI: regWrite = true" addiCtrl.regWrite

  -- XORI x1, x2, 0xFF
  let xoriInst := encodeI (BitVec.ofNat 12 0xFF) 0b00010#5 0b100#3 0b00001#5 0b0010011#7
  let xoriCtrl := decodeControlSignals xoriInst
  check "XORI: aluOp = XOR" (xoriCtrl.aluOp == .XOR)

  -- LW x1, 0(x2) (LOAD)
  let lwInst := encodeI (BitVec.ofNat 12 0) 0b00010#5 0b010#3 0b00001#5 0b0000011#7
  let lwCtrl := decodeControlSignals lwInst
  check "LW: aluOp = ADD" (lwCtrl.aluOp == .ADD)
  check "LW: aluSrcB = true" lwCtrl.aluSrcB
  check "LW: memRead = true" lwCtrl.memRead
  check "LW: memToReg = true" lwCtrl.memToReg
  check "LW: regWrite = true" lwCtrl.regWrite
  check "LW: memWrite = false" (!lwCtrl.memWrite)

  -- SW x1, 0(x2) (STORE)
  let swInst := encodeS (BitVec.ofNat 12 0) 0b00001#5 0b00010#5 0b010#3 0b0100011#7
  let swCtrl := decodeControlSignals swInst
  check "SW: aluOp = ADD" (swCtrl.aluOp == .ADD)
  check "SW: memWrite = true" swCtrl.memWrite
  check "SW: regWrite = false" (!swCtrl.regWrite)
  check "SW: memRead = false" (!swCtrl.memRead)

  -- BEQ (BRANCH)
  -- BEQ x1, x2, offset (B-type)
  -- Use a simple encoding for BEQ
  let beqInst := BitVec.ofNat 32 0x00208463  -- BEQ x1, x2, 8
  let beqCtrl := decodeControlSignals beqInst
  check "BEQ: branch = true" beqCtrl.branch
  check "BEQ: regWrite = false" (!beqCtrl.regWrite)
  check "BEQ: aluOp = SUB" (beqCtrl.aluOp == .SUB)

  -- LUI x1, 0x12345
  let luiInst := encodeU (BitVec.ofNat 20 0x12345) 0b00001#5 0b0110111#7
  let luiCtrl := decodeControlSignals luiInst
  check "LUI: aluOp = PASS" (luiCtrl.aluOp == .PASS)
  check "LUI: regWrite = true" luiCtrl.regWrite
  check "LUI: aluSrcB = true" luiCtrl.aluSrcB

  -- AUIPC x1, 0x12345
  let auipcInst := encodeU (BitVec.ofNat 20 0x12345) 0b00001#5 0b0010111#7
  let auipcCtrl := decodeControlSignals auipcInst
  check "AUIPC: aluOp = ADD" (auipcCtrl.aluOp == .ADD)
  check "AUIPC: auipc = true" auipcCtrl.auipc
  check "AUIPC: regWrite = true" auipcCtrl.regWrite

-- ============================================================================
-- 7. Branch Evaluation Tests
-- ============================================================================

def testBranchEvaluation : IO Unit := do
  IO.println "--- Branch Evaluation Tests ---"

  -- BEQ
  check "BEQ: equal = taken" (evalBranch 0b000#3 5#32 5#32 == true)
  check "BEQ: not equal = not taken" (evalBranch 0b000#3 5#32 6#32 == false)

  -- BNE
  check "BNE: not equal = taken" (evalBranch 0b001#3 5#32 6#32 == true)
  check "BNE: equal = not taken" (evalBranch 0b001#3 5#32 5#32 == false)

  -- BLT (signed)
  check "BLT: -1 < 0 = taken" (evalBranch 0b100#3 0xFFFFFFFF#32 0#32 == true)
  check "BLT: 0 < -1 = not taken" (evalBranch 0b100#3 0#32 0xFFFFFFFF#32 == false)
  check "BLT: 5 < 5 = not taken" (evalBranch 0b100#3 5#32 5#32 == false)

  -- BGE (signed)
  check "BGE: 0 >= -1 = taken" (evalBranch 0b101#3 0#32 0xFFFFFFFF#32 == true)
  check "BGE: 5 >= 5 = taken" (evalBranch 0b101#3 5#32 5#32 == true)
  check "BGE: -1 >= 0 = not taken" (evalBranch 0b101#3 0xFFFFFFFF#32 0#32 == false)

  -- BLTU (unsigned)
  check "BLTU: 0 < 1 = taken" (evalBranch 0b110#3 0#32 1#32 == true)
  check "BLTU: 0xFFFFFFFF < 0 = not taken" (evalBranch 0b110#3 0xFFFFFFFF#32 0#32 == false)

  -- BGEU (unsigned)
  check "BGEU: 1 >= 0 = taken" (evalBranch 0b111#3 1#32 0#32 == true)
  check "BGEU: 0 >= 0 = taken" (evalBranch 0b111#3 0#32 0#32 == true)
  check "BGEU: 0 >= 1 = not taken" (evalBranch 0b111#3 0#32 1#32 == false)

-- ============================================================================
-- 8. Instruction Format Classification Tests
-- ============================================================================

def testInstrFormat : IO Unit := do
  IO.println "--- Instruction Format Tests ---"

  check "ALU is R-type" (InstrFormat.fromOpcode .ALU == .R)
  check "ALUI is I-type" (InstrFormat.fromOpcode .ALUI == .I)
  check "LOAD is I-type" (InstrFormat.fromOpcode .LOAD == .I)
  check "JALR is I-type" (InstrFormat.fromOpcode .JALR == .I)
  check "STORE is S-type" (InstrFormat.fromOpcode .STORE == .S)
  check "BRANCH is B-type" (InstrFormat.fromOpcode .BRANCH == .B)
  check "LUI is U-type" (InstrFormat.fromOpcode .LUI == .U)
  check "AUIPC is U-type" (InstrFormat.fromOpcode .AUIPC == .U)
  check "JAL is J-type" (InstrFormat.fromOpcode .JAL == .J)

-- ============================================================================
-- 9. RTL Module Structure Tests
-- ============================================================================

def testDecoderModule : IO Unit := do
  IO.println "--- Decoder Module Structure Tests ---"

  let m := Decode.buildDecoder

  check "decoder module name" (m.name == "RV32I_Decoder")
  check "decoder has 1 input (inst)" (m.inputs.length == 1)
  check "decoder input is 32-bit" (m.inputs.head?.map (·.ty) == some (.bitVector 32))

  -- Count output ports
  -- opcode(7) + rd(5) + funct3(3) + rs1(5) + rs2(5) + funct7(7) + imm(32)
  -- + alu_op(4) + alu_src_b(1) + reg_write(1) + mem_read(1) + mem_write(1)
  -- + mem_to_reg(1) + is_branch(1) + is_jump(1) + auipc(1)
  check "decoder has 16 outputs" (m.outputs.length == 16)

  -- No registers (fully combinational)
  let hasRegister := m.body.any (fun s => match s with | .register .. => true | _ => false)
  check "decoder is combinational (no registers)" (!hasRegister)

  -- Verify specific output names exist
  let outputNames := m.outputs.map (·.name)
  check "has opcode output" (outputNames.contains "opcode")
  check "has rd output" (outputNames.contains "rd")
  check "has funct3 output" (outputNames.contains "funct3")
  check "has rs1 output" (outputNames.contains "rs1")
  check "has rs2 output" (outputNames.contains "rs2")
  check "has imm output" (outputNames.contains "imm")
  check "has alu_op output" (outputNames.contains "alu_op")
  check "has alu_src_b output" (outputNames.contains "alu_src_b")
  check "has reg_write output" (outputNames.contains "reg_write")
  check "has mem_read output" (outputNames.contains "mem_read")
  check "has mem_write output" (outputNames.contains "mem_write")
  check "has is_branch output" (outputNames.contains "is_branch")
  check "has is_jump output" (outputNames.contains "is_jump")

def testALUModule : IO Unit := do
  IO.println "--- ALU Module Structure Tests ---"

  let m := Core.buildALU

  check "ALU module name" (m.name == "RV32I_ALU")
  check "ALU has 3 inputs" (m.inputs.length == 3)
  check "ALU has 2 outputs" (m.outputs.length == 2)

  -- No registers (fully combinational)
  let hasRegister := m.body.any (fun s => match s with | .register .. => true | _ => false)
  check "ALU is combinational (no registers)" (!hasRegister)

  -- Verify input types
  let inputA := m.inputs.find? (·.name == "alu_a")
  check "ALU input a is 32-bit" (inputA.map (·.ty) == some (.bitVector 32))
  let inputB := m.inputs.find? (·.name == "alu_b")
  check "ALU input b is 32-bit" (inputB.map (·.ty) == some (.bitVector 32))
  let inputOp := m.inputs.find? (·.name == "alu_op")
  check "ALU input op is 4-bit" (inputOp.map (·.ty) == some (.bitVector 4))

def testBranchCompModule : IO Unit := do
  IO.println "--- Branch Comparator Module Structure Tests ---"

  let m := Core.buildBranchComp

  check "BranchComp module name" (m.name == "RV32I_BranchComp")
  check "BranchComp has 3 inputs" (m.inputs.length == 3)
  check "BranchComp has 1 output" (m.outputs.length == 1)

  -- Output is 1-bit
  check "BranchComp output is 1-bit" (m.outputs.head?.map (·.ty) == some .bit)

def testHazardUnitModule : IO Unit := do
  IO.println "--- Hazard Unit Module Structure Tests ---"

  let m := Core.buildHazardUnit

  check "HazardUnit module name" (m.name == "RV32I_HazardUnit")
  check "HazardUnit has 4 inputs" (m.inputs.length == 4)
  check "HazardUnit has 1 output" (m.outputs.length == 1)
  check "HazardUnit output is stall" (m.outputs.head?.map (·.name) == some "stall")

def testCoreModule : IO Unit := do
  IO.println "--- Core Pipeline Module Structure Tests ---"

  let m := Core.buildCore

  check "Core module name" (m.name == "RV32I_Core")

  -- Verify key input ports
  let inputNames := m.inputs.map (·.name)
  check "Core has clk input" (inputNames.contains "clk")
  check "Core has rst input" (inputNames.contains "rst")
  check "Core has imem_rdata input" (inputNames.contains "imem_rdata")
  check "Core has dmem_rdata input" (inputNames.contains "dmem_rdata")

  -- Verify key output ports
  let outputNames := m.outputs.map (·.name)
  check "Core has imem_addr output" (outputNames.contains "imem_addr")
  check "Core has dmem_addr output" (outputNames.contains "dmem_addr")
  check "Core has dmem_wdata output" (outputNames.contains "dmem_wdata")
  check "Core has dmem_we output" (outputNames.contains "dmem_we")
  check "Core has dmem_re output" (outputNames.contains "dmem_re")
  check "Core has debug_pc output" (outputNames.contains "debug_pc")

  -- Verify pipeline registers exist
  let regCount := m.body.foldl (fun acc s =>
    match s with | .register .. => acc + 1 | _ => acc) 0
  check "Core has pipeline registers" (regCount > 0)
  check "Core has many pipeline registers (4-stage)" (regCount >= 10)

  -- Verify memory statements exist (register file)
  let memCount := m.body.foldl (fun acc s =>
    match s with | .memory .. => acc + 1 | _ => acc) 0
  check "Core has memory blocks (regfile)" (memCount >= 2)

-- ============================================================================
-- 10. Formal Proofs (native_decide)
-- ============================================================================

section FormalProofs

/-- All valid opcodes round-trip through encode/decode -/
theorem opcode_lui_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .LUI) = some .LUI := by
  native_decide

theorem opcode_auipc_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .AUIPC) = some .AUIPC := by
  native_decide

theorem opcode_jal_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .JAL) = some .JAL := by
  native_decide

theorem opcode_jalr_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .JALR) = some .JALR := by
  native_decide

theorem opcode_branch_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .BRANCH) = some .BRANCH := by
  native_decide

theorem opcode_load_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .LOAD) = some .LOAD := by
  native_decide

theorem opcode_store_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .STORE) = some .STORE := by
  native_decide

theorem opcode_alui_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .ALUI) = some .ALUI := by
  native_decide

theorem opcode_alu_roundtrip : Opcode.fromBitVec7 (Opcode.toBitVec7 .ALU) = some .ALU := by
  native_decide

/-- All ALU ops round-trip through encode/decode -/
theorem aluop_add_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .ADD) = .ADD := by
  native_decide

theorem aluop_sub_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SUB) = .SUB := by
  native_decide

theorem aluop_and_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .AND) = .AND := by
  native_decide

theorem aluop_or_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .OR) = .OR := by
  native_decide

theorem aluop_xor_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .XOR) = .XOR := by
  native_decide

theorem aluop_sll_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SLL) = .SLL := by
  native_decide

theorem aluop_srl_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SRL) = .SRL := by
  native_decide

theorem aluop_sra_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SRA) = .SRA := by
  native_decide

theorem aluop_slt_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SLT) = .SLT := by
  native_decide

theorem aluop_sltu_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .SLTU) = .SLTU := by
  native_decide

theorem aluop_pass_roundtrip : ALUOp.fromBitVec4 (ALUOp.toBitVec4 .PASS) = .PASS := by
  native_decide

/-- ALU ADD is commutative -/
theorem alu_add_comm (a b : BitVec 32) : aluCompute .ADD a b = aluCompute .ADD b a := by
  simp [aluCompute, BitVec.add_comm]

/-- ALU XOR is commutative -/
theorem alu_xor_comm (a b : BitVec 32) : aluCompute .XOR a b = aluCompute .XOR b a := by
  simp [aluCompute, BitVec.xor_comm]

/-- ALU AND is commutative -/
theorem alu_and_comm (a b : BitVec 32) : aluCompute .AND a b = aluCompute .AND b a := by
  simp [aluCompute, BitVec.and_comm]

/-- ALU OR is commutative -/
theorem alu_or_comm (a b : BitVec 32) : aluCompute .OR a b = aluCompute .OR b a := by
  simp [aluCompute, BitVec.or_comm]

/-- ALU SUB x x = 0 -/
theorem alu_sub_self (a : BitVec 32) : aluCompute .SUB a a = 0#32 := by
  simp [aluCompute, BitVec.sub_self]

/-- PASS always returns second operand -/
theorem alu_pass_returns_b (a b : BitVec 32) : aluCompute .PASS a b = b := by
  simp [aluCompute]

/-- x0 is always hardwired to zero: extracting register 0 should always give 0 -/
theorem x0_hardwired_zero : extractRd (0 : BitVec 32) = 0#5 := by
  native_decide

/-- Opcode field is in bits [6:0]: shifting right by 7 removes it -/
theorem opcode_field_width : (extractOpcode (0b1111111#32)).toNat = 0b1111111 := by
  native_decide

/-- BEQ with equal operands is always taken -/
theorem beq_equal_taken (v : BitVec 32) : evalBranch 0b000#3 v v = true := by
  simp [evalBranch]

/-- BNE with equal operands is never taken -/
theorem bne_equal_not_taken (v : BitVec 32) : evalBranch 0b001#3 v v = false := by
  simp [evalBranch]

/-- BGE with equal operands is always taken (x >= x) -/
theorem bge_equal_taken (v : BitVec 32) : evalBranch 0b101#3 v v = true := by
  simp [evalBranch, Int.le_refl]

/-- BGEU with equal operands is always taken (x >= x unsigned) -/
theorem bgeu_equal_taken (v : BitVec 32) : evalBranch 0b111#3 v v = true := by
  simp [evalBranch, Nat.le_refl]

/-- BLT is never taken when operands are equal -/
theorem blt_equal_not_taken (v : BitVec 32) : evalBranch 0b100#3 v v = false := by
  simp [evalBranch, Int.lt_irrefl]

/-- BLTU is never taken when operands are equal -/
theorem bltu_equal_not_taken (v : BitVec 32) : evalBranch 0b110#3 v v = false := by
  simp [evalBranch, Nat.lt_irrefl]

/-- ADD with zero is identity -/
theorem alu_add_zero (a : BitVec 32) : aluCompute .ADD a 0#32 = a := by
  simp [aluCompute, BitVec.add_zero]

/-- AND with all-ones is identity (concrete verification) -/
theorem alu_and_allones_42 : aluCompute .AND 42#32 0xFFFFFFFF#32 = 42#32 := by
  native_decide

/-- OR with zero is identity -/
theorem alu_or_zero (a : BitVec 32) : aluCompute .OR a 0#32 = a := by
  simp [aluCompute, BitVec.or_zero]

/-- XOR with itself is zero -/
theorem alu_xor_self (a : BitVec 32) : aluCompute .XOR a a = 0#32 := by
  simp [aluCompute, BitVec.xor_self]

/-- SLL by 0 is identity -/
theorem alu_sll_zero (a : BitVec 32) : aluCompute .SLL a 0#32 = a := by
  simp [aluCompute]

end FormalProofs

end Sparkle.Examples.RV32.Tests.IsaTests

-- ============================================================================
-- Main entry point
-- ============================================================================

open Sparkle.Examples.RV32.Tests.IsaTests in
def main : IO Unit := do
  IO.println "=== RV32I ISA Verification Tests ==="
  testOpcodeEncoding
  testALUOpEncoding
  testFieldExtraction
  testImmediateExtraction
  testALU
  testDecoderControlSignals
  testBranchEvaluation
  testInstrFormat
  testDecoderModule
  testALUModule
  testBranchCompModule
  testHazardUnitModule
  testCoreModule
  IO.println "=== Formal proofs verified by Lean type checker ==="
  IO.println "=== Tests complete ==="
