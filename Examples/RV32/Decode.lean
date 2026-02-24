/-
  RV32I Instruction Decoder — Sparkle HDL Module

  Combinational decoder that extracts fields from a 32-bit instruction and
  produces control signals for the pipeline.

  Inputs:  inst[31:0]
  Outputs: opcode[6:0], rd[4:0], funct3[2:0], rs1[4:0], rs2[4:0], funct7[6:0]
           imm[31:0], alu_op[3:0], alu_src_b, reg_write, mem_read, mem_write,
           mem_to_reg, is_branch, is_jump, auipc
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.Types

namespace Sparkle.Examples.RV32.Decode

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32
open CircuitM

-- ============================================================================
-- Opcode Constants (as Expr literals)
-- ============================================================================

private def opcLUI    : Expr := .const (Opcode.toBitVec7 .LUI).toNat 7
private def opcAUIPC  : Expr := .const (Opcode.toBitVec7 .AUIPC).toNat 7
private def opcJAL    : Expr := .const (Opcode.toBitVec7 .JAL).toNat 7
private def opcJALR   : Expr := .const (Opcode.toBitVec7 .JALR).toNat 7
private def opcBRANCH : Expr := .const (Opcode.toBitVec7 .BRANCH).toNat 7
private def opcLOAD   : Expr := .const (Opcode.toBitVec7 .LOAD).toNat 7
private def opcSTORE  : Expr := .const (Opcode.toBitVec7 .STORE).toNat 7
private def opcALUI   : Expr := .const (Opcode.toBitVec7 .ALUI).toNat 7
private def opcALU    : Expr := .const (Opcode.toBitVec7 .ALU).toNat 7

-- ============================================================================
-- Field Extraction Subcircuit
-- ============================================================================

/-- Extract all instruction fields from the 32-bit instruction word -/
def generateFieldExtraction : CircuitM Unit := do
  let inst := Expr.ref "inst"

  -- opcode = inst[6:0]
  let opcWire ← makeWire "opcode_field" (.bitVector 7)
  emitAssign opcWire (.slice inst 6 0)

  -- rd = inst[11:7]
  let rdWire ← makeWire "rd_field" (.bitVector 5)
  emitAssign rdWire (.slice inst 11 7)

  -- funct3 = inst[14:12]
  let f3Wire ← makeWire "funct3_field" (.bitVector 3)
  emitAssign f3Wire (.slice inst 14 12)

  -- rs1 = inst[19:15]
  let rs1Wire ← makeWire "rs1_field" (.bitVector 5)
  emitAssign rs1Wire (.slice inst 19 15)

  -- rs2 = inst[24:20]
  let rs2Wire ← makeWire "rs2_field" (.bitVector 5)
  emitAssign rs2Wire (.slice inst 24 20)

  -- funct7 = inst[31:25]
  let f7Wire ← makeWire "funct7_field" (.bitVector 7)
  emitAssign f7Wire (.slice inst 31 25)

  -- Drive outputs from internal wires
  emitAssign "opcode" (.ref opcWire)
  emitAssign "rd"     (.ref rdWire)
  emitAssign "funct3" (.ref f3Wire)
  emitAssign "rs1"    (.ref rs1Wire)
  emitAssign "rs2"    (.ref rs2Wire)
  emitAssign "funct7" (.ref f7Wire)

-- ============================================================================
-- Immediate Generation Subcircuit
-- ============================================================================

/-- Generate the immediate value based on instruction format.
    Uses mux tree keyed on the opcode to select the correct immediate format. -/
def generateImmGen : CircuitM Unit := do
  let inst := Expr.ref "inst"
  let opc  := Expr.ref "opcode"

  -- I-type immediate: sign-extend inst[31:20]
  let immI ← makeWire "imm_i" (.bitVector 32)
  let inst31 := Expr.slice inst 31 31  -- sign bit
  let immI_hi ← makeWire "imm_i_hi" (.bitVector 20)
  emitAssign immI_hi (Expr.mux inst31 (.const 0xFFFFF 20) (.const 0 20))
  emitAssign immI (.concat [.ref immI_hi, .slice inst 31 20])

  -- S-type immediate: {inst[31:25], inst[11:7]} sign-extended
  let immS ← makeWire "imm_s" (.bitVector 32)
  let immS_hi ← makeWire "imm_s_hi" (.bitVector 20)
  emitAssign immS_hi (Expr.mux inst31 (.const 0xFFFFF 20) (.const 0 20))
  emitAssign immS (.concat [.ref immS_hi, .slice inst 31 25, .slice inst 11 7])

  -- B-type immediate: {inst[31], inst[7], inst[30:25], inst[11:8], 0} sign-extended
  let immB ← makeWire "imm_b" (.bitVector 32)
  let immB_hi ← makeWire "imm_b_hi" (.bitVector 19)
  emitAssign immB_hi (Expr.mux inst31 (.const 0x7FFFF 19) (.const 0 19))
  emitAssign immB (.concat [.ref immB_hi, .slice inst 31 31,
    .slice inst 7 7, .slice inst 30 25, .slice inst 11 8, .const 0 1])

  -- U-type immediate: inst[31:12] << 12
  let immU ← makeWire "imm_u" (.bitVector 32)
  emitAssign immU (.concat [.slice inst 31 12, .const 0 12])

  -- J-type immediate: {inst[31], inst[19:12], inst[20], inst[30:21], 0} sign-extended
  let immJ ← makeWire "imm_j" (.bitVector 32)
  let immJ_hi ← makeWire "imm_j_hi" (.bitVector 11)
  emitAssign immJ_hi (Expr.mux inst31 (.const 0x7FF 11) (.const 0 11))
  emitAssign immJ (.concat [.ref immJ_hi, .slice inst 31 31,
    .slice inst 19 12, .slice inst 20 20, .slice inst 30 21, .const 0 1])

  -- Select immediate based on opcode using mux cascade
  -- Default to I-type; override for S, B, U, J
  let isStore  ← makeWire "is_store" .bit
  emitAssign isStore (.op .eq [opc, opcSTORE])
  let isBranch ← makeWire "is_branch" .bit
  emitAssign isBranch (.op .eq [opc, opcBRANCH])
  let isLUI    ← makeWire "is_lui" .bit
  emitAssign isLUI (.op .eq [opc, opcLUI])
  let isAUIPC  ← makeWire "is_auipc" .bit
  emitAssign isAUIPC (.op .eq [opc, opcAUIPC])
  let isJAL    ← makeWire "is_jal" .bit
  emitAssign isJAL (.op .eq [opc, opcJAL])

  -- Combine LUI | AUIPC for U-type
  let isUType ← makeWire "is_utype" .bit
  emitAssign isUType (.op .or [.ref isLUI, .ref isAUIPC])

  -- Mux cascade: JAL > U-type > Branch > Store > I-type (default)
  let selSB ← makeWire "sel_sb" (.bitVector 32)
  emitAssign selSB (Expr.mux (.ref isBranch) (.ref immB)
    (Expr.mux (.ref isStore) (.ref immS) (.ref immI)))

  let selSBU ← makeWire "sel_sbu" (.bitVector 32)
  emitAssign selSBU (Expr.mux (.ref isUType) (.ref immU) (.ref selSB))

  let immFinal ← makeWire "imm_final" (.bitVector 32)
  emitAssign immFinal (Expr.mux (.ref isJAL) (.ref immJ) (.ref selSBU))

  emitAssign "imm" (.ref immFinal)

-- ============================================================================
-- ALU Control Subcircuit
-- ============================================================================

/-- Generate ALU control signal from opcode, funct3, funct7.
    Encodes the ALUOp as a 4-bit value. -/
def generateALUControl : CircuitM Unit := do
  let opc := Expr.ref "opcode"
  let f3  := Expr.ref "funct3"
  let f7  := Expr.ref "funct7"

  -- Detect ALU/ALUI instructions
  let isALU  ← makeWire "is_alu_rr" .bit
  emitAssign isALU (.op .eq [opc, opcALU])
  let isALUI ← makeWire "is_alu_imm" .bit
  emitAssign isALUI (.op .eq [opc, opcALUI])
  let isALUany ← makeWire "is_alu_any" .bit
  emitAssign isALUany (.op .or [.ref isALU, .ref isALUI])

  -- funct7 bit 5 (distinguishes ADD/SUB, SRL/SRA)
  let f7_bit5 ← makeWire "f7_bit5" .bit
  emitAssign f7_bit5 (.slice f7 5 5)

  -- sub_flag: true for SUB (R-type with funct7[5]=1 and funct3=000)
  let isSub ← makeWire "is_sub" .bit
  let f3_is_0 ← makeWire "f3_is_0" .bit
  emitAssign f3_is_0 (.op .eq [f3, .const 0 3])
  emitAssign isSub (.op .and [.ref isALU, .ref f7_bit5, .ref f3_is_0])

  -- sra_flag: true for SRA (funct7[5]=1 and funct3=101)
  let isSRA ← makeWire "is_sra" .bit
  let f3_is_5 ← makeWire "f3_is_5" .bit
  emitAssign f3_is_5 (.op .eq [f3, .const 5 3])
  emitAssign isSRA (.op .and [.ref isALUany, .ref f7_bit5, .ref f3_is_5])

  -- Base ALU op from funct3 (for ALU/ALUI instructions)
  -- funct3 = 000 -> ADD(0), 001 -> SLL(5), 010 -> SLT(8), 011 -> SLTU(9)
  -- funct3 = 100 -> XOR(4), 101 -> SRL(6), 110 -> OR(3), 111 -> AND(2)
  -- We build this as a mux tree on funct3
  let baseOp ← makeWire "base_alu_op" (.bitVector 4)
  let f3_is_1 ← makeWire "f3_is_1" .bit
  emitAssign f3_is_1 (.op .eq [f3, .const 1 3])
  let f3_is_2 ← makeWire "f3_is_2" .bit
  emitAssign f3_is_2 (.op .eq [f3, .const 2 3])
  let f3_is_3 ← makeWire "f3_is_3" .bit
  emitAssign f3_is_3 (.op .eq [f3, .const 3 3])
  let f3_is_4 ← makeWire "f3_is_4" .bit
  emitAssign f3_is_4 (.op .eq [f3, .const 4 3])
  let f3_is_6 ← makeWire "f3_is_6" .bit
  emitAssign f3_is_6 (.op .eq [f3, .const 6 3])
  let f3_is_7 ← makeWire "f3_is_7" .bit
  emitAssign f3_is_7 (.op .eq [f3, .const 7 3])

  -- Mux cascade for base ALU op:
  -- funct3=7(AND=0x2) > 6(OR=0x3) > 5(SRL=0x6) > 4(XOR=0x4) >
  -- 3(SLTU=0x9) > 2(SLT=0x8) > 1(SLL=0x5) > 0(ADD=0x0)
  let add_val := ALUOp.toBitVec4 .ADD
  let sll_val := ALUOp.toBitVec4 .SLL
  let slt_val := ALUOp.toBitVec4 .SLT
  let sltu_val := ALUOp.toBitVec4 .SLTU
  let xor_val := ALUOp.toBitVec4 .XOR
  let srl_val := ALUOp.toBitVec4 .SRL
  let or_val  := ALUOp.toBitVec4 .OR
  let and_val := ALUOp.toBitVec4 .AND

  emitAssign baseOp
    (Expr.mux (.ref f3_is_7) (.const and_val.toNat 4)
    (Expr.mux (.ref f3_is_6) (.const or_val.toNat 4)
    (Expr.mux (.ref f3_is_5) (.const srl_val.toNat 4)
    (Expr.mux (.ref f3_is_4) (.const xor_val.toNat 4)
    (Expr.mux (.ref f3_is_3) (.const sltu_val.toNat 4)
    (Expr.mux (.ref f3_is_2) (.const slt_val.toNat 4)
    (Expr.mux (.ref f3_is_1) (.const sll_val.toNat 4)
      (.const add_val.toNat 4))))))))

  -- Apply SUB/SRA overrides
  let sub_val := ALUOp.toBitVec4 .SUB
  let sra_val := ALUOp.toBitVec4 .SRA
  let pass_val := ALUOp.toBitVec4 .PASS

  let aluOpAdj ← makeWire "alu_op_adj" (.bitVector 4)
  emitAssign aluOpAdj (Expr.mux (.ref isSub) (.const sub_val.toNat 4)
    (Expr.mux (.ref isSRA) (.const sra_val.toNat 4)
      (.ref baseOp)))

  -- For non-ALU instructions, select the appropriate op
  let isLUI ← makeWire "is_lui_ctrl" .bit
  emitAssign isLUI (.op .eq [opc, opcLUI])

  -- LUI: PASS, Branch: SUB, all others (LOAD/STORE/AUIPC/JAL/JALR): ADD
  let isBranch ← makeWire "is_branch_ctrl" .bit
  emitAssign isBranch (.op .eq [opc, opcBRANCH])

  let nonAluOp ← makeWire "non_alu_op" (.bitVector 4)
  emitAssign nonAluOp (Expr.mux (.ref isLUI) (.const pass_val.toNat 4)
    (Expr.mux (.ref isBranch) (.const sub_val.toNat 4)
      (.const add_val.toNat 4)))

  -- Final mux: use ALU-derived op for ALU/ALUI, otherwise non-ALU op
  emitAssign "alu_op" (Expr.mux (.ref isALUany) (.ref aluOpAdj) (.ref nonAluOp))

-- ============================================================================
-- Control Signal Generation
-- ============================================================================

/-- Generate all control signals based on opcode -/
def generateControlSignals : CircuitM Unit := do
  let opc := Expr.ref "opcode"

  -- Boolean control flags using opcode comparisons
  let isALUrr ← makeWire "ctrl_is_alu_rr" .bit
  emitAssign isALUrr (.op .eq [opc, opcALU])
  let isALUi ← makeWire "ctrl_is_alu_imm" .bit
  emitAssign isALUi (.op .eq [opc, opcALUI])
  let isLoad ← makeWire "ctrl_is_load" .bit
  emitAssign isLoad (.op .eq [opc, opcLOAD])
  let isStore ← makeWire "ctrl_is_store" .bit
  emitAssign isStore (.op .eq [opc, opcSTORE])
  let isBranch ← makeWire "ctrl_is_branch" .bit
  emitAssign isBranch (.op .eq [opc, opcBRANCH])
  let isLUI ← makeWire "ctrl_is_lui" .bit
  emitAssign isLUI (.op .eq [opc, opcLUI])
  let isAUIPC ← makeWire "ctrl_is_auipc" .bit
  emitAssign isAUIPC (.op .eq [opc, opcAUIPC])
  let isJAL ← makeWire "ctrl_is_jal" .bit
  emitAssign isJAL (.op .eq [opc, opcJAL])
  let isJALR ← makeWire "ctrl_is_jalr" .bit
  emitAssign isJALR (.op .eq [opc, opcJALR])

  -- alu_src_b: true for I-type, S-type, U-type, J-type (anything with immediate as ALU input B)
  let srcB ← makeWire "alu_src_b_w" .bit
  emitAssign srcB (.op .or [.ref isALUi,
    .op .or [.ref isLoad,
    .op .or [.ref isStore,
    .op .or [.ref isLUI,
    .op .or [.ref isAUIPC,
    .op .or [.ref isJAL, .ref isJALR]]]]]])
  emitAssign "alu_src_b" (.ref srcB)

  -- reg_write: true for ALU, ALUI, LOAD, LUI, AUIPC, JAL, JALR
  let regW ← makeWire "reg_write_w" .bit
  emitAssign regW (.op .or [.ref isALUrr,
    .op .or [.ref isALUi,
    .op .or [.ref isLoad,
    .op .or [.ref isLUI,
    .op .or [.ref isAUIPC,
    .op .or [.ref isJAL, .ref isJALR]]]]]])
  emitAssign "reg_write" (.ref regW)

  -- mem_read: true only for LOAD
  emitAssign "mem_read" (.ref isLoad)

  -- mem_write: true only for STORE
  emitAssign "mem_write" (.ref isStore)

  -- mem_to_reg: true only for LOAD
  emitAssign "mem_to_reg" (.ref isLoad)

  -- is_branch
  emitAssign "is_branch" (.ref isBranch)

  -- is_jump: JAL or JALR
  let jumpW ← makeWire "is_jump_w" .bit
  emitAssign jumpW (.op .or [.ref isJAL, .ref isJALR])
  emitAssign "is_jump" (.ref jumpW)

  -- auipc: true for AUIPC and JAL (ALU src A = PC)
  let auipcW ← makeWire "auipc_w" .bit
  emitAssign auipcW (.op .or [.ref isAUIPC, .ref isJAL])
  emitAssign "auipc" (.ref auipcW)

-- ============================================================================
-- Top-Level Decoder Module
-- ============================================================================

/-- Build the full RV32I decoder as a Sparkle module.
    All outputs are combinational (no registers). -/
def generateDecoder : CircuitM Unit := do
  -- Input: 32-bit instruction
  addInput "inst" (.bitVector 32)

  -- Outputs: Decoded fields
  addOutput "opcode"  (.bitVector 7)
  addOutput "rd"      (.bitVector 5)
  addOutput "funct3"  (.bitVector 3)
  addOutput "rs1"     (.bitVector 5)
  addOutput "rs2"     (.bitVector 5)
  addOutput "funct7"  (.bitVector 7)
  addOutput "imm"     (.bitVector 32)

  -- Outputs: Control signals
  addOutput "alu_op"    (.bitVector 4)
  addOutput "alu_src_b" .bit
  addOutput "reg_write" .bit
  addOutput "mem_read"  .bit
  addOutput "mem_write" .bit
  addOutput "mem_to_reg" .bit
  addOutput "is_branch" .bit
  addOutput "is_jump"   .bit
  addOutput "auipc"     .bit

  -- Generate subcircuits
  generateFieldExtraction
  generateImmGen
  generateALUControl
  generateControlSignals

/-- Build the decoder module -/
def buildDecoder : Module :=
  CircuitM.runModule "RV32I_Decoder" do
    generateDecoder

end Sparkle.Examples.RV32.Decode
