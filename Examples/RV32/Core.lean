/-
  RV32I 4-Stage Pipelined Core — Sparkle HDL Module

  Pipeline stages:
    IF  — Fetch instruction from instruction memory
    ID  — Decode instruction, read register file, detect hazards
    EX/MEM — ALU execution, branch resolution, data memory access
    WB  — Write-back to register file

  Hazard handling:
    - Load-use stall: 1-cycle stall when EX/MEM stage has mem_read and
      the following ID stage needs that register
    - Branch/Jump: flush IF/ID on taken branch or jump

  Interface:
    - Harvard architecture with separate I-mem and D-mem ports
    - Synchronous memory interfaces compatible with FPGA BRAMs
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.Types
import Examples.RV32.Decode

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.Core

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32
open CircuitM

-- ============================================================================
-- ALU Module (standalone)
-- ============================================================================

/-- Generate the 32-bit ALU.
    Inputs:  alu_a[31:0], alu_b[31:0], alu_op[3:0]
    Outputs: alu_result[31:0], alu_zero (1-bit) -/
def generateALU : CircuitM Unit := do
  addInput "alu_a" (.bitVector 32)
  addInput "alu_b" (.bitVector 32)
  addInput "alu_op" (.bitVector 4)
  addOutput "alu_result" (.bitVector 32)
  addOutput "alu_zero" .bit

  let a := Expr.ref "alu_a"
  let b := Expr.ref "alu_b"
  let op := Expr.ref "alu_op"

  let shamt ← makeWire "shamt" (.bitVector 5)
  emitAssign shamt (.slice b 4 0)

  let addR  ← makeWire "add_result" (.bitVector 32)
  emitAssign addR (Expr.add a b)
  let subR  ← makeWire "sub_result" (.bitVector 32)
  emitAssign subR (Expr.sub a b)
  let andR  ← makeWire "and_result" (.bitVector 32)
  emitAssign andR (Expr.and a b)
  let orR   ← makeWire "or_result" (.bitVector 32)
  emitAssign orR (Expr.or a b)
  let xorR  ← makeWire "xor_result" (.bitVector 32)
  emitAssign xorR (Expr.xor a b)
  let sllR  ← makeWire "sll_result" (.bitVector 32)
  emitAssign sllR (.op .shl [a, .concat [.const 0 27, .ref shamt]])
  let srlR  ← makeWire "srl_result" (.bitVector 32)
  emitAssign srlR (.op .shr [a, .concat [.const 0 27, .ref shamt]])
  let sraR  ← makeWire "sra_result" (.bitVector 32)
  emitAssign sraR (.op .asr [a, .concat [.const 0 27, .ref shamt]])
  let sltR  ← makeWire "slt_result" (.bitVector 32)
  emitAssign sltR (Expr.mux (.op .lt_s [a, b]) (.const 1 32) (.const 0 32))
  let sltuR ← makeWire "sltu_result" (.bitVector 32)
  emitAssign sltuR (Expr.mux (.op .lt_u [a, b]) (.const 1 32) (.const 0 32))

  let isOp0 ← makeWire "is_op_0" .bit
  emitAssign isOp0 (.op .eq [op, .const 0 4])
  let isOp1 ← makeWire "is_op_1" .bit
  emitAssign isOp1 (.op .eq [op, .const 1 4])
  let isOp2 ← makeWire "is_op_2" .bit
  emitAssign isOp2 (.op .eq [op, .const 2 4])
  let isOp3 ← makeWire "is_op_3" .bit
  emitAssign isOp3 (.op .eq [op, .const 3 4])
  let isOp4 ← makeWire "is_op_4" .bit
  emitAssign isOp4 (.op .eq [op, .const 4 4])
  let isOp5 ← makeWire "is_op_5" .bit
  emitAssign isOp5 (.op .eq [op, .const 5 4])
  let isOp6 ← makeWire "is_op_6" .bit
  emitAssign isOp6 (.op .eq [op, .const 6 4])
  let isOp7 ← makeWire "is_op_7" .bit
  emitAssign isOp7 (.op .eq [op, .const 7 4])
  let isOp8 ← makeWire "is_op_8" .bit
  emitAssign isOp8 (.op .eq [op, .const 8 4])
  let isOp9 ← makeWire "is_op_9" .bit
  emitAssign isOp9 (.op .eq [op, .const 9 4])

  emitAssign "alu_result"
    (Expr.mux (.ref isOp9) (.ref sltuR)
    (Expr.mux (.ref isOp8) (.ref sltR)
    (Expr.mux (.ref isOp7) (.ref sraR)
    (Expr.mux (.ref isOp6) (.ref srlR)
    (Expr.mux (.ref isOp5) (.ref sllR)
    (Expr.mux (.ref isOp4) (.ref xorR)
    (Expr.mux (.ref isOp3) (.ref orR)
    (Expr.mux (.ref isOp2) (.ref andR)
    (Expr.mux (.ref isOp1) (.ref subR)
    (Expr.mux (.ref isOp0) (.ref addR)
      b))))))))))

  emitAssign "alu_zero" (.op .eq [.ref subR, .const 0 32])

def buildALU : Module :=
  CircuitM.runModule "RV32I_ALU" do
    generateALU

-- ============================================================================
-- Branch Comparator Module (standalone)
-- ============================================================================

/-- Generate the branch comparator. -/
def generateBranchComp : CircuitM Unit := do
  addInput "br_a" (.bitVector 32)
  addInput "br_b" (.bitVector 32)
  addInput "br_funct3" (.bitVector 3)
  addOutput "br_taken" .bit

  let a := Expr.ref "br_a"
  let b := Expr.ref "br_b"
  let f3 := Expr.ref "br_funct3"

  let beq ← makeWire "beq" .bit
  emitAssign beq (.op .eq [a, b])
  let bne ← makeWire "bne" .bit
  emitAssign bne (.op .not [.ref beq])
  let blt ← makeWire "blt" .bit
  emitAssign blt (.op .lt_s [a, b])
  let bge ← makeWire "bge" .bit
  emitAssign bge (.op .not [.ref blt])
  let bltu ← makeWire "bltu" .bit
  emitAssign bltu (.op .lt_u [a, b])
  let bgeu ← makeWire "bgeu" .bit
  emitAssign bgeu (.op .not [.ref bltu])

  let f3_is_0 ← makeWire "brf3_is_0" .bit
  emitAssign f3_is_0 (.op .eq [f3, .const 0 3])
  let f3_is_1 ← makeWire "brf3_is_1" .bit
  emitAssign f3_is_1 (.op .eq [f3, .const 1 3])
  let f3_is_4 ← makeWire "brf3_is_4" .bit
  emitAssign f3_is_4 (.op .eq [f3, .const 4 3])
  let f3_is_5 ← makeWire "brf3_is_5" .bit
  emitAssign f3_is_5 (.op .eq [f3, .const 5 3])
  let f3_is_6 ← makeWire "brf3_is_6" .bit
  emitAssign f3_is_6 (.op .eq [f3, .const 6 3])
  let f3_is_7 ← makeWire "brf3_is_7" .bit
  emitAssign f3_is_7 (.op .eq [f3, .const 7 3])

  emitAssign "br_taken"
    (Expr.mux (.ref f3_is_7) (.ref bgeu)
    (Expr.mux (.ref f3_is_6) (.ref bltu)
    (Expr.mux (.ref f3_is_5) (.ref bge)
    (Expr.mux (.ref f3_is_4) (.ref blt)
    (Expr.mux (.ref f3_is_1) (.ref bne)
    (Expr.mux (.ref f3_is_0) (.ref beq)
      (.const 0 1)))))))

def buildBranchComp : Module :=
  CircuitM.runModule "RV32I_BranchComp" do
    generateBranchComp

-- ============================================================================
-- Hazard Detection Unit (standalone)
-- ============================================================================

/-- Generate the hazard detection unit. -/
def generateHazardUnit : CircuitM Unit := do
  addInput "ex_mem_read" .bit
  addInput "ex_rd" (.bitVector 5)
  addInput "id_rs1" (.bitVector 5)
  addInput "id_rs2" (.bitVector 5)
  addOutput "stall" .bit

  let exRd := Expr.ref "ex_rd"
  let idRs1 := Expr.ref "id_rs1"
  let idRs2 := Expr.ref "id_rs2"

  let rdNonZero ← makeWire "rd_nonzero" .bit
  emitAssign rdNonZero (.op .not [.op .eq [exRd, .const 0 5]])
  let rs1Match ← makeWire "rs1_match" .bit
  emitAssign rs1Match (.op .eq [exRd, idRs1])
  let rs2Match ← makeWire "rs2_match" .bit
  emitAssign rs2Match (.op .eq [exRd, idRs2])
  let anyMatch ← makeWire "any_match" .bit
  emitAssign anyMatch (.op .or [.ref rs1Match, .ref rs2Match])
  emitAssign "stall" (.op .and [.ref "ex_mem_read",
    .op .and [.ref rdNonZero, .ref anyMatch]])

def buildHazardUnit : Module :=
  CircuitM.runModule "RV32I_HazardUnit" do
    generateHazardUnit

-- ============================================================================
-- Pipeline Core: split into sub-functions to avoid maxRecDepth issues
-- ============================================================================

/-- Context wires shared between pipeline stages -/
structure PipelineWires where
  pcReg     : String
  pcPlus4   : String
  pcNext    : String
  flush     : String
  stall     : String
  -- Write-back forwarding (pre-created for register file BRAM)
  wrAddrFwd : String
  wrDataFwd : String
  wrEnFwd   : String
  -- Delayed PC for IFID alignment (accounts for IMEM BRAM 1-cycle latency)
  fetchPC     : String
  fetchPCPlus4 : String
  -- Previous-cycle WB forwarding (for pre-read bypass, see ID stage)
  prevWrAddr : String
  prevWrData : String
  prevWrEn   : String
  -- Delayed flush: extends flush by 1 cycle for 2-cycle IF delay
  flushDelay : String

/-- IF/ID pipeline register outputs -/
structure IFID_Wires where
  inst : String
  pc   : String
  pc4  : String

/-- Decoded signals from the ID stage -/
structure ID_Signals where
  opcode    : String
  rd        : String
  funct3    : String
  rs1       : String
  rs2       : String
  funct7    : String
  imm       : String
  aluOp     : String
  aluSrcB   : String
  regWrite  : String
  memRead   : String
  memWrite  : String
  memToReg  : String
  isBranch  : String
  isJump    : String
  auipc     : String
  isJalr    : String
  rs1Val    : String
  rs2Val    : String
  isCsr     : String
  isEcall   : String
  isEbreak  : String
  isMret    : String
  csrAddr   : String
  csrFunct3 : String

/-- ID/EX pipeline register outputs -/
structure IDEX_Wires where
  aluOp    : String
  regWrite : String
  memRead  : String
  memWrite : String
  memToReg : String
  branch   : String
  jump     : String
  auipc    : String
  aluSrcB  : String
  rs1Val   : String
  rs2Val   : String
  imm      : String
  rd       : String
  rs1Idx   : String  -- rs1 register index for forwarding
  rs2Idx   : String  -- rs2 register index for forwarding
  funct3   : String
  pc       : String
  pc4      : String
  isJalr   : String
  isCsr     : String
  isEcall   : String
  isEbreak  : String
  isMret    : String
  csrAddr   : String
  csrFunct3 : String

/-- Stage 1: IF — Instruction Fetch -/
def generateIF (pw : PipelineWires) : CircuitM Unit := do
  emitAssign pw.pcPlus4 (Expr.add (.ref pw.pcReg) (.const 4 32))
  -- CRITICAL: During a load-use stall, pcReg is held at its current value
  -- (2 instructions ahead of IFID). The IMEM BRAM reads at this address,
  -- producing the wrong instruction for when the stall clears. To fix this,
  -- during a stall we redirect the IMEM address to fetchPC (1 instruction
  -- ahead of IFID = the correct next instruction to enter IFID).
  emitAssign "imem_addr"
    (Expr.mux (.ref pw.stall)
      (.slice (.ref pw.fetchPC) (imemAddrBits + 1) 2)
      (.slice (.ref pw.pcReg) (imemAddrBits + 1) 2))
  emitAssign "debug_pc" (.ref pw.pcReg)

/-- IF/ID pipeline registers -/
def generateIFID (pw : PipelineWires) : CircuitM IFID_Wires := do
  let nopInst : Int := (Opcode.toBitVec7 .ALUI).toNat

  -- IFID instruction register:
  --   flush/flushDelay → NOP (wrong-path instruction must be squashed;
  --     flushDelay covers the 2nd wrong-path instruction from BRAM latency)
  --   stall → HOLD (instruction must stay in IFID for re-decode next cycle)
  --   normal → new instruction from IMEM BRAM
  let flushAny ← makeWire "flush_any" .bit
  emitAssign flushAny (.op .or [.ref pw.flush, .ref pw.flushDelay])
  let ifid_inst_in ← makeWire "ifid_inst_in" (.bitVector 32)
  let ifid_inst ← emitRegister "ifid_inst" "clk" "rst" (.ref ifid_inst_in) nopInst (.bitVector 32)
  emitAssign ifid_inst_in
    (Expr.mux (.ref flushAny) (.const nopInst 32)
    (Expr.mux (.ref pw.stall) (.ref ifid_inst)
      (.ref "imem_rdata")))

  -- IFID PC registers: hold on stall, update from fetchPC otherwise.
  -- fetchPC is delayed by 1 cycle from pcReg so ifid_pc aligns with IMEM BRAM output.
  let ifid_pc_in ← makeWire "ifid_pc_in" (.bitVector 32)
  let ifid_pc ← emitRegister "ifid_pc" "clk" "rst" (.ref ifid_pc_in) 0 (.bitVector 32)
  emitAssign ifid_pc_in (Expr.mux (.ref pw.stall) (.ref ifid_pc) (.ref pw.fetchPC))

  let ifid_pc4_in ← makeWire "ifid_pc4_in" (.bitVector 32)
  let ifid_pc4 ← emitRegister "ifid_pc4" "clk" "rst" (.ref ifid_pc4_in) 4 (.bitVector 32)
  emitAssign ifid_pc4_in (Expr.mux (.ref pw.stall) (.ref ifid_pc4) (.ref pw.fetchPCPlus4))

  return { inst := ifid_inst, pc := ifid_pc, pc4 := ifid_pc4 }

/-- Stage 2a: ID — Field extraction and immediate generation -/
def generateID_FieldsAndImm (pw : PipelineWires) (ifid : IFID_Wires) : CircuitM ID_Signals := do
  let id_opcode ← makeWire "id_opcode" (.bitVector 7)
  emitAssign id_opcode (.slice (.ref ifid.inst) 6 0)
  let id_rd ← makeWire "id_rd" (.bitVector 5)
  emitAssign id_rd (.slice (.ref ifid.inst) 11 7)
  let id_funct3 ← makeWire "id_funct3" (.bitVector 3)
  emitAssign id_funct3 (.slice (.ref ifid.inst) 14 12)
  let id_rs1 ← makeWire "id_rs1" (.bitVector 5)
  emitAssign id_rs1 (.slice (.ref ifid.inst) 19 15)
  let id_rs2 ← makeWire "id_rs2" (.bitVector 5)
  emitAssign id_rs2 (.slice (.ref ifid.inst) 24 20)
  let id_funct7 ← makeWire "id_funct7" (.bitVector 7)
  emitAssign id_funct7 (.slice (.ref ifid.inst) 31 25)

  -- Immediate generation
  let inst31 ← makeWire "inst31" .bit
  emitAssign inst31 (.slice (.ref ifid.inst) 31 31)

  -- I-type
  let id_imm_i ← makeWire "id_imm_i" (.bitVector 32)
  let imm_i_hi ← makeWire "imm_i_hi" (.bitVector 20)
  emitAssign imm_i_hi (Expr.mux (.ref inst31) (.const 0xFFFFF 20) (.const 0 20))
  emitAssign id_imm_i (.concat [.ref imm_i_hi, .slice (.ref ifid.inst) 31 20])

  -- S-type
  let id_imm_s ← makeWire "id_imm_s" (.bitVector 32)
  let imm_s_hi ← makeWire "imm_s_hi" (.bitVector 20)
  emitAssign imm_s_hi (Expr.mux (.ref inst31) (.const 0xFFFFF 20) (.const 0 20))
  emitAssign id_imm_s (.concat [.ref imm_s_hi, .slice (.ref ifid.inst) 31 25,
    .slice (.ref ifid.inst) 11 7])

  -- B-type
  let id_imm_b ← makeWire "id_imm_b" (.bitVector 32)
  let imm_b_hi ← makeWire "imm_b_hi" (.bitVector 19)
  emitAssign imm_b_hi (Expr.mux (.ref inst31) (.const 0x7FFFF 19) (.const 0 19))
  emitAssign id_imm_b (.concat [.ref imm_b_hi, .slice (.ref ifid.inst) 31 31,
    .slice (.ref ifid.inst) 7 7, .slice (.ref ifid.inst) 30 25,
    .slice (.ref ifid.inst) 11 8, .const 0 1])

  -- U-type
  let id_imm_u ← makeWire "id_imm_u" (.bitVector 32)
  emitAssign id_imm_u (.concat [.slice (.ref ifid.inst) 31 12, .const 0 12])

  -- J-type
  let id_imm_j ← makeWire "id_imm_j" (.bitVector 32)
  let imm_j_hi ← makeWire "imm_j_hi" (.bitVector 11)
  emitAssign imm_j_hi (Expr.mux (.ref inst31) (.const 0x7FF 11) (.const 0 11))
  emitAssign id_imm_j (.concat [.ref imm_j_hi, .slice (.ref ifid.inst) 31 31,
    .slice (.ref ifid.inst) 19 12, .slice (.ref ifid.inst) 20 20,
    .slice (.ref ifid.inst) 30 21, .const 0 1])

  -- Opcode comparisons for immediate selection
  let opcSTORE_val  : Int := (Opcode.toBitVec7 .STORE).toNat
  let opcBRANCH_val : Int := (Opcode.toBitVec7 .BRANCH).toNat
  let opcLUI_val    : Int := (Opcode.toBitVec7 .LUI).toNat
  let opcAUIPC_val  : Int := (Opcode.toBitVec7 .AUIPC).toNat
  let opcJAL_val    : Int := (Opcode.toBitVec7 .JAL).toNat

  let id_is_store ← makeWire "id_is_store" .bit
  emitAssign id_is_store (.op .eq [.ref id_opcode, .const opcSTORE_val 7])
  let id_is_branch ← makeWire "id_is_branch" .bit
  emitAssign id_is_branch (.op .eq [.ref id_opcode, .const opcBRANCH_val 7])
  let id_is_lui ← makeWire "id_is_lui" .bit
  emitAssign id_is_lui (.op .eq [.ref id_opcode, .const opcLUI_val 7])
  let id_is_auipc ← makeWire "id_is_auipc" .bit
  emitAssign id_is_auipc (.op .eq [.ref id_opcode, .const opcAUIPC_val 7])
  let id_is_utype ← makeWire "id_is_utype" .bit
  emitAssign id_is_utype (.op .or [.ref id_is_lui, .ref id_is_auipc])
  let id_is_jal ← makeWire "id_is_jal" .bit
  emitAssign id_is_jal (.op .eq [.ref id_opcode, .const opcJAL_val 7])

  -- Immediate mux
  let id_imm ← makeWire "id_imm" (.bitVector 32)
  emitAssign id_imm
    (Expr.mux (.ref id_is_jal) (.ref id_imm_j)
    (Expr.mux (.ref id_is_utype) (.ref id_imm_u)
    (Expr.mux (.ref id_is_branch) (.ref id_imm_b)
    (Expr.mux (.ref id_is_store) (.ref id_imm_s)
      (.ref id_imm_i)))))

  -- Control signal decode
  let opcALU_val  : Int := (Opcode.toBitVec7 .ALU).toNat
  let opcALUI_val : Int := (Opcode.toBitVec7 .ALUI).toNat
  let opcLOAD_val : Int := (Opcode.toBitVec7 .LOAD).toNat
  let opcJALR_val : Int := (Opcode.toBitVec7 .JALR).toNat

  let id_is_alu_rr ← makeWire "id_is_alu_rr" .bit
  emitAssign id_is_alu_rr (.op .eq [.ref id_opcode, .const opcALU_val 7])
  let id_is_alu_imm ← makeWire "id_is_alu_imm" .bit
  emitAssign id_is_alu_imm (.op .eq [.ref id_opcode, .const opcALUI_val 7])
  let id_is_alu_any ← makeWire "id_is_alu_any" .bit
  emitAssign id_is_alu_any (.op .or [.ref id_is_alu_rr, .ref id_is_alu_imm])
  let id_is_load ← makeWire "id_is_load" .bit
  emitAssign id_is_load (.op .eq [.ref id_opcode, .const opcLOAD_val 7])
  let id_is_jalr ← makeWire "id_is_jalr" .bit
  emitAssign id_is_jalr (.op .eq [.ref id_opcode, .const opcJALR_val 7])
  let id_is_jump ← makeWire "id_is_jump" .bit
  emitAssign id_is_jump (.op .or [.ref id_is_jal, .ref id_is_jalr])

  -- SYSTEM instruction decoding
  let opcSYSTEM_val : Int := (Opcode.toBitVec7 .SYSTEM).toNat
  let id_is_system ← makeWire "id_is_system" .bit
  emitAssign id_is_system (.op .eq [.ref id_opcode, .const opcSYSTEM_val 7])

  -- CSR address is in imm field (bits [31:20] of instruction)
  let id_csr_addr ← makeWire "id_csr_addr" (.bitVector 12)
  emitAssign id_csr_addr (.slice (.ref ifid.inst) 31 20)

  -- CSR funct3 (same as id_funct3, but named for clarity)
  let id_csr_funct3 ← makeWire "id_csr_funct3" (.bitVector 3)
  emitAssign id_csr_funct3 (.ref id_funct3)

  -- CSR operations: funct3 ∈ {001, 010, 011, 101, 110, 111}
  let id_funct3_nz ← makeWire "id_funct3_nz" .bit
  emitAssign id_funct3_nz (.op .not [.op .eq [.ref id_funct3, .const 0 3]])
  let id_is_csr ← makeWire "id_is_csr" .bit
  emitAssign id_is_csr (.op .and [.ref id_is_system, .ref id_funct3_nz])

  -- ECALL: funct3=000, rs2=00000, funct7=0000000
  let id_funct3_zero ← makeWire "id_funct3_zero" .bit
  emitAssign id_funct3_zero (.op .eq [.ref id_funct3, .const 0 3])
  let id_rs2_is_0 ← makeWire "id_rs2_is_0" .bit
  emitAssign id_rs2_is_0 (.op .eq [.ref id_rs2, .const 0 5])
  let id_funct7_is_0 ← makeWire "id_funct7_is_0" .bit
  emitAssign id_funct7_is_0 (.op .eq [.ref id_funct7, .const 0 7])
  let id_is_ecall ← makeWire "id_is_ecall" .bit
  emitAssign id_is_ecall (.op .and [.ref id_is_system,
    .op .and [.ref id_funct3_zero,
    .op .and [.ref id_rs2_is_0, .ref id_funct7_is_0]]])

  -- EBREAK: funct3=000, rs2=00001
  let id_rs2_is_1 ← makeWire "id_rs2_is_1" .bit
  emitAssign id_rs2_is_1 (.op .eq [.ref id_rs2, .const 1 5])
  let id_is_ebreak ← makeWire "id_is_ebreak" .bit
  emitAssign id_is_ebreak (.op .and [.ref id_is_system,
    .op .and [.ref id_funct3_zero,
    .op .and [.ref id_rs2_is_1, .ref id_funct7_is_0]]])

  -- MRET: funct3=000, rs2=00010, funct7=0011000
  let id_rs2_is_2 ← makeWire "id_rs2_is_2" .bit
  emitAssign id_rs2_is_2 (.op .eq [.ref id_rs2, .const 2 5])
  let id_funct7_mret ← makeWire "id_funct7_mret" .bit
  emitAssign id_funct7_mret (.op .eq [.ref id_funct7, .const 0b0011000 7])
  let id_is_mret ← makeWire "id_is_mret" .bit
  emitAssign id_is_mret (.op .and [.ref id_is_system,
    .op .and [.ref id_funct3_zero,
    .op .and [.ref id_rs2_is_2, .ref id_funct7_mret]]])

  -- ALU op from funct3
  let f7_bit5 ← makeWire "id_f7_bit5" .bit
  emitAssign f7_bit5 (.slice (.ref id_funct7) 5 5)

  let f3eq0 ← makeWire "id_f3eq0" .bit
  emitAssign f3eq0 (.op .eq [.ref id_funct3, .const 0 3])
  let f3eq1 ← makeWire "id_f3eq1" .bit
  emitAssign f3eq1 (.op .eq [.ref id_funct3, .const 1 3])
  let f3eq2 ← makeWire "id_f3eq2" .bit
  emitAssign f3eq2 (.op .eq [.ref id_funct3, .const 2 3])
  let f3eq3 ← makeWire "id_f3eq3" .bit
  emitAssign f3eq3 (.op .eq [.ref id_funct3, .const 3 3])
  let f3eq4 ← makeWire "id_f3eq4" .bit
  emitAssign f3eq4 (.op .eq [.ref id_funct3, .const 4 3])
  let f3eq5 ← makeWire "id_f3eq5" .bit
  emitAssign f3eq5 (.op .eq [.ref id_funct3, .const 5 3])
  let f3eq6 ← makeWire "id_f3eq6" .bit
  emitAssign f3eq6 (.op .eq [.ref id_funct3, .const 6 3])
  let f3eq7 ← makeWire "id_f3eq7" .bit
  emitAssign f3eq7 (.op .eq [.ref id_funct3, .const 7 3])

  let id_base_op ← makeWire "id_base_op" (.bitVector 4)
  emitAssign id_base_op
    (Expr.mux (.ref f3eq7) (.const (ALUOp.toBitVec4 .AND).toNat 4)
    (Expr.mux (.ref f3eq6) (.const (ALUOp.toBitVec4 .OR).toNat 4)
    (Expr.mux (.ref f3eq5) (.const (ALUOp.toBitVec4 .SRL).toNat 4)
    (Expr.mux (.ref f3eq4) (.const (ALUOp.toBitVec4 .XOR).toNat 4)
    (Expr.mux (.ref f3eq3) (.const (ALUOp.toBitVec4 .SLTU).toNat 4)
    (Expr.mux (.ref f3eq2) (.const (ALUOp.toBitVec4 .SLT).toNat 4)
    (Expr.mux (.ref f3eq1) (.const (ALUOp.toBitVec4 .SLL).toNat 4)
      (.const (ALUOp.toBitVec4 .ADD).toNat 4))))))))

  let id_is_sub ← makeWire "id_is_sub" .bit
  emitAssign id_is_sub (.op .and [.ref id_is_alu_rr, .op .and [.ref f7_bit5, .ref f3eq0]])
  let id_is_sra ← makeWire "id_is_sra" .bit
  emitAssign id_is_sra (.op .and [.ref id_is_alu_any, .op .and [.ref f7_bit5, .ref f3eq5]])

  let id_alu_op_adj ← makeWire "id_alu_op_adj" (.bitVector 4)
  emitAssign id_alu_op_adj
    (Expr.mux (.ref id_is_sub) (.const (ALUOp.toBitVec4 .SUB).toNat 4)
    (Expr.mux (.ref id_is_sra) (.const (ALUOp.toBitVec4 .SRA).toNat 4)
      (.ref id_base_op)))

  let id_non_alu_op ← makeWire "id_non_alu_op" (.bitVector 4)
  emitAssign id_non_alu_op
    (Expr.mux (.ref id_is_lui) (.const (ALUOp.toBitVec4 .PASS).toNat 4)
    (Expr.mux (.ref id_is_branch) (.const (ALUOp.toBitVec4 .SUB).toNat 4)
      (.const (ALUOp.toBitVec4 .ADD).toNat 4)))

  let id_alu_op ← makeWire "id_alu_op" (.bitVector 4)
  emitAssign id_alu_op (Expr.mux (.ref id_is_alu_any) (.ref id_alu_op_adj) (.ref id_non_alu_op))

  -- Control signals
  let id_alu_src_b ← makeWire "id_alu_src_b" .bit
  emitAssign id_alu_src_b (.op .or [.ref id_is_alu_imm,
    .op .or [.ref id_is_load,
    .op .or [.ref id_is_store,
    .op .or [.ref id_is_lui,
    .op .or [.ref id_is_auipc,
    .op .or [.ref id_is_jal, .ref id_is_jalr]]]]]])

  let id_reg_write ← makeWire "id_reg_write" .bit
  emitAssign id_reg_write (.op .or [.ref id_is_alu_rr,
    .op .or [.ref id_is_alu_imm,
    .op .or [.ref id_is_load,
    .op .or [.ref id_is_lui,
    .op .or [.ref id_is_auipc,
    .op .or [.ref id_is_jal,
    .op .or [.ref id_is_jalr, .ref id_is_csr]]]]]]])

  let id_mem_read ← makeWire "id_mem_read" .bit
  emitAssign id_mem_read (.ref id_is_load)
  let id_mem_write ← makeWire "id_mem_write" .bit
  emitAssign id_mem_write (.ref id_is_store)
  let id_mem_to_reg ← makeWire "id_mem_to_reg" .bit
  emitAssign id_mem_to_reg (.ref id_is_load)
  let id_auipc ← makeWire "id_auipc" .bit
  emitAssign id_auipc (.op .or [.ref id_is_auipc, .ref id_is_jal])

  -- Register file reads (using memory primitives for BRAM inference)
  -- Read addresses come from imem_rdata (BEFORE the IFID register) so the
  -- BRAM output aligns with the next cycle when the instruction is in IFID.
  -- The BRAM has 1-cycle read latency: address at cycle N → output at N+1.
  --
  -- On stall: IFID holds its instruction, so we must re-read the regfile
  -- with the HELD instruction's rs1/rs2 (from ifid_inst) instead of the
  -- new instruction from imem_rdata. This ensures the regfile output aligns
  -- with the held instruction when the stall clears.
  let pre_rs1 ← makeWire "pre_rs1" (.bitVector 5)
  emitAssign pre_rs1 (Expr.mux (.ref pw.stall)
    (.slice (.ref ifid.inst) 19 15)
    (.slice (.ref "imem_rdata") 19 15))
  let pre_rs2 ← makeWire "pre_rs2" (.bitVector 5)
  emitAssign pre_rs2 (Expr.mux (.ref pw.stall)
    (.slice (.ref ifid.inst) 24 20)
    (.slice (.ref "imem_rdata") 24 20))

  let rs1_data ← emitMemory "regfile_rs1" 5 32 "clk"
    (.ref pw.wrAddrFwd) (.ref pw.wrDataFwd) (.ref pw.wrEnFwd)
    (.ref pre_rs1)
  let rs2_data ← emitMemory "regfile_rs2" 5 32 "clk"
    (.ref pw.wrAddrFwd) (.ref pw.wrDataFwd) (.ref pw.wrEnFwd)
    (.ref pre_rs2)

  -- WB→ID bypass (two levels):
  --
  -- Level 1 (current WB): The current WB instruction writes to the regfile
  -- at the same posedge when the IFID instruction is decoded. If the WB rd
  -- matches the IFID rs1/rs2, bypass the WB data.
  --
  -- Level 2 (previous WB): Due to the 2-cycle IF delay, the regfile BRAM
  -- pre-read (from pre_rs1/pre_rs2) happens 1 cycle BEFORE the instruction
  -- enters IFID. If the WB at THAT cycle (= previous cycle relative to IFID)
  -- writes to the same register, the BRAM gets the stale value (read-before-
  -- write). The current-WB bypass misses this because it checks 1 cycle too
  -- late. The prevWr* registers capture that write so we can bypass here.
  --
  -- Priority: current WB > previous WB > BRAM output.
  let wb_bypass_rs1 ← makeWire "wb_bypass_rs1" .bit
  emitAssign wb_bypass_rs1 (.op .and [.ref pw.wrEnFwd,
    .op .eq [.ref pw.wrAddrFwd, .ref id_rs1]])
  let wb_bypass_rs2 ← makeWire "wb_bypass_rs2" .bit
  emitAssign wb_bypass_rs2 (.op .and [.ref pw.wrEnFwd,
    .op .eq [.ref pw.wrAddrFwd, .ref id_rs2]])
  let prev_wb_bypass_rs1 ← makeWire "prev_wb_bypass_rs1" .bit
  emitAssign prev_wb_bypass_rs1 (.op .and [.ref pw.prevWrEn,
    .op .eq [.ref pw.prevWrAddr, .ref id_rs1]])
  let prev_wb_bypass_rs2 ← makeWire "prev_wb_bypass_rs2" .bit
  emitAssign prev_wb_bypass_rs2 (.op .and [.ref pw.prevWrEn,
    .op .eq [.ref pw.prevWrAddr, .ref id_rs2]])
  let rs1_bypassed ← makeWire "rs1_bypassed" (.bitVector 32)
  emitAssign rs1_bypassed (Expr.mux (.ref wb_bypass_rs1)
    (.ref pw.wrDataFwd)
    (Expr.mux (.ref prev_wb_bypass_rs1)
      (.ref pw.prevWrData) (.ref rs1_data)))
  let rs2_bypassed ← makeWire "rs2_bypassed" (.bitVector 32)
  emitAssign rs2_bypassed (Expr.mux (.ref wb_bypass_rs2)
    (.ref pw.wrDataFwd)
    (Expr.mux (.ref prev_wb_bypass_rs2)
      (.ref pw.prevWrData) (.ref rs2_data)))

  -- x0 hardwiring
  let rs1_zero ← makeWire "rs1_is_zero" .bit
  emitAssign rs1_zero (.op .eq [.ref id_rs1, .const 0 5])
  let rs2_zero ← makeWire "rs2_is_zero" .bit
  emitAssign rs2_zero (.op .eq [.ref id_rs2, .const 0 5])
  let rs1_val ← makeWire "rs1_val" (.bitVector 32)
  emitAssign rs1_val (Expr.mux (.ref rs1_zero) (.const 0 32) (.ref rs1_bypassed))
  let rs2_val ← makeWire "rs2_val" (.bitVector 32)
  emitAssign rs2_val (Expr.mux (.ref rs2_zero) (.const 0 32) (.ref rs2_bypassed))

  return {
    opcode := id_opcode, rd := id_rd, funct3 := id_funct3
    rs1 := id_rs1, rs2 := id_rs2, funct7 := id_funct7
    imm := id_imm, aluOp := id_alu_op, aluSrcB := id_alu_src_b
    regWrite := id_reg_write, memRead := id_mem_read
    memWrite := id_mem_write, memToReg := id_mem_to_reg
    isBranch := id_is_branch, isJump := id_is_jump
    auipc := id_auipc, isJalr := id_is_jalr
    rs1Val := rs1_val, rs2Val := rs2_val
    isCsr := id_is_csr, isEcall := id_is_ecall
    isEbreak := id_is_ebreak, isMret := id_is_mret
    csrAddr := id_csr_addr, csrFunct3 := id_csr_funct3
  }

/-- Hazard detection between ID and EX/MEM stages -/
def generateHazardDetection (pw : PipelineWires)
    (idSig : ID_Signals) (exMemRead exRd : String) : CircuitM Unit := do
  let rd_nz ← makeWire "hz_rd_nz" .bit
  emitAssign rd_nz (.op .not [.op .eq [.ref exRd, .const 0 5]])
  let rs1m ← makeWire "hz_rs1m" .bit
  emitAssign rs1m (.op .eq [.ref exRd, .ref idSig.rs1])
  let rs2m ← makeWire "hz_rs2m" .bit
  emitAssign rs2m (.op .eq [.ref exRd, .ref idSig.rs2])
  let anym ← makeWire "hz_anym" .bit
  emitAssign anym (.op .or [.ref rs1m, .ref rs2m])
  emitAssign pw.stall (.op .and [.ref exMemRead,
    .op .and [.ref rd_nz, .ref anym]])

/-- ID/EX pipeline registers -/
def generateIDEX (pw : PipelineWires) (idSig : ID_Signals) (ifid : IFID_Wires)
    : CircuitM IDEX_Wires := do
  -- Helper: register with bubble on stall OR flush OR flushDelay.
  -- On stall: insert bubble because load-use hazard (IDEX holds dependent instruction)
  -- On flush/flushDelay: insert bubble because the instruction in IFID is from the wrong path
  --   (flushDelay covers the 2nd wrong-path instruction from 2-cycle BRAM latency)
  let squash ← makeWire "idex_squash" .bit
  emitAssign squash (.op .or [.ref pw.stall, .op .or [.ref pw.flush, .ref pw.flushDelay]])
  let mkCtrlReg (hint : String) (input : String) (ty : HWType) : CircuitM String := do
    let muxIn ← makeWire s!"idex_in_{hint}" ty
    let zeroVal := match ty with | .bit => 1 | .bitVector w => w | _ => 1
    emitAssign muxIn (Expr.mux (.ref squash) (.const 0 zeroVal) (.ref input))
    emitRegister s!"idex_{hint}" "clk" "rst" (.ref muxIn) 0 ty

  let aluOp ← mkCtrlReg "alu_op" idSig.aluOp (.bitVector 4)
  let regWrite ← mkCtrlReg "reg_write" idSig.regWrite .bit
  let memRead ← mkCtrlReg "mem_read" idSig.memRead .bit
  let memWrite ← mkCtrlReg "mem_write" idSig.memWrite .bit
  let memToReg ← mkCtrlReg "mem_to_reg" idSig.memToReg .bit
  let branch ← mkCtrlReg "branch" idSig.isBranch .bit
  let jump ← mkCtrlReg "jump" idSig.isJump .bit
  let auipc ← mkCtrlReg "auipc" idSig.auipc .bit
  let aluSrcB ← mkCtrlReg "alu_src_b" idSig.aluSrcB .bit
  let isJalr ← mkCtrlReg "is_jalr" idSig.isJalr .bit
  let isCsr ← mkCtrlReg "is_csr" idSig.isCsr .bit
  let isEcall ← mkCtrlReg "is_ecall" idSig.isEcall .bit
  let isEbreak ← mkCtrlReg "is_ebreak" idSig.isEbreak .bit
  let isMret ← mkCtrlReg "is_mret" idSig.isMret .bit

  let csrAddrIn ← makeWire "idex_in_csr_addr" (.bitVector 12)
  emitAssign csrAddrIn (Expr.mux (.ref squash) (.const 0 12) (.ref idSig.csrAddr))
  let csrAddr ← emitRegister "idex_csr_addr" "clk" "rst" (.ref csrAddrIn) 0 (.bitVector 12)
  let csrFunct3 ← emitRegister "idex_csr_funct3" "clk" "rst" (.ref idSig.csrFunct3) 0 (.bitVector 3)

  -- Data registers (always pass through)
  let rs1Val ← emitRegister "idex_rs1_val" "clk" "rst" (.ref idSig.rs1Val) 0 (.bitVector 32)
  let rs2Val ← emitRegister "idex_rs2_val" "clk" "rst" (.ref idSig.rs2Val) 0 (.bitVector 32)
  let imm ← emitRegister "idex_imm" "clk" "rst" (.ref idSig.imm) 0 (.bitVector 32)

  -- rd with stall/flush bubble
  let rdIn ← makeWire "idex_in_rd" (.bitVector 5)
  emitAssign rdIn (Expr.mux (.ref squash) (.const 0 5) (.ref idSig.rd))
  let rd ← emitRegister "idex_rd" "clk" "rst" (.ref rdIn) 0 (.bitVector 5)

  -- rs1/rs2 register indices (needed for forwarding in EX stage)
  let rs1Idx ← emitRegister "idex_rs1_idx" "clk" "rst" (.ref idSig.rs1) 0 (.bitVector 5)
  let rs2Idx ← emitRegister "idex_rs2_idx" "clk" "rst" (.ref idSig.rs2) 0 (.bitVector 5)

  let funct3 ← emitRegister "idex_funct3" "clk" "rst" (.ref idSig.funct3) 0 (.bitVector 3)
  let pc ← emitRegister "idex_pc" "clk" "rst" (.ref ifid.pc) 0 (.bitVector 32)
  let pc4 ← emitRegister "idex_pc4" "clk" "rst" (.ref ifid.pc4) 0 (.bitVector 32)

  return {
    aluOp, regWrite, memRead, memWrite, memToReg
    branch, jump, auipc, aluSrcB, rs1Val, rs2Val
    imm, rd, rs1Idx, rs2Idx, funct3, pc, pc4, isJalr
    isCsr, isEcall, isEbreak, isMret, csrAddr, csrFunct3
  }

/-- Stage 3: EX/MEM — ALU, branch resolution, data memory -/
def generateEXMEM (pw : PipelineWires) (idex : IDEX_Wires) : CircuitM Unit := do
  -- =========================================================================
  -- WB→EX Forwarding
  -- =========================================================================
  -- If the WB stage is writing to a register that EX is reading, forward
  -- the WB result instead of the stale BRAM output.
  -- Forwarding condition: wb_we && wb_rd != 0 && wb_rd == ex_rs_idx
  let fwd_rs1_match ← makeWire "fwd_rs1_match" .bit
  emitAssign fwd_rs1_match (.op .and [.ref pw.wrEnFwd,
    .op .eq [.ref pw.wrAddrFwd, .ref idex.rs1Idx]])
  let fwd_rs2_match ← makeWire "fwd_rs2_match" .bit
  emitAssign fwd_rs2_match (.op .and [.ref pw.wrEnFwd,
    .op .eq [.ref pw.wrAddrFwd, .ref idex.rs2Idx]])

  let ex_rs1 ← makeWire "ex_rs1_fwd" (.bitVector 32)
  emitAssign ex_rs1 (Expr.mux (.ref fwd_rs1_match)
    (.ref pw.wrDataFwd) (.ref idex.rs1Val))
  let ex_rs2 ← makeWire "ex_rs2_fwd" (.bitVector 32)
  emitAssign ex_rs2 (Expr.mux (.ref fwd_rs2_match)
    (.ref pw.wrDataFwd) (.ref idex.rs2Val))

  -- ALU operand A: PC for AUIPC/JAL, otherwise rs1 (forwarded)
  let alu_a ← makeWire "alu_a" (.bitVector 32)
  emitAssign alu_a (Expr.mux (.ref idex.auipc) (.ref idex.pc) (.ref ex_rs1))

  -- ALU operand B: immediate or rs2 (forwarded)
  let alu_b ← makeWire "alu_b" (.bitVector 32)
  emitAssign alu_b (Expr.mux (.ref idex.aluSrcB) (.ref idex.imm) (.ref ex_rs2))

  -- ALU results
  let addR  ← makeWire "ex_add" (.bitVector 32)
  emitAssign addR (Expr.add (.ref alu_a) (.ref alu_b))
  let subR  ← makeWire "ex_sub" (.bitVector 32)
  emitAssign subR (Expr.sub (.ref alu_a) (.ref alu_b))
  let andR  ← makeWire "ex_and" (.bitVector 32)
  emitAssign andR (Expr.and (.ref alu_a) (.ref alu_b))
  let orR   ← makeWire "ex_or" (.bitVector 32)
  emitAssign orR (Expr.or (.ref alu_a) (.ref alu_b))
  let xorR  ← makeWire "ex_xor" (.bitVector 32)
  emitAssign xorR (Expr.xor (.ref alu_a) (.ref alu_b))
  let shamt ← makeWire "ex_shamt" (.bitVector 5)
  emitAssign shamt (.slice (.ref alu_b) 4 0)
  let shamtExt ← makeWire "ex_shamt_ext" (.bitVector 32)
  emitAssign shamtExt (.concat [.const 0 27, .ref shamt])
  let sllR  ← makeWire "ex_sll" (.bitVector 32)
  emitAssign sllR (.op .shl [.ref alu_a, .ref shamtExt])
  let srlR  ← makeWire "ex_srl" (.bitVector 32)
  emitAssign srlR (.op .shr [.ref alu_a, .ref shamtExt])
  let sraR  ← makeWire "ex_sra" (.bitVector 32)
  emitAssign sraR (.op .asr [.ref alu_a, .ref shamtExt])
  let sltR  ← makeWire "ex_slt" (.bitVector 32)
  emitAssign sltR (Expr.mux (.op .lt_s [.ref alu_a, .ref alu_b]) (.const 1 32) (.const 0 32))
  let sltuR ← makeWire "ex_sltu" (.bitVector 32)
  emitAssign sltuR (Expr.mux (.op .lt_u [.ref alu_a, .ref alu_b]) (.const 1 32) (.const 0 32))

  -- ALU result mux
  let isOp0 ← makeWire "ex_isop0" .bit
  emitAssign isOp0 (.op .eq [.ref idex.aluOp, .const 0 4])
  let isOp1 ← makeWire "ex_isop1" .bit
  emitAssign isOp1 (.op .eq [.ref idex.aluOp, .const 1 4])
  let isOp2 ← makeWire "ex_isop2" .bit
  emitAssign isOp2 (.op .eq [.ref idex.aluOp, .const 2 4])
  let isOp3 ← makeWire "ex_isop3" .bit
  emitAssign isOp3 (.op .eq [.ref idex.aluOp, .const 3 4])
  let isOp4 ← makeWire "ex_isop4" .bit
  emitAssign isOp4 (.op .eq [.ref idex.aluOp, .const 4 4])
  let isOp5 ← makeWire "ex_isop5" .bit
  emitAssign isOp5 (.op .eq [.ref idex.aluOp, .const 5 4])
  let isOp6 ← makeWire "ex_isop6" .bit
  emitAssign isOp6 (.op .eq [.ref idex.aluOp, .const 6 4])
  let isOp7 ← makeWire "ex_isop7" .bit
  emitAssign isOp7 (.op .eq [.ref idex.aluOp, .const 7 4])
  let isOp8 ← makeWire "ex_isop8" .bit
  emitAssign isOp8 (.op .eq [.ref idex.aluOp, .const 8 4])
  let isOp9 ← makeWire "ex_isop9" .bit
  emitAssign isOp9 (.op .eq [.ref idex.aluOp, .const 9 4])

  let alu_result ← makeWire "alu_result" (.bitVector 32)
  emitAssign alu_result
    (Expr.mux (.ref isOp9) (.ref sltuR)
    (Expr.mux (.ref isOp8) (.ref sltR)
    (Expr.mux (.ref isOp7) (.ref sraR)
    (Expr.mux (.ref isOp6) (.ref srlR)
    (Expr.mux (.ref isOp5) (.ref sllR)
    (Expr.mux (.ref isOp4) (.ref xorR)
    (Expr.mux (.ref isOp3) (.ref orR)
    (Expr.mux (.ref isOp2) (.ref andR)
    (Expr.mux (.ref isOp1) (.ref subR)
    (Expr.mux (.ref isOp0) (.ref addR)
      (.ref alu_b)))))))))))

  -- Full 32-bit bus address for SoC bus routing (CLINT vs DMEM)
  emitAssign "bus_addr" (.ref alu_result)

  -- CSR interface signals
  -- CSR write data: register value for CSRRW/CSRRS/CSRRC, zimm for immediate variants
  -- funct3[2] = 1 → immediate variant, use zero-extended rs1 field (5 bits)
  let csrIsImm ← makeWire "csr_is_imm" .bit
  emitAssign csrIsImm (.slice (.ref idex.csrFunct3) 2 2)
  let csrZimm ← makeWire "csr_zimm" (.bitVector 32)
  emitAssign csrZimm (.concat [.const 0 27, .ref idex.rs1Idx])
  let csrWdataMux ← makeWire "csr_wdata_mux" (.bitVector 32)
  emitAssign csrWdataMux (Expr.mux (.ref csrIsImm) (.ref csrZimm) (.ref ex_rs1))

  emitAssign "csr_addr" (.ref idex.csrAddr)
  emitAssign "csr_funct3" (.ref idex.csrFunct3)
  emitAssign "csr_wdata" (.ref csrWdataMux)
  emitAssign "csr_we" (.ref idex.isCsr)

  -- Trap signals
  emitAssign "trap_ecall" (.ref idex.isEcall)
  emitAssign "trap_ebreak" (.ref idex.isEbreak)
  emitAssign "trap_mret" (.ref idex.isMret)
  emitAssign "trap_pc" (.ref idex.pc)

  -- Branch condition evaluation (using forwarded values)
  let beq ← makeWire "ex_beq" .bit
  emitAssign beq (.op .eq [.ref ex_rs1, .ref ex_rs2])
  let blt ← makeWire "ex_blt" .bit
  emitAssign blt (.op .lt_s [.ref ex_rs1, .ref ex_rs2])
  let bltu ← makeWire "ex_bltu" .bit
  emitAssign bltu (.op .lt_u [.ref ex_rs1, .ref ex_rs2])

  let br_f3_0 ← makeWire "br_f3_0" .bit
  emitAssign br_f3_0 (.op .eq [.ref idex.funct3, .const 0 3])
  let br_f3_1 ← makeWire "br_f3_1" .bit
  emitAssign br_f3_1 (.op .eq [.ref idex.funct3, .const 1 3])
  let br_f3_4 ← makeWire "br_f3_4" .bit
  emitAssign br_f3_4 (.op .eq [.ref idex.funct3, .const 4 3])
  let br_f3_5 ← makeWire "br_f3_5" .bit
  emitAssign br_f3_5 (.op .eq [.ref idex.funct3, .const 5 3])
  let br_f3_6 ← makeWire "br_f3_6" .bit
  emitAssign br_f3_6 (.op .eq [.ref idex.funct3, .const 6 3])
  let br_f3_7 ← makeWire "br_f3_7" .bit
  emitAssign br_f3_7 (.op .eq [.ref idex.funct3, .const 7 3])

  let brCond ← makeWire "br_cond" .bit
  emitAssign brCond
    (Expr.mux (.ref br_f3_7) (.op .not [.ref bltu])
    (Expr.mux (.ref br_f3_6) (.ref bltu)
    (Expr.mux (.ref br_f3_5) (.op .not [.ref blt])
    (Expr.mux (.ref br_f3_4) (.ref blt)
    (Expr.mux (.ref br_f3_1) (.op .not [.ref beq])
    (Expr.mux (.ref br_f3_0) (.ref beq)
      (.const 0 1)))))))

  let branchTaken ← makeWire "branch_taken" .bit
  emitAssign branchTaken (.op .and [.ref idex.branch, .ref brCond])

  -- Branch/Jump targets
  let brTarget ← makeWire "br_target" (.bitVector 32)
  emitAssign brTarget (Expr.add (.ref idex.pc) (.ref idex.imm))
  let jalrSum ← makeWire "jalr_sum" (.bitVector 32)
  emitAssign jalrSum (Expr.add (.ref ex_rs1) (.ref idex.imm))
  let jalrTarget ← makeWire "jalr_target" (.bitVector 32)
  emitAssign jalrTarget (.op .and [.ref jalrSum, .const 0xFFFFFFFE 32])
  let jumpTarget ← makeWire "jump_target" (.bitVector 32)
  emitAssign jumpTarget (Expr.mux (.ref idex.isJalr) (.ref jalrTarget) (.ref brTarget))

  -- Flush signal (includes branch, jump, trap, and MRET)
  emitAssign pw.flush (.op .or [.ref branchTaken,
    .op .or [.ref idex.jump,
    .op .or [.ref "trap_taken", .ref idex.isMret]]])

  -- Data memory interface
  emitAssign "dmem_addr" (.slice (.ref alu_result) (dmemAddrBits + 1) 2)
  emitAssign "dmem_wdata" (.ref ex_rs2)
  emitAssign "dmem_we" (.ref idex.memWrite)
  emitAssign "dmem_re" (.ref idex.memRead)

  -- EX/WB pipeline registers
  let exwb_alu ← emitRegister "exwb_alu" "clk" "rst" (.ref alu_result) 0 (.bitVector 32)
  let exwb_rd ← emitRegister "exwb_rd" "clk" "rst" (.ref idex.rd) 0 (.bitVector 5)
  let exwb_regW ← emitRegister "exwb_regW" "clk" "rst" (.ref idex.regWrite) 0 .bit
  let exwb_m2r ← emitRegister "exwb_m2r" "clk" "rst" (.ref idex.memToReg) 0 .bit
  let exwb_pc4 ← emitRegister "exwb_pc4" "clk" "rst" (.ref idex.pc4) 0 (.bitVector 32)
  let exwb_jump ← emitRegister "exwb_jump" "clk" "rst" (.ref idex.jump) 0 .bit
  let exwb_isCsr ← emitRegister "exwb_is_csr" "clk" "rst" (.ref idex.isCsr) 0 .bit
  let exwb_csrRdata ← emitRegister "exwb_csr_rdata" "clk" "rst" (.ref "csr_rdata") 0 (.bitVector 32)

  -- Store-to-Load forwarding (Memory RAW hazard):
  -- When a STORE writes to DMEM BRAM at cycle N, a LOAD from the same address
  -- at cycle N+1 gets stale data due to read-before-write BRAM behavior.
  -- We save the previous cycle's store address/data/enable and bypass the
  -- BRAM output when the addresses match.
  let prevStoreAddr ← emitRegister "prev_store_addr" "clk" "rst"
    (.ref alu_result) 0 (.bitVector 32)
  let prevStoreData ← emitRegister "prev_store_data" "clk" "rst"
    (.ref ex_rs2) 0 (.bitVector 32)
  let prevStoreEn ← emitRegister "prev_store_en" "clk" "rst"
    (.ref idex.memWrite) 0 .bit

  -- Detect store-to-load address match (word-aligned comparison)
  let storeLoadMatch ← makeWire "store_load_match" .bit
  emitAssign storeLoadMatch (.op .and [.ref prevStoreEn,
    .op .eq [.slice (.ref prevStoreAddr) 31 2,
             .slice (.ref exwb_alu) 31 2]])

  -- Forwarded DMEM read data: bypass BRAM output when store-to-load match
  let dmemRdataFwd ← makeWire "dmem_rdata_fwd" (.bitVector 32)
  emitAssign dmemRdataFwd (Expr.mux (.ref storeLoadMatch)
    (.ref prevStoreData) (.ref "dmem_rdata"))

  -- WB stage: result mux (uses forwarded dmem_rdata)
  let wb_result ← makeWire "wb_result" (.bitVector 32)
  emitAssign wb_result
    (Expr.mux (.ref exwb_isCsr) (.ref exwb_csrRdata)
    (Expr.mux (.ref exwb_jump) (.ref exwb_pc4)
    (Expr.mux (.ref exwb_m2r) (.ref dmemRdataFwd)
      (.ref exwb_alu))))

  -- Write-back forwarding (wires pre-created in PipelineWires)
  emitAssign pw.wrAddrFwd (.ref exwb_rd)
  emitAssign pw.wrDataFwd (.ref wb_result)
  let wbRdNz ← makeWire "wb_rd_nz" .bit
  emitAssign wbRdNz (.op .not [.op .eq [.ref exwb_rd, .const 0 5]])
  emitAssign pw.wrEnFwd (.op .and [.ref exwb_regW, .ref wbRdNz])

  -- PC update (priority: trap > MRET > branch/jump > stall > normal)
  emitAssign pw.pcNext
    (Expr.mux (.ref "trap_taken") (.ref "trap_target")
    (Expr.mux (.ref idex.isMret) (.ref "mret_target")
    (Expr.mux (.ref pw.flush) (.ref jumpTarget)
    (Expr.mux (.ref pw.stall) (.ref pw.pcReg)
      (.ref pw.pcPlus4)))))

/-- Generate the complete 4-stage RV32I pipeline core. -/
def generateCore : CircuitM Unit := do
  -- Ports
  addInput "clk" .bit
  addInput "rst" .bit
  addOutput "imem_addr" (.bitVector imemAddrBits)
  addInput "imem_rdata" (.bitVector 32)
  addOutput "dmem_addr" (.bitVector dmemAddrBits)
  addOutput "dmem_wdata" (.bitVector 32)
  addOutput "dmem_we" .bit
  addOutput "dmem_re" .bit
  addInput "dmem_rdata" (.bitVector 32)
  addOutput "debug_pc" (.bitVector 32)
  addOutput "bus_addr" (.bitVector 32)  -- Full 32-bit address for bus routing

  -- CSR interface (directly connected by SoC)
  addOutput "csr_addr" (.bitVector 12)
  addOutput "csr_funct3" (.bitVector 3)
  addOutput "csr_wdata" (.bitVector 32)
  addOutput "csr_we" .bit
  addInput "csr_rdata" (.bitVector 32)

  -- Trap outputs
  addOutput "trap_ecall" .bit
  addOutput "trap_ebreak" .bit
  addOutput "trap_mret" .bit
  addOutput "trap_pc" (.bitVector 32)

  -- Trap input (redirect PC)
  addInput "trap_taken" .bit
  addInput "trap_target" (.bitVector 32)
  addInput "mret_target" (.bitVector 32)

  -- Shared pipeline wires
  let pcNext ← makeWire "pc_next" (.bitVector 32)
  let pcReg ← emitRegister "pc" "clk" "rst" (.ref pcNext) 0 (.bitVector 32)
  let pcPlus4 ← makeWire "pc_plus4" (.bitVector 32)
  let flush ← makeWire "flush" .bit
  let stall ← makeWire "stall" .bit

  -- Pre-create write-back forwarding wires (needed by register file BRAM
  -- which is emitted in ID stage, before WB stage assigns them)
  let wrAddrFwd ← makeWire "wr_addr_fwd" (.bitVector 5)
  let wrDataFwd ← makeWire "wr_data_fwd" (.bitVector 32)
  let wrEnFwd ← makeWire "wr_en_fwd" .bit

  -- Delayed flush: the 2-cycle IF delay means a branch/jump creates TWO
  -- wrong-path instructions in the fetch pipeline. The flush signal only
  -- squashes the first one (at posedge N+1). The second wrong-path
  -- instruction arrives from the stale BRAM output at posedge N+2 and
  -- sneaks through IFID. flushDelay extends the flush by one cycle so
  -- both wrong-path instructions are squashed.
  let flushDelay ← emitRegister "flush_delay" "clk" "rst" (.ref flush) 0 .bit

  -- Delayed PC: captures the current PC value each cycle.
  -- The IMEM BRAM reads at address pc[11:2] and produces the result one
  -- cycle later. fetchPC holds the PC that was used for the IMEM read,
  -- so ifid_pc (which captures fetchPC) aligns with the IMEM BRAM output.
  -- CRITICAL: fetchPC must HOLD during stall. Otherwise, during a load-use
  -- stall, fetchPC advances to pcReg (which is 2 ahead of IFID), and when
  -- the stall clears, IFID gets the instruction at the advanced fetchPC,
  -- skipping the instruction immediately after the stalled one.
  let fetchPCIn ← makeWire "fetch_pc_in" (.bitVector 32)
  let fetchPC ← emitRegister "fetch_pc" "clk" "rst" (.ref fetchPCIn) 0 (.bitVector 32)
  emitAssign fetchPCIn (Expr.mux (.ref stall) (.ref fetchPC) (.ref pcReg))
  let fetchPCPlus4 ← makeWire "fetch_pc_plus4" (.bitVector 32)
  emitAssign fetchPCPlus4 (Expr.add (.ref fetchPC) (.const 4 32))

  -- Previous-cycle WB forwarding: the regfile BRAM pre-read (from imem_rdata)
  -- happens 1 cycle before the instruction enters IFID. If WB writes to the
  -- same register at the same posedge, the BRAM gets the stale value (read-
  -- before-write). The current WB→ID bypass only checks the WB at the IFID
  -- cycle, missing the write from the previous cycle. These registers capture
  -- the previous cycle's WB data to enable a second-level bypass.
  let prevWrAddr ← emitRegister "prev_wr_addr" "clk" "rst" (.ref wrAddrFwd) 0 (.bitVector 5)
  let prevWrData ← emitRegister "prev_wr_data" "clk" "rst" (.ref wrDataFwd) 0 (.bitVector 32)
  let prevWrEn ← emitRegister "prev_wr_en" "clk" "rst" (.ref wrEnFwd) 0 .bit

  let pw : PipelineWires := {
    pcReg, pcPlus4, pcNext, flush, stall, wrAddrFwd, wrDataFwd, wrEnFwd,
    fetchPC, fetchPCPlus4, prevWrAddr, prevWrData, prevWrEn, flushDelay
  }

  -- Stage 1: IF
  generateIF pw

  -- IF/ID pipeline registers
  let ifid ← generateIFID pw

  -- Stage 2: ID (decode + register file)
  let idSig ← generateID_FieldsAndImm pw ifid

  -- Hazard detection
  -- Use the idex pipeline reg outputs for hazard detection.
  -- We need to create the IDEX first and use the outputs.
  -- But there's a circular dependency: stall depends on IDEX outputs, IDEX depends on stall.
  -- Solution: use the ID_Signals to create IDEX, and wire hazard from IDEX mem_read/rd.
  let idex ← generateIDEX pw idSig ifid

  -- Wire hazard detection from IDEX pipeline register outputs
  generateHazardDetection pw idSig idex.memRead idex.rd

  -- Stage 3: EX/MEM + Stage 4: WB
  generateEXMEM pw idex

/-- Build the complete RV32I pipeline core -/
def buildCore : Module :=
  CircuitM.runModule "RV32I_Core" do
    generateCore

end Sparkle.Examples.RV32.Core
