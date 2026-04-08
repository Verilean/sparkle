/-
  RV32I 4-Stage Pipeline — Signal DSL

  Uses Signal.loop with tuple state for feedback.
  All 44 pipeline registers are bundled into a right-nested pair.
  projN! and bundleAll! macros handle tuple projection/construction.

  Register index map (0-43):
    0  pcReg          : BitVec 32    1  fetchPC        : BitVec 32
    2  flushDelay     : Bool         3  ifid_inst      : BitVec 32
    4  ifid_pc        : BitVec 32    5  ifid_pc4       : BitVec 32
    6  idex_aluOp     : BitVec 4     7  idex_regWrite  : Bool
    8  idex_memRead   : Bool         9  idex_memWrite  : Bool
    10 idex_memToReg  : Bool         11 idex_branch    : Bool
    12 idex_jump      : Bool         13 idex_auipc     : Bool
    14 idex_aluSrcB   : Bool         15 idex_isJalr    : Bool
    16 idex_isCsr     : Bool         17 idex_isEcall   : Bool
    18 idex_isMret    : Bool         19 idex_rs1Val    : BitVec 32
    20 idex_rs2Val    : BitVec 32    21 idex_imm       : BitVec 32
    22 idex_rd        : BitVec 5     23 idex_rs1Idx    : BitVec 5
    24 idex_rs2Idx    : BitVec 5     25 idex_funct3    : BitVec 3
    26 idex_pc        : BitVec 32    27 idex_pc4       : BitVec 32
    28 idex_csrAddr   : BitVec 12    29 idex_csrFunct3 : BitVec 3
    30 exwb_alu       : BitVec 32    31 exwb_rd        : BitVec 5
    32 exwb_regW      : Bool         33 exwb_m2r       : Bool
    34 exwb_pc4       : BitVec 32    35 exwb_jump      : Bool
    36 exwb_isCsr     : Bool         37 exwb_csrRdata  : BitVec 32
    38 prev_wb_addr   : BitVec 5     39 prev_wb_data   : BitVec 32
    40 prev_wb_en     : Bool         41 prevStoreAddr  : BitVec 32
    42 prevStoreData  : BitVec 32    43 prevStoreEn    : Bool
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

namespace Sparkle.IP.RV32

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- NOP instruction = ADDI x0, x0, 0
def nopInst : BitVec 32 := 0x00000013#32

-- Number of pipeline registers
def numPipelineRegs : Nat := 44

/-- RV32I 4-stage pipeline core (Signal DSL).

    Uses Signal.loop with a 44-register tuple state.
    Output: debug_pc (first element of the tuple). -/
def rv32iCore {dom : DomainConfig}
    (imem_rdata : Signal dom (BitVec 32))
    (dmem_rdata : Signal dom (BitVec 32))
    (csr_rdata : Signal dom (BitVec 32))
    (trap_taken : Signal dom Bool)
    (trap_target : Signal dom (BitVec 32))
    (mret_target : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=  -- debug_pc
  let pipeline := Signal.loop fun state =>
    -- =================================================================
    -- Unbundle: extract all 44 register outputs from loop state
    -- =================================================================
    let pcReg         := projN! state 44 0
    let fetchPC       := projN! state 44 1
    let flushDelay    := projN! state 44 2
    let ifid_inst     := projN! state 44 3
    let ifid_pc       := projN! state 44 4
    let ifid_pc4      := projN! state 44 5
    let idex_aluOp    := projN! state 44 6
    let idex_regWrite := projN! state 44 7
    let idex_memRead  := projN! state 44 8
    let idex_memWrite := projN! state 44 9
    let idex_memToReg := projN! state 44 10
    let idex_branch   := projN! state 44 11
    let idex_jump     := projN! state 44 12
    let idex_auipc    := projN! state 44 13
    let idex_aluSrcB  := projN! state 44 14
    let idex_isJalr   := projN! state 44 15
    let idex_isCsr    := projN! state 44 16
    let idex_isEcall  := projN! state 44 17
    let idex_isMret   := projN! state 44 18
    let idex_rs1Val   := projN! state 44 19
    let idex_rs2Val   := projN! state 44 20
    let idex_imm      := projN! state 44 21
    let idex_rd       := projN! state 44 22
    let idex_rs1Idx   := projN! state 44 23
    let idex_rs2Idx   := projN! state 44 24
    let idex_funct3   := projN! state 44 25
    let idex_pc       := projN! state 44 26
    let idex_pc4      := projN! state 44 27
    let idex_csrAddr  := projN! state 44 28
    let idex_csrFunct3 := projN! state 44 29
    let exwb_alu      := projN! state 44 30
    let exwb_rd       := projN! state 44 31
    let exwb_regW     := projN! state 44 32
    let exwb_m2r      := projN! state 44 33
    let exwb_pc4      := projN! state 44 34
    let exwb_jump     := projN! state 44 35
    let exwb_isCsr    := projN! state 44 36
    let exwb_csrRdata := projN! state 44 37
    let prev_wb_addr  := projN! state 44 38
    let prev_wb_data  := projN! state 44 39
    let prev_wb_en    := projN! state 44 40
    let prevStoreAddr := projN! state 44 41
    let prevStoreData := projN! state 44 42
    let prevStoreEn   := projN! state 44 43

    -- =================================================================
    -- WB Stage (compute first — needed for forwarding/bypass)
    -- =================================================================
    -- Store-to-load forwarding (split compound lambda)
    let storeAddrHi := prevStoreAddr.map (BitVec.extractLsb' 2 30 ·)
    let loadAddrHi := exwb_alu.map (BitVec.extractLsb' 2 30 ·)
    let addrMatch := storeAddrHi === loadAddrHi
    let storeLoadMatch := prevStoreEn &&& addrMatch
    let dmemRdataFwd := Signal.mux storeLoadMatch prevStoreData dmem_rdata

    let wb_result := Signal.mux exwb_isCsr exwb_csrRdata
                       (Signal.mux exwb_jump exwb_pc4
                       (Signal.mux exwb_m2r dmemRdataFwd
                         exwb_alu))
    let wbRdNz_check := exwb_rd === 0#5
    let wbRdNz := ~~~wbRdNz_check
    let wb_addr := exwb_rd
    let wb_data := wb_result
    let wb_en   := exwb_regW &&& wbRdNz

    -- =================================================================
    -- EX Stage
    -- =================================================================
    -- WB→EX forwarding
    let fwd_rs1_match := wb_en &&& (wb_addr === idex_rs1Idx)
    let fwd_rs2_match := wb_en &&& (wb_addr === idex_rs2Idx)
    let ex_rs1 := Signal.mux fwd_rs1_match wb_data idex_rs1Val
    let ex_rs2 := Signal.mux fwd_rs2_match wb_data idex_rs2Val
    -- ALU
    let alu_a := Signal.mux idex_auipc idex_pc ex_rs1
    let alu_b := Signal.mux idex_aluSrcB idex_imm ex_rs2
    let alu_result := aluSignal idex_aluOp alu_a alu_b
    -- Branch
    let branchCond := branchCompSignal idex_funct3 ex_rs1 ex_rs2
    let branchTaken := idex_branch &&& branchCond
    -- Branch/jump target
    let brTarget := idex_pc + idex_imm
    let jalrSum  := ex_rs1 + idex_imm
    let jalrTarget := jalrSum &&& 0xFFFFFFFE#32
    let jumpTarget := Signal.mux idex_isJalr jalrTarget brTarget
    -- Flush
    let flush := (branchTaken ||| idex_jump) ||| (trap_taken ||| idex_isMret)
    let flushOrDelay := flush ||| flushDelay

    -- =================================================================
    -- Hazard / Stall (depends on idex outputs and ID decode)
    -- =================================================================
    -- ID decode (from ifid_inst)
    let id_opcode := ifid_inst.map (BitVec.extractLsb' 0 7 ·)
    let id_rd     := ifid_inst.map (BitVec.extractLsb' 7 5 ·)
    let id_funct3 := ifid_inst.map (BitVec.extractLsb' 12 3 ·)
    let id_rs1    := ifid_inst.map (BitVec.extractLsb' 15 5 ·)
    let id_rs2    := ifid_inst.map (BitVec.extractLsb' 20 5 ·)
    let id_funct7 := ifid_inst.map (BitVec.extractLsb' 25 7 ·)
    let id_imm := immGenSignal ifid_inst id_opcode
    let id_aluOp := aluControlSignal id_opcode id_funct3 id_funct7
    -- Control signals
    let id_isALUrr  := id_opcode === 0b0110011#7
    let id_isALUimm := id_opcode === 0b0010011#7
    let id_isLoad   := id_opcode === 0b0000011#7
    let id_isStore  := id_opcode === 0b0100011#7
    let id_isBranch := id_opcode === 0b1100011#7
    let id_isLUI    := id_opcode === 0b0110111#7
    let id_isAUIPC  := id_opcode === 0b0010111#7
    let id_isJAL    := id_opcode === 0b1101111#7
    let id_isJALR   := id_opcode === 0b1100111#7
    let id_isSystem := id_opcode === 0b1110011#7
    -- Derived
    let id_aluSrcB := ((id_isALUimm ||| id_isLoad) ||| (id_isStore ||| id_isLUI)) |||
                      ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let id_regWrite := ((id_isALUrr ||| id_isALUimm) ||| (id_isLoad ||| id_isLUI)) |||
                       ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let id_memRead  := id_isLoad
    let id_memWrite := id_isStore
    let id_memToReg := id_isLoad
    let id_jump     := id_isJAL ||| id_isJALR
    let id_auipc    := id_isAUIPC ||| id_isJAL
    let f3isZero := id_funct3 === 0#3
    let f3notZero := ~~~f3isZero
    let id_isCsr := id_isSystem &&& f3notZero
    let id_isEcall := id_isSystem &&& f3isZero
    let id_csrAddr := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let mretField := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let isMretField := mretField === 0x302#12
    let id_isMret := id_isSystem &&& isMretField

    -- Stall
    let stall := hazardSignal idex_memRead idex_rd id_rs1 id_rs2

    -- =================================================================
    -- Register File (dual-read, single-write via Signal.memory)
    -- =================================================================
    let rf_rs1_addr := Signal.mux stall id_rs1
                         (imem_rdata.map (BitVec.extractLsb' 15 5 ·))
    let rf_rs2_addr := Signal.mux stall id_rs2
                         (imem_rdata.map (BitVec.extractLsb' 20 5 ·))
    let rf_rs1_raw := Signal.memory wb_addr wb_data wb_en rf_rs1_addr
    let rf_rs2_raw := Signal.memory wb_addr wb_data wb_en rf_rs2_addr
    -- WB→ID bypass
    let wb_fwd_rs1 := wb_en &&& (wb_addr === id_rs1)
    let wb_fwd_rs2 := wb_en &&& (wb_addr === id_rs2)
    -- Previous-cycle WB bypass
    let prev_fwd_rs1 := prev_wb_en &&& (prev_wb_addr === id_rs1)
    let prev_fwd_rs2 := prev_wb_en &&& (prev_wb_addr === id_rs2)
    let rf_rs1_bypassed := Signal.mux wb_fwd_rs1 wb_data
                             (Signal.mux prev_fwd_rs1 prev_wb_data rf_rs1_raw)
    let rf_rs2_bypassed := Signal.mux wb_fwd_rs2 wb_data
                             (Signal.mux prev_fwd_rs2 prev_wb_data rf_rs2_raw)
    -- x0 hardwiring
    let id_rs1Val := Signal.mux (id_rs1 === 0#5)
                       (Signal.pure 0#32) rf_rs1_bypassed
    let id_rs2Val := Signal.mux (id_rs2 === 0#5)
                       (Signal.pure 0#32) rf_rs2_bypassed

    -- =================================================================
    -- IF Stage: PC + fetch
    -- =================================================================
    let pcPlus4 := pcReg + 4#32
    let fetchPCIn := Signal.mux stall fetchPC pcReg
    let fetchPCPlus4 := fetchPC + 4#32

    -- =================================================================
    -- IF/ID register inputs
    -- =================================================================
    let ifid_inst_in := Signal.mux flushOrDelay (Signal.pure nopInst)
                          (Signal.mux stall ifid_inst imem_rdata)
    let ifid_pc_in := Signal.mux stall ifid_pc fetchPC
    let ifid_pc4_in := Signal.mux stall ifid_pc4 fetchPCPlus4

    -- =================================================================
    -- ID/EX register inputs (squash on stall or flush)
    -- =================================================================
    let squash := stall ||| flushOrDelay
    -- CSR interface
    let csrIsImm_bit := idex_csrFunct3.map (BitVec.extractLsb' 2 1 ·)
    let csrIsImm := csrIsImm_bit === 1#1
    let csrZimm  := 0#27 ++ idex_rs1Idx

    -- =================================================================
    -- PC Next
    -- =================================================================
    let pcNext := Signal.mux trap_taken trap_target
                    (Signal.mux idex_isMret mret_target
                    (Signal.mux flush jumpTarget
                    (Signal.mux stall pcReg
                      pcPlus4)))

    -- =================================================================
    -- Create all 44 registers and rebundle
    -- =================================================================
    bundleAll! [
      Signal.register 0#32 pcNext,                                              -- 0  pcReg
      Signal.register 0#32 fetchPCIn,                                           -- 1  fetchPC
      Signal.register false flush,                                              -- 2  flushDelay
      Signal.register 0x00000013#32 ifid_inst_in,                               -- 3  ifid_inst
      Signal.register 0#32 ifid_pc_in,                                          -- 4  ifid_pc
      Signal.register 0#32 ifid_pc4_in,                                         -- 5  ifid_pc4
      Signal.register 0#4 (Signal.mux squash (Signal.pure 0#4) id_aluOp),      -- 6  idex_aluOp
      Signal.register false (Signal.mux squash (Signal.pure false) id_regWrite), -- 7  idex_regWrite
      Signal.register false (Signal.mux squash (Signal.pure false) id_memRead), -- 8  idex_memRead
      Signal.register false (Signal.mux squash (Signal.pure false) id_memWrite), -- 9  idex_memWrite
      Signal.register false (Signal.mux squash (Signal.pure false) id_memToReg), -- 10 idex_memToReg
      Signal.register false (Signal.mux squash (Signal.pure false) id_isBranch), -- 11 idex_branch
      Signal.register false (Signal.mux squash (Signal.pure false) id_jump),    -- 12 idex_jump
      Signal.register false (Signal.mux squash (Signal.pure false) id_auipc),   -- 13 idex_auipc
      Signal.register false (Signal.mux squash (Signal.pure false) id_aluSrcB), -- 14 idex_aluSrcB
      Signal.register false (Signal.mux squash (Signal.pure false) id_isJALR),  -- 15 idex_isJalr
      Signal.register false (Signal.mux squash (Signal.pure false) id_isCsr),   -- 16 idex_isCsr
      Signal.register false (Signal.mux squash (Signal.pure false) id_isEcall), -- 17 idex_isEcall
      Signal.register false (Signal.mux squash (Signal.pure false) id_isMret),  -- 18 idex_isMret
      Signal.register 0#32 id_rs1Val,                                           -- 19 idex_rs1Val
      Signal.register 0#32 id_rs2Val,                                           -- 20 idex_rs2Val
      Signal.register 0#32 id_imm,                                              -- 21 idex_imm
      Signal.register 0#5 (Signal.mux squash (Signal.pure 0#5) id_rd),         -- 22 idex_rd
      Signal.register 0#5 id_rs1,                                               -- 23 idex_rs1Idx
      Signal.register 0#5 id_rs2,                                               -- 24 idex_rs2Idx
      Signal.register 0#3 id_funct3,                                            -- 25 idex_funct3
      Signal.register 0#32 ifid_pc,                                             -- 26 idex_pc
      Signal.register 0#32 ifid_pc4,                                            -- 27 idex_pc4
      Signal.register 0#12 id_csrAddr,                                          -- 28 idex_csrAddr
      Signal.register 0#3 id_funct3,                                            -- 29 idex_csrFunct3
      Signal.register 0#32 alu_result,                                          -- 30 exwb_alu
      Signal.register 0#5 idex_rd,                                              -- 31 exwb_rd
      Signal.register false idex_regWrite,                                      -- 32 exwb_regW
      Signal.register false idex_memToReg,                                      -- 33 exwb_m2r
      Signal.register 0#32 idex_pc4,                                            -- 34 exwb_pc4
      Signal.register false idex_jump,                                          -- 35 exwb_jump
      Signal.register false idex_isCsr,                                         -- 36 exwb_isCsr
      Signal.register 0#32 csr_rdata,                                           -- 37 exwb_csrRdata
      Signal.register 0#5 wb_addr,                                              -- 38 prev_wb_addr
      Signal.register 0#32 wb_data,                                             -- 39 prev_wb_data
      Signal.register false wb_en,                                              -- 40 prev_wb_en
      Signal.register 0#32 alu_result,                                          -- 41 prevStoreAddr
      Signal.register 0#32 ex_rs2,                                              -- 42 prevStoreData
      Signal.register false idex_memWrite                                       -- 43 prevStoreEn
    ]
  -- Output: debug_pc = pcReg (first element)
  Signal.fst pipeline

-- Test synthesis of the pipeline core
#synthesizeVerilog rv32iCore

end Sparkle.IP.RV32
