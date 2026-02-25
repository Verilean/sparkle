/-
  RV32I SoC — Signal DSL (flat design)

  All state (pipeline + CLINT + CSR) in a single Signal.loop.
  56 registers total in a right-nested pair.

  Register index map (0-55):
  Pipeline (0-43): same as Pipeline.lean
  CLINT (44-48): msip, mtimeLo, mtimeHi, mtimecmpLo, mtimecmpHi
  CSR (49-55): mstatus, mie, mtvec, mscratch, mepc, mcause, mtval

  Architecture note:
    The DMEM read address uses an "approximate" ALU result that omits
    load-result forwarding (WB→EX when exwb_m2r=true). This is safe
    because load-use hazards are stalled, so the only cycle where the
    approximation differs is the stall-bubble cycle, whose BRAM read
    result is never consumed.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.Core
import Examples.RV32.CSR.Types

set_option maxRecDepth 32768
set_option maxHeartbeats 3200000

namespace Sparkle.Examples.RV32.SoC

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32
open Sparkle.Examples.RV32
open Sparkle.Examples.RV32.CSR

def nopInst : BitVec 32 := 0x00000013#32

-- rv32iSoC (synthesis-only, phantom-type-safe version) is in SoCVerilog.lean
-- to prevent module-init stack overflow from closed-term evaluation.

/-- State type for the 56-register SoC loop (right-nested tuple). -/
private abbrev SoCState :=
  BitVec 32 × BitVec 32 × Bool × BitVec 32 × BitVec 32 × BitVec 32 ×
  BitVec 4 × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool ×
  Bool × Bool × Bool × Bool × BitVec 32 × BitVec 32 × BitVec 32 ×
  BitVec 5 × BitVec 5 × BitVec 5 × BitVec 3 × BitVec 32 × BitVec 32 ×
  BitVec 12 × BitVec 3 × BitVec 32 × BitVec 5 × Bool × Bool ×
  BitVec 32 × Bool × Bool × BitVec 32 × BitVec 5 × BitVec 32 × Bool ×
  BitVec 32 × BitVec 32 × Bool × BitVec 32 × BitVec 32 × BitVec 32 ×
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- Loop body for RV32I SoC with pre-loaded firmware.
    Extracted so it can be shared between `rv32iSoCWithFirmware` (synthesis)
    and `rv32iSoCSimulate` (memoized simulation). -/
private def rv32iSoCWithFirmwareBody {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    (state : Signal dom SoCState) : Signal dom SoCState :=
    -- Extract all 56 register outputs (same layout as rv32iSoC)
    let pcReg          := projN! state 56 0
    let fetchPC        := projN! state 56 1
    let flushDelay     := projN! state 56 2
    let ifid_inst      := projN! state 56 3
    let ifid_pc        := projN! state 56 4
    let ifid_pc4       := projN! state 56 5
    let idex_aluOp     := projN! state 56 6
    let idex_regWrite  := projN! state 56 7
    let idex_memRead   := projN! state 56 8
    let idex_memWrite  := projN! state 56 9
    let idex_memToReg  := projN! state 56 10
    let idex_branch    := projN! state 56 11
    let idex_jump      := projN! state 56 12
    let idex_auipc     := projN! state 56 13
    let idex_aluSrcB   := projN! state 56 14
    let idex_isJalr    := projN! state 56 15
    let idex_isCsr     := projN! state 56 16
    let idex_isEcall   := projN! state 56 17
    let idex_isMret    := projN! state 56 18
    let idex_rs1Val    := projN! state 56 19
    let idex_rs2Val    := projN! state 56 20
    let idex_imm       := projN! state 56 21
    let idex_rd        := projN! state 56 22
    let idex_rs1Idx    := projN! state 56 23
    let idex_rs2Idx    := projN! state 56 24
    let idex_funct3    := projN! state 56 25
    let idex_pc        := projN! state 56 26
    let idex_pc4       := projN! state 56 27
    let idex_csrAddr   := projN! state 56 28
    let idex_csrFunct3 := projN! state 56 29
    let exwb_alu       := projN! state 56 30
    let exwb_rd        := projN! state 56 31
    let exwb_regW      := projN! state 56 32
    let exwb_m2r       := projN! state 56 33
    let exwb_pc4       := projN! state 56 34
    let exwb_jump      := projN! state 56 35
    let exwb_isCsr     := projN! state 56 36
    let exwb_csrRdata  := projN! state 56 37
    let prev_wb_addr   := projN! state 56 38
    let prev_wb_data   := projN! state 56 39
    let prev_wb_en     := projN! state 56 40
    let prevStoreAddr  := projN! state 56 41
    let prevStoreData  := projN! state 56 42
    let prevStoreEn    := projN! state 56 43
    let msipReg        := projN! state 56 44
    let mtimeLoReg     := projN! state 56 45
    let mtimeHiReg     := projN! state 56 46
    let mtimecmpLoReg  := projN! state 56 47
    let mtimecmpHiReg  := projN! state 56 48
    let mstatusReg     := projN! state 56 49
    let mieReg         := projN! state 56 50
    let mtvecReg       := projN! state 56 51
    let mscratchReg    := projN! state 56 52
    let mepcReg        := projN! state 56 53
    let mcauseReg      := projN! state 56 54
    let mtvalReg       := projN! state 56 55

    -- Phase 1-5: identical to rv32iSoC except IMEM uses memoryWithInit
    let wbRdNz := (fun x => !x) <$> ((· == ·) <$> exwb_rd <*> Signal.pure 0#5)
    let wb_addr := exwb_rd
    let wb_en   := (· && ·) <$> exwb_regW <*> wbRdNz
    let wb_data_non_mem := Signal.mux exwb_isCsr exwb_csrRdata
                             (Signal.mux exwb_jump exwb_pc4 exwb_alu)
    let fwd_rs1_match := (· && ·) <$> wb_en <*> ((· == ·) <$> wb_addr <*> idex_rs1Idx)
    let fwd_rs2_match := (· && ·) <$> wb_en <*> ((· == ·) <$> wb_addr <*> idex_rs2Idx)

    let fwd_val_approx := Signal.mux exwb_m2r idex_rs1Val wb_data_non_mem
    let ex_rs1_approx := Signal.mux fwd_rs1_match fwd_val_approx idex_rs1Val
    let fwd_val2_approx := Signal.mux exwb_m2r idex_rs2Val wb_data_non_mem
    let ex_rs2_approx := Signal.mux fwd_rs2_match fwd_val2_approx idex_rs2Val
    let alu_a_approx := Signal.mux idex_auipc idex_pc ex_rs1_approx
    let alu_b_approx := Signal.mux idex_aluSrcB idex_imm ex_rs2_approx
    let alu_result_approx := aluSignal idex_aluOp alu_a_approx alu_b_approx

    -- IMEM with pre-loaded firmware (combinational read)
    -- Must be combinational (not synchronous memory) so that imem_rdata.val t
    -- = firmware[fetchPC.val t], aligning with ifid_pc_in = fetchPC.val t.
    -- Synchronous memory reads from readAddr.val (t-1), which would make
    -- ifid_inst lag ifid_pc by 1 cycle, causing branch targets to be PC+4+offset.
    let imem_addr := fetchPC.map (BitVec.extractLsb' 2 12 ·)
    let imem_rdata := imem_addr.map firmware

    let busAddrHi_ex := alu_result_approx.map (BitVec.extractLsb' 16 16 ·)
    let isCLINT_ex := (· == ·) <$> busAddrHi_ex <*> Signal.pure 0x0200#16
    let isDMEM_ex := (fun x => !x) <$> isCLINT_ex

    let dmem_write_addr := alu_result_approx.map (BitVec.extractLsb' 2 14 ·)
    let dmem_read_addr  := alu_result_approx.map (BitVec.extractLsb' 2 14 ·)
    let dmem_we := (· && ·) <$> idex_memWrite <*> isDMEM_ex
    let dmem_rdata := Signal.memory dmem_write_addr ex_rs2_approx dmem_we
                        dmem_read_addr

    let storeAddrHi := prevStoreAddr.map (BitVec.extractLsb' 2 30 ·)
    let loadAddrHi := exwb_alu.map (BitVec.extractLsb' 2 30 ·)
    let addrMatch := (· == ·) <$> storeAddrHi <*> loadAddrHi
    let storeLoadMatch := (· && ·) <$> prevStoreEn <*> addrMatch
    let dmemRdataFwd := Signal.mux storeLoadMatch prevStoreData dmem_rdata
    let clintOffset_wb := exwb_alu.map (BitVec.extractLsb' 0 16 ·)
    let msipMatch_wb     := (· == ·) <$> clintOffset_wb <*> Signal.pure 0x0000#16
    let mtimeLoMatch_wb  := (· == ·) <$> clintOffset_wb <*> Signal.pure 0xBFF8#16
    let mtimeHiMatch_wb  := (· == ·) <$> clintOffset_wb <*> Signal.pure 0xBFFC#16
    let mtimecmpLoMatch_wb := (· == ·) <$> clintOffset_wb <*> Signal.pure 0x4000#16
    let mtimecmpHiMatch_wb := (· == ·) <$> clintOffset_wb <*> Signal.pure 0x4004#16
    let clintRdata :=
      Signal.mux msipMatch_wb msipReg
      (Signal.mux mtimecmpLoMatch_wb mtimecmpLoReg
      (Signal.mux mtimecmpHiMatch_wb mtimecmpHiReg
      (Signal.mux mtimeLoMatch_wb mtimeLoReg
      (Signal.mux mtimeHiMatch_wb mtimeHiReg
        (Signal.pure 0#32)))))
    let busAddrHi_wb := exwb_alu.map (BitVec.extractLsb' 16 16 ·)
    let isCLINT_wb := (· == ·) <$> busAddrHi_wb <*> Signal.pure 0x0200#16
    let busRdata := Signal.mux isCLINT_wb clintRdata dmemRdataFwd
    let wb_result := Signal.mux exwb_isCsr exwb_csrRdata
                       (Signal.mux exwb_jump exwb_pc4
                       (Signal.mux exwb_m2r busRdata
                         exwb_alu))
    let wb_data := wb_result

    let ex_rs1 := Signal.mux fwd_rs1_match wb_data idex_rs1Val
    let ex_rs2 := Signal.mux fwd_rs2_match wb_data idex_rs2Val
    let alu_a := Signal.mux idex_auipc idex_pc ex_rs1
    let alu_b := Signal.mux idex_aluSrcB idex_imm ex_rs2
    let alu_result := aluSignal idex_aluOp alu_a alu_b
    let branchCond := branchCompSignal idex_funct3 ex_rs1 ex_rs2
    let branchTaken := (· && ·) <$> idex_branch <*> branchCond
    let brTarget := (· + ·) <$> idex_pc <*> idex_imm
    let jalrSum  := (· + ·) <$> ex_rs1 <*> idex_imm
    let jalrTarget := (· &&& ·) <$> jalrSum <*> Signal.pure 0xFFFFFFFE#32
    let jumpTarget := Signal.mux idex_isJalr jalrTarget brTarget

    let hiGt := (BitVec.ult · ·) <$> mtimecmpHiReg <*> mtimeHiReg
    let hiEq := (· == ·) <$> mtimeHiReg <*> mtimecmpHiReg
    let loGe := (fun x => !x) <$> ((BitVec.ult · ·) <$> mtimeLoReg <*> mtimecmpLoReg)
    let timerIrq := (· || ·) <$> hiGt <*> ((· && ·) <$> hiEq <*> loGe)
    let swIrq := (· == ·) <$> (msipReg.map (BitVec.extractLsb' 0 1 ·)) <*> Signal.pure 1#1
    let mipTimerBit := Signal.mux timerIrq (Signal.pure 0x00000080#32) (Signal.pure 0#32)
    let mipSwBit := Signal.mux swIrq (Signal.pure 0x00000008#32) (Signal.pure 0#32)
    let mipValue := (· ||| ·) <$> mipTimerBit <*> mipSwBit
    let csrIsMstatus  := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x300#12
    let csrIsMie      := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x304#12
    let csrIsMtvec    := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x305#12
    let csrIsMscratch := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x340#12
    let csrIsMepc     := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x341#12
    let csrIsMcause   := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x342#12
    let csrIsMtval    := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x343#12
    let csrIsMip      := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x344#12
    let csrIsMisa     := (· == ·) <$> idex_csrAddr <*> Signal.pure 0x301#12
    let csrIsMhartid  := (· == ·) <$> idex_csrAddr <*> Signal.pure 0xF14#12
    let csr_rdata :=
      Signal.mux csrIsMstatus mstatusReg
      (Signal.mux csrIsMie mieReg
      (Signal.mux csrIsMtvec mtvecReg
      (Signal.mux csrIsMscratch mscratchReg
      (Signal.mux csrIsMepc mepcReg
      (Signal.mux csrIsMcause mcauseReg
      (Signal.mux csrIsMtval mtvalReg
      (Signal.mux csrIsMip mipValue
      (Signal.mux csrIsMisa (Signal.pure 0x40000100#32)
      (Signal.mux csrIsMhartid (Signal.pure 0#32)
        (Signal.pure 0#32))))))))))

    let mstatusMIE_flag := (· == ·) <$> (mstatusReg.map (BitVec.extractLsb' 3 1 ·)) <*> Signal.pure 1#1
    let mstatusMPIE_flag := (· == ·) <$> (mstatusReg.map (BitVec.extractLsb' 7 1 ·)) <*> Signal.pure 1#1
    let mieMTIE_flag := (· == ·) <$> (mieReg.map (BitVec.extractLsb' 7 1 ·)) <*> Signal.pure 1#1
    let mieMSIE_flag := (· == ·) <$> (mieReg.map (BitVec.extractLsb' 3 1 ·)) <*> Signal.pure 1#1
    let timerIntEnabled := (· && ·) <$> mstatusMIE_flag <*> ((· && ·) <$> mieMTIE_flag <*> timerIrq)
    let swIntEnabled    := (· && ·) <$> mstatusMIE_flag <*> ((· && ·) <$> mieMSIE_flag <*> swIrq)
    let trap_taken := (· || ·) <$> idex_isEcall <*>
                        ((· || ·) <$> timerIntEnabled <*> swIntEnabled)
    let trapCause :=
      Signal.mux idex_isEcall (Signal.pure 0x0000000B#32)
      (Signal.mux timerIntEnabled (Signal.pure 0x80000007#32)
      (Signal.mux swIntEnabled (Signal.pure 0x80000003#32)
        (Signal.pure 0#32)))
    let trap_target := (· &&& ·) <$> mtvecReg <*> Signal.pure 0xFFFFFFFC#32
    let mret_target := mepcReg

    let flush := (· || ·) <$> ((· || ·) <$> branchTaken <*> idex_jump) <*>
                 ((· || ·) <$> trap_taken <*> idex_isMret)
    let flushOrDelay := (· || ·) <$> flush <*> flushDelay

    let id_opcode := ifid_inst.map (BitVec.extractLsb' 0 7 ·)
    let id_rd     := ifid_inst.map (BitVec.extractLsb' 7 5 ·)
    let id_funct3 := ifid_inst.map (BitVec.extractLsb' 12 3 ·)
    let id_rs1    := ifid_inst.map (BitVec.extractLsb' 15 5 ·)
    let id_rs2    := ifid_inst.map (BitVec.extractLsb' 20 5 ·)
    let id_funct7 := ifid_inst.map (BitVec.extractLsb' 25 7 ·)
    let id_imm := immGenSignal ifid_inst id_opcode
    let id_aluOp := aluControlSignal id_opcode id_funct3 id_funct7
    let id_isALUrr  := (· == ·) <$> id_opcode <*> Signal.pure 0b0110011#7
    let id_isALUimm := (· == ·) <$> id_opcode <*> Signal.pure 0b0010011#7
    let id_isLoad   := (· == ·) <$> id_opcode <*> Signal.pure 0b0000011#7
    let id_isStore  := (· == ·) <$> id_opcode <*> Signal.pure 0b0100011#7
    let id_isBranch := (· == ·) <$> id_opcode <*> Signal.pure 0b1100011#7
    let id_isLUI    := (· == ·) <$> id_opcode <*> Signal.pure 0b0110111#7
    let id_isAUIPC  := (· == ·) <$> id_opcode <*> Signal.pure 0b0010111#7
    let id_isJAL    := (· == ·) <$> id_opcode <*> Signal.pure 0b1101111#7
    let id_isJALR   := (· == ·) <$> id_opcode <*> Signal.pure 0b1100111#7
    let id_isSystem := (· == ·) <$> id_opcode <*> Signal.pure 0b1110011#7
    let id_aluSrcB := (· || ·) <$> ((· || ·) <$> ((· || ·) <$> id_isALUimm <*> id_isLoad) <*>
                      ((· || ·) <$> id_isStore <*> id_isLUI)) <*>
                      ((· || ·) <$> ((· || ·) <$> id_isAUIPC <*> id_isJAL) <*> id_isJALR)
    let id_regWrite := (· || ·) <$> ((· || ·) <$> ((· || ·) <$> id_isALUrr <*> id_isALUimm) <*>
                       ((· || ·) <$> id_isLoad <*> id_isLUI)) <*>
                       ((· || ·) <$> ((· || ·) <$> id_isAUIPC <*> id_isJAL) <*> id_isJALR)
    let id_memRead  := id_isLoad
    let id_memWrite := id_isStore
    let id_memToReg := id_isLoad
    let id_jump     := (· || ·) <$> id_isJAL <*> id_isJALR
    let id_auipc    := (· || ·) <$> id_isAUIPC <*> id_isJAL
    let f3isZero := (· == ·) <$> id_funct3 <*> Signal.pure 0#3
    let f3notZero := (fun x => !x) <$> f3isZero
    let id_isCsr := (· && ·) <$> id_isSystem <*> f3notZero
    let id_isEcall := (· && ·) <$> id_isSystem <*> f3isZero
    let id_csrAddr := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let mretField := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let isMretField := (· == ·) <$> mretField <*> Signal.pure 0x302#12
    let id_isMret := (· && ·) <$> id_isSystem <*> isMretField

    let stall := hazardSignal idex_memRead idex_rd id_rs1 id_rs2

    let rf_rs1_addr := Signal.mux stall id_rs1
                         (ifid_inst.map (BitVec.extractLsb' 15 5 ·))
    let rf_rs2_addr := Signal.mux stall id_rs2
                         (ifid_inst.map (BitVec.extractLsb' 20 5 ·))
    -- Register file uses combinational reads (same-cycle readAddr)
    -- so that rf_rs1_raw.val t reads the register addressed by rf_rs1_addr.val t,
    -- not rf_rs1_addr.val (t-1) as Signal.memory would.
    let rf_rs1_raw := Signal.memoryComboRead wb_addr wb_data wb_en rf_rs1_addr
    let rf_rs2_raw := Signal.memoryComboRead wb_addr wb_data wb_en rf_rs2_addr
    let wb_fwd_rs1 := (· && ·) <$> wb_en <*> ((· == ·) <$> wb_addr <*> id_rs1)
    let wb_fwd_rs2 := (· && ·) <$> wb_en <*> ((· == ·) <$> wb_addr <*> id_rs2)
    let prev_fwd_rs1 := (· && ·) <$> prev_wb_en <*> ((· == ·) <$> prev_wb_addr <*> id_rs1)
    let prev_fwd_rs2 := (· && ·) <$> prev_wb_en <*> ((· == ·) <$> prev_wb_addr <*> id_rs2)
    let rf_rs1_bypassed := Signal.mux wb_fwd_rs1 wb_data
                             (Signal.mux prev_fwd_rs1 prev_wb_data rf_rs1_raw)
    let rf_rs2_bypassed := Signal.mux wb_fwd_rs2 wb_data
                             (Signal.mux prev_fwd_rs2 prev_wb_data rf_rs2_raw)
    let id_rs1Val := Signal.mux ((· == ·) <$> id_rs1 <*> Signal.pure 0#5)
                       (Signal.pure 0#32) rf_rs1_bypassed
    let id_rs2Val := Signal.mux ((· == ·) <$> id_rs2 <*> Signal.pure 0#5)
                       (Signal.pure 0#32) rf_rs2_bypassed

    let pcPlus4 := (· + ·) <$> pcReg <*> Signal.pure 4#32
    let fetchPCIn := Signal.mux stall fetchPC pcReg
    let fetchPCPlus4 := (· + ·) <$> fetchPC <*> Signal.pure 4#32
    let ifid_inst_in := Signal.mux flushOrDelay (Signal.pure nopInst)
                          (Signal.mux stall ifid_inst imem_rdata)
    let ifid_pc_in := Signal.mux stall ifid_pc fetchPC
    let ifid_pc4_in := Signal.mux stall ifid_pc4 fetchPCPlus4
    let squash := (· || ·) <$> stall <*> flushOrDelay

    let clintOffset := alu_result_approx.map (BitVec.extractLsb' 0 16 ·)
    let clintWE := (· && ·) <$> idex_memWrite <*> isCLINT_ex
    let msipMatch     := (· == ·) <$> clintOffset <*> Signal.pure 0x0000#16
    let mtimeLoMatch  := (· == ·) <$> clintOffset <*> Signal.pure 0xBFF8#16
    let mtimeHiMatch  := (· == ·) <$> clintOffset <*> Signal.pure 0xBFFC#16
    let mtimecmpLoMatch := (· == ·) <$> clintOffset <*> Signal.pure 0x4000#16
    let mtimecmpHiMatch := (· == ·) <$> clintOffset <*> Signal.pure 0x4004#16
    let mtimeLoInc := (· + ·) <$> mtimeLoReg <*> Signal.pure 1#32
    let mtimeCarry := (· == ·) <$> mtimeLoInc <*> Signal.pure 0#32
    let mtimeHiInc := Signal.mux mtimeCarry
                        ((· + ·) <$> mtimeHiReg <*> Signal.pure 1#32) mtimeHiReg
    let msipNext := Signal.mux ((· && ·) <$> clintWE <*> msipMatch)
                      ex_rs2_approx msipReg
    let mtimeLoNext := Signal.mux ((· && ·) <$> clintWE <*> mtimeLoMatch)
                         ex_rs2_approx mtimeLoInc
    let mtimeHiNext := Signal.mux ((· && ·) <$> clintWE <*> mtimeHiMatch)
                         ex_rs2_approx mtimeHiInc
    let mtimecmpLoNext := Signal.mux ((· && ·) <$> clintWE <*> mtimecmpLoMatch)
                            ex_rs2_approx mtimecmpLoReg
    let mtimecmpHiNext := Signal.mux ((· && ·) <$> clintWE <*> mtimecmpHiMatch)
                            ex_rs2_approx mtimecmpHiReg

    let csrIsImm := (· == ·) <$> (idex_csrFunct3.map (BitVec.extractLsb' 2 1 ·)) <*> Signal.pure 1#1
    let csrZimm := (· ++ ·) <$> Signal.pure 0#27 <*> idex_rs1Idx
    let csrWdata := Signal.mux csrIsImm csrZimm ex_rs1
    let csrF3Low := idex_csrFunct3.map (BitVec.extractLsb' 0 2 ·)
    let csrIsRW := (· == ·) <$> csrF3Low <*> Signal.pure 0b01#2
    let csrIsRS := (· == ·) <$> csrF3Low <*> Signal.pure 0b10#2
    let csrIsRC := (· == ·) <$> csrF3Low <*> Signal.pure 0b11#2
    let mkCsrNewVal (oldVal : Signal dom (BitVec 32)) :=
      let rsVal := (· ||| ·) <$> oldVal <*> csrWdata
      let rcVal := (· &&& ·) <$> oldVal <*> ((fun x => ~~~ x) <$> csrWdata)
      Signal.mux csrIsRW csrWdata
        (Signal.mux csrIsRS rsVal (Signal.mux csrIsRC rcVal oldVal))
    let mstatusNewCSR  := mkCsrNewVal mstatusReg
    let mieNewCSR      := mkCsrNewVal mieReg
    let mtvecNewCSR    := mkCsrNewVal mtvecReg
    let mscratchNewCSR := mkCsrNewVal mscratchReg
    let mepcNewCSR     := mkCsrNewVal mepcReg
    let mcauseNewCSR   := mkCsrNewVal mcauseReg
    let mtvalNewCSR    := mkCsrNewVal mtvalReg

    let msClearMIE := (· &&& ·) <$> mstatusReg <*> Signal.pure 0xFFFFFFF7#32
    let msSetMPIE := Signal.mux mstatusMIE_flag
      ((· ||| ·) <$> msClearMIE <*> Signal.pure 0x00000080#32)
      ((· &&& ·) <$> msClearMIE <*> Signal.pure 0xFFFFFF7F#32)
    let mstatusTrapVal := (· ||| ·) <$> msSetMPIE <*> Signal.pure 0x00001800#32
    let msClearMPP := (· &&& ·) <$> mstatusReg <*> Signal.pure 0xFFFFE7FF#32
    let msRestoreMIE := Signal.mux mstatusMPIE_flag
      ((· ||| ·) <$> msClearMPP <*> Signal.pure 0x00000008#32)
      ((· &&& ·) <$> msClearMPP <*> Signal.pure 0xFFFFFFF7#32)
    let mstatusMretVal := (· ||| ·) <$> msRestoreMIE <*> Signal.pure 0x00000080#32
    let mstatusNext := Signal.mux trap_taken mstatusTrapVal
      (Signal.mux idex_isMret mstatusMretVal
      (Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMstatus) mstatusNewCSR
        mstatusReg))
    let mieNext := Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMie) mieNewCSR mieReg
    let mtvecNext := Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMtvec) mtvecNewCSR mtvecReg
    let mscratchNext := Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMscratch) mscratchNewCSR mscratchReg
    let mepcNext := Signal.mux trap_taken idex_pc
      (Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMepc) mepcNewCSR mepcReg)
    let mcauseNext := Signal.mux trap_taken trapCause
      (Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMcause) mcauseNewCSR mcauseReg)
    let mtvalNext := Signal.mux trap_taken (Signal.pure 0#32)
      (Signal.mux ((· && ·) <$> idex_isCsr <*> csrIsMtval) mtvalNewCSR mtvalReg)

    let pcNext := Signal.mux trap_taken trap_target
                    (Signal.mux idex_isMret mret_target
                    (Signal.mux flush jumpTarget
                    (Signal.mux stall pcReg
                      pcPlus4)))

    bundleAll! [
      Signal.register 0#32 pcNext,
      Signal.register 0#32 fetchPCIn,
      Signal.register false flush,
      Signal.register 0x00000013#32 ifid_inst_in,
      Signal.register 0#32 ifid_pc_in,
      Signal.register 0#32 ifid_pc4_in,
      Signal.register 0#4 (Signal.mux squash (Signal.pure 0#4) id_aluOp),
      Signal.register false (Signal.mux squash (Signal.pure false) id_regWrite),
      Signal.register false (Signal.mux squash (Signal.pure false) id_memRead),
      Signal.register false (Signal.mux squash (Signal.pure false) id_memWrite),
      Signal.register false (Signal.mux squash (Signal.pure false) id_memToReg),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isBranch),
      Signal.register false (Signal.mux squash (Signal.pure false) id_jump),
      Signal.register false (Signal.mux squash (Signal.pure false) id_auipc),
      Signal.register false (Signal.mux squash (Signal.pure false) id_aluSrcB),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isJALR),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isCsr),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isEcall),
      Signal.register false (Signal.mux squash (Signal.pure false) id_isMret),
      Signal.register 0#32 id_rs1Val,
      Signal.register 0#32 id_rs2Val,
      Signal.register 0#32 id_imm,
      Signal.register 0#5 (Signal.mux squash (Signal.pure 0#5) id_rd),
      Signal.register 0#5 id_rs1,
      Signal.register 0#5 id_rs2,
      Signal.register 0#3 id_funct3,
      Signal.register 0#32 ifid_pc,
      Signal.register 0#32 ifid_pc4,
      Signal.register 0#12 id_csrAddr,
      Signal.register 0#3 id_funct3,
      Signal.register 0#32 alu_result,
      Signal.register 0#5 idex_rd,
      Signal.register false idex_regWrite,
      Signal.register false idex_memToReg,
      Signal.register 0#32 idex_pc4,
      Signal.register false idex_jump,
      Signal.register false idex_isCsr,
      Signal.register 0#32 csr_rdata,
      Signal.register 0#5 wb_addr,
      Signal.register 0#32 wb_data,
      Signal.register false wb_en,
      Signal.register 0#32 alu_result,
      Signal.register 0#32 ex_rs2,
      Signal.register false idex_memWrite,
      Signal.register 0#32 msipNext,
      Signal.register 0#32 mtimeLoNext,
      Signal.register 0#32 mtimeHiNext,
      Signal.register 0xFFFFFFFF#32 mtimecmpLoNext,
      Signal.register 0xFFFFFFFF#32 mtimecmpHiNext,
      Signal.register 0#32 mstatusNext,
      Signal.register 0#32 mieNext,
      Signal.register 0#32 mtvecNext,
      Signal.register 0#32 mscratchNext,
      Signal.register 0#32 mepcNext,
      Signal.register 0#32 mcauseNext,
      Signal.register 0#32 mtvalNext
    ]

/-- RV32I SoC with pre-loaded firmware — Signal DSL.
    Same as rv32iSoC but IMEM is initialized with firmware data
    for Lean4-native simulation via Signal.atTime.

    firmware: function from 12-bit address to 32-bit instruction word -/
def rv32iSoCWithFirmware {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    : Signal dom (BitVec 32) :=
  Signal.fst (Signal.loop (rv32iSoCWithFirmwareBody firmware))

/-- RV32I SoC simulation with memoized loop.
    Uses `Signal.loopMemo` to cache loop output per timestep,
    eliminating stack overflow for sequential simulation. -/
def rv32iSoCSimulate {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    : IO (Signal dom (BitVec 32)) := do
  let soc ← Signal.loopMemo (rv32iSoCWithFirmwareBody firmware)
  return Signal.fst soc

/-- RV32I SoC simulation returning full state tuple.
    Allows extracting PC, store signals, CSRs, etc. for verification.
    State indices: 0=PC, 41=storeAddr, 42=storeData, 43=storeEn -/
def rv32iSoCSimulateFull {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    : IO (Signal dom SoCState) := do
  Signal.loopMemo (rv32iSoCWithFirmwareBody firmware)

/-- Non-memoized full state for debugging -/
def rv32iSoCDebugFull {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    : Signal dom SoCState :=
  Signal.loop (rv32iSoCWithFirmwareBody firmware)

end Sparkle.Examples.RV32.SoC
