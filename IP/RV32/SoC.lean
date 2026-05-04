/-
  RV32I SoC — Signal DSL (flat design)

  All state (pipeline + CLINT + CSR + AI MMIO + S-mode + MMU + UART + divider) in a single Signal.loop.
  122 registers total in a right-nested pair.

  Register index map (0-117):
  Pipeline (0-43): same as Pipeline.lean, except exwb_physAddr inserted at index 31
    0=pcReg, 1=fetchPC, 2=flushDelay, 3-5=ifid_inst/pc/pc4,
    6-18=idex control, 19-29=idex data, 30=exwb_alu, 31=exwb_physAddr,
    32-37=exwb_rd/regW/m2r/pc4/jump/isCsr, 38=exwb_csrRdata,
    39-41=prev_wb_addr/data/en, 42-44=prevStoreAddr/Data/En
  CLINT (45-49): msip, mtimeLo, mtimeHi, mtimecmpLo, mtimecmpHi
  CSR (50-56): mstatus, mie, mtvec, mscratch, mepc, mcause, mtval
  AI MMIO (57-58): aiStatus, aiInput
  Sub-word (59): exwb_funct3
  M-ext (60): idex_isMext
  A-ext (61-69): reservationValid, reservationAddr, idex_isAMO, idex_amoOp, exwb_isAMO, exwb_amoOp,
                 pendingWriteEn, pendingWriteAddr, pendingWriteData
  S-mode CSRs + privilege (70-79): privMode, sie, stvec, sscratch, sepc, scause, stval, satp,
                                    medeleg, mideleg
  MMU TLB + PTW (80-107): mmuState, ptwState, ptwVaddr, ptwPte, ptwMega, replPtr,
                           4×TLB entries (valid, vpn, ppn, flags, mega),
                           ptwIsIfetch, ifetchFaultPending
  Pipeline additions (108-109): idex_isSret, idex_isSFenceVMA
  UART 8250 (110-115): uartLCR, uartIER, uartMCR, uartSCR, uartDLL, uartDLM
  Counter CSRs (116-117): mcounteren, scounteren
  Divider (118): divPending
  D-side TLB miss (119-121): dMissPC, dMissVaddr, dMissIsStore

  Bug fixes ported from verilator/rv32i_soc.sv:
  1. exwb_physAddr: WB bus decode uses physical address (not virtual alu_result)
  2. holdEX: freeze EX stage when DMEM port is hijacked by pending write
  3. fetchPC flush: fetchPC_next = flush ? pcReg_next : (stall ? fetchPC : pcReg)

  Architecture note:
    The DMEM read address uses an "approximate" ALU result that omits
    load-result forwarding (WB→EX when exwb_m2r=true). This is safe
    because load-use hazards are stalled, so the only cycle where the
    approximation differs is the stall-bubble cycle, whose BRAM read
    result is never consumed.
-/

import Sparkle
import Sparkle.Core.JITLoop
import Sparkle.Compiler.Elab
import IP.RV32.Core
import IP.RV32.Bus.Decoder
import IP.RV32.Bus.StoreWidth
import IP.RV32.Bus.LoadWidth
import IP.RV32.Divider
import IP.RV32.CSR.Types
-- Level-1a BitNet MMIO peripheral wrapper.
-- Exposes `bitNetPeripheral : Signal dom (BitVec 32) → Signal dom (BitVec 32)`
-- which we wire into the AI MMIO region at 0x40000000 below.
import IP.RV32.BitNetPeripheral
import IP.RV32.AMO.Reservation
import IP.RV32.Privilege.PrivMode
import IP.RV32.Trap.TrapPC
import IP.RV32.Trap.Delegation
import IP.RV32.Trap.IRQEnable
import IP.RV32.Trap.Cause
import IP.RV32.Trap.TrapTaken
import IP.RV32.CSR.MStatus
import IP.RV32.CSR.MStatusNext
import IP.RV32.CSR.NewValue
import IP.RV32.CSR.Commit
import IP.RV32.Pipeline.SuppressEXWB
import IP.RV32.Pipeline.PCNext
import IP.RV32.Pipeline.Writeback

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace Sparkle.IP.RV32.SoC

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32
open Sparkle.IP.RV32
open Sparkle.IP.RV32.CSR

def nopInst : BitVec 32 := 0x00000013#32

-- rv32iSoC (synthesis-only, phantom-type-safe version) is in SoCVerilog.lean
-- to prevent module-init stack overflow from closed-term evaluation.

declare_signal_state SoCState
  -- Pipeline (0-5)
  | pcReg          : BitVec 32  := 0#32
  | fetchPC        : BitVec 32  := 0#32
  | flushDelay     : Bool       := false
  | ifid_inst      : BitVec 32  := 0x00000013#32
  | ifid_pc        : BitVec 32  := 0#32
  | ifid_pc4       : BitVec 32  := 0#32
  -- ID/EX control (6-18)
  | idex_aluOp     : BitVec 4   := 0#4
  | idex_regWrite  : Bool       := false
  | idex_memRead   : Bool       := false
  | idex_memWrite  : Bool       := false
  | idex_memToReg  : Bool       := false
  | idex_branch    : Bool       := false
  | idex_jump      : Bool       := false
  | idex_auipc     : Bool       := false
  | idex_aluSrcB   : Bool       := false
  | idex_isJalr    : Bool       := false
  | idex_isCsr     : Bool       := false
  | idex_isEcall   : Bool       := false
  | idex_isMret    : Bool       := false
  -- ID/EX data (19-29)
  | idex_rs1Val    : BitVec 32  := 0#32
  | idex_rs2Val    : BitVec 32  := 0#32
  | idex_imm       : BitVec 32  := 0#32
  | idex_rd        : BitVec 5   := 0#5
  | idex_rs1Idx    : BitVec 5   := 0#5
  | idex_rs2Idx    : BitVec 5   := 0#5
  | idex_funct3    : BitVec 3   := 0#3
  | idex_pc        : BitVec 32  := 0#32
  | idex_pc4       : BitVec 32  := 0#32
  | idex_csrAddr   : BitVec 12  := 0#12
  | idex_csrFunct3 : BitVec 3   := 0#3
  -- EX/WB (30-38)
  | exwb_alu       : BitVec 32  := 0#32
  | exwb_physAddr  : BitVec 32  := 0#32
  | exwb_rd        : BitVec 5   := 0#5
  | exwb_regW      : Bool       := false
  | exwb_m2r       : Bool       := false
  | exwb_pc4       : BitVec 32  := 0#32
  | exwb_jump      : Bool       := false
  | exwb_isCsr     : Bool       := false
  | exwb_csrRdata  : BitVec 32  := 0#32
  -- WB forwarding (39-41)
  | prev_wb_addr   : BitVec 5   := 0#5
  | prev_wb_data   : BitVec 32  := 0#32
  | prev_wb_en     : Bool       := false
  -- Store history (42-44)
  | prevStoreAddr  : BitVec 32  := 0#32
  | prevStoreData  : BitVec 32  := 0#32
  | prevStoreEn    : Bool       := false
  -- CLINT (45-49)
  | msipReg        : BitVec 32  := 0#32
  | mtimeLoReg     : BitVec 32  := 0#32
  | mtimeHiReg     : BitVec 32  := 0#32
  | mtimecmpLoReg  : BitVec 32  := 0xFFFFFFFF#32
  | mtimecmpHiReg  : BitVec 32  := 0xFFFFFFFF#32
  -- CSR M-mode (50-56)
  | mstatusReg     : BitVec 32  := 0#32
  | mieReg         : BitVec 32  := 0#32
  | mtvecReg       : BitVec 32  := 0#32
  | mscratchReg    : BitVec 32  := 0#32
  | mepcReg        : BitVec 32  := 0#32
  | mcauseReg      : BitVec 32  := 0#32
  | mtvalReg       : BitVec 32  := 0#32
  -- AI MMIO (57-58)
  | aiStatusReg    : BitVec 32  := 0#32
  | aiInputReg     : BitVec 32  := 0#32
  -- Sub-word (59)
  | exwb_funct3    : BitVec 3   := 0#3
  -- M-ext (60)
  | idex_isMext    : Bool       := false
  -- A-ext (61-69)
  | reservationValid : Bool     := false
  | reservationAddr  : BitVec 32 := 0#32
  | idex_isAMO     : Bool       := false
  | idex_amoOp     : BitVec 5   := 0#5
  | exwb_isAMO     : Bool       := false
  | exwb_amoOp     : BitVec 5   := 0#5
  | pendingWriteEn   : Bool     := false
  | pendingWriteAddr : BitVec 32 := 0#32
  | pendingWriteData : BitVec 32 := 0#32
  -- S-mode CSRs + privilege (70-79)
  | privMode       : BitVec 2   := 3#2
  | sieReg         : BitVec 32  := 0#32
  | stvecReg       : BitVec 32  := 0#32
  | sscratchReg    : BitVec 32  := 0#32
  | sepcReg        : BitVec 32  := 0#32
  | scauseReg      : BitVec 32  := 0#32
  | stvalReg       : BitVec 32  := 0#32
  | satpReg        : BitVec 32  := 0#32
  | medelegReg     : BitVec 32  := 0#32
  | midelegReg     : BitVec 32  := 0#32
  -- MMU TLB + PTW (80-107)
  | mmuStateReg    : BitVec 3   := 0#3
  | ptwStateReg    : BitVec 3   := 0#3
  | ptwVaddrReg    : BitVec 32  := 0#32
  | ptwPteReg      : BitVec 32  := 0#32
  | ptwMegaReg     : Bool       := false
  | replPtrReg     : BitVec 2   := 0#2
  | tlb0Valid      : Bool       := false
  | tlb0VPN        : BitVec 20  := 0#20
  | tlb0PPN        : BitVec 22  := 0#22
  | tlb0Flags      : BitVec 8   := 0#8
  | tlb0Mega       : Bool       := false
  | tlb1Valid      : Bool       := false
  | tlb1VPN        : BitVec 20  := 0#20
  | tlb1PPN        : BitVec 22  := 0#22
  | tlb1Flags      : BitVec 8   := 0#8
  | tlb1Mega       : Bool       := false
  | tlb2Valid      : Bool       := false
  | tlb2VPN        : BitVec 20  := 0#20
  | tlb2PPN        : BitVec 22  := 0#22
  | tlb2Flags      : BitVec 8   := 0#8
  | tlb2Mega       : Bool       := false
  | tlb3Valid      : Bool       := false
  | tlb3VPN        : BitVec 20  := 0#20
  | tlb3PPN        : BitVec 22  := 0#22
  | tlb3Flags      : BitVec 8   := 0#8
  | tlb3Mega       : Bool       := false
  | ptwIsIfetch    : Bool       := false
  | ifetchFaultPending : Bool   := false
  -- Pipeline additions (108-109)
  | idex_isSret      : Bool     := false
  | idex_isSFenceVMA : Bool     := false
  -- UART 8250 registers (110-115)
  | uartLCRReg     : BitVec 8   := 0#8
  | uartIERReg     : BitVec 8   := 0#8
  | uartMCRReg     : BitVec 8   := 0#8
  | uartSCRReg     : BitVec 8   := 0#8
  | uartDLLReg     : BitVec 8   := 0#8
  | uartDLMReg     : BitVec 8   := 0#8
  -- Counter CSRs (116-117)
  | mcounterenReg  : BitVec 32  := 0#32
  | scounterenReg  : BitVec 32  := 0#32
  -- Divider pending (118)
  | divPending     : Bool       := false
  -- D-side TLB miss registers (119-121)
  | dMissPC        : BitVec 32  := 0#32
  | dMissVaddr     : BitVec 32  := 0#32
  | dMissIsStore   : Bool       := false
  -- Stall-delay register (122). Captures previous-cycle's `stall` so that
  -- the cycle-after-stall-release squashes its IDEX, preventing the same
  -- instruction from being latched twice (see squash usage above).
  | stallDelay     : Bool       := false
  -- mip software-writable bits (123). Only the S-mode pending bits
  -- (SSIP=1, STIP=5, SEIP=9) are writable; the M-mode pending bits
  -- (MSIP=3, MTIP=7) are hardware-driven from CLINT and ORed at read time.
  -- Used by OpenSBI's `csr_set(CSR_MIP, MIP_STIP)` to forward timer
  -- interrupts to S-mode.
  | mipSoftReg     : BitVec 32  := 0#32

/-- Loop body for RV32I SoC (122 registers).
    Parameterized by `imem_rdata` (pre-resolved instruction read data) so the
    same body works for simulation and synthesis. Callers compute imem_rdata:
    - Simulation: `(projN! state 122 1).map (BitVec.extractLsb' 2 12 ·) |>.map firmware`
    - Synthesis:  `Signal.memoryComboRead wr_addr wr_data wr_en imem_addr`
    Optionally takes DMEM external write signals for synthesis firmware loading. -/
def rv32iSoCBody {dom : DomainConfig}
    (imem_rdata : Signal dom (BitVec 32))
    (dmemExtWriteEn : Signal dom Bool := Signal.pure false)
    (dmemExtWriteAddr : Signal dom (BitVec 23) := Signal.pure 0#23)
    (dmemExtWriteData : Signal dom (BitVec 32) := Signal.pure 0#32)
    (state : Signal dom SoCState) : Signal dom SoCState :=
    -- Extract all 122 register outputs via accessor defs
    let pcReg          := SoCState.pcReg state
    let fetchPC        := SoCState.fetchPC state
    let flushDelay     := SoCState.flushDelay state
    let stallDelay     := SoCState.stallDelay state
    let ifid_inst      := SoCState.ifid_inst state
    let ifid_pc        := SoCState.ifid_pc state
    let ifid_pc4       := SoCState.ifid_pc4 state
    let idex_aluOp     := SoCState.idex_aluOp state
    let idex_regWrite  := SoCState.idex_regWrite state
    let idex_memRead   := SoCState.idex_memRead state
    let idex_memWrite  := SoCState.idex_memWrite state
    let idex_memToReg  := SoCState.idex_memToReg state
    let idex_branch    := SoCState.idex_branch state
    let idex_jump      := SoCState.idex_jump state
    let idex_auipc     := SoCState.idex_auipc state
    let idex_aluSrcB   := SoCState.idex_aluSrcB state
    let idex_isJalr    := SoCState.idex_isJalr state
    let idex_isCsr     := SoCState.idex_isCsr state
    let idex_isEcall   := SoCState.idex_isEcall state
    let idex_isMret    := SoCState.idex_isMret state
    let idex_rs1Val    := SoCState.idex_rs1Val state
    let idex_rs2Val    := SoCState.idex_rs2Val state
    let idex_imm       := SoCState.idex_imm state
    let idex_rd        := SoCState.idex_rd state
    let idex_rs1Idx    := SoCState.idex_rs1Idx state
    let idex_rs2Idx    := SoCState.idex_rs2Idx state
    let idex_funct3    := SoCState.idex_funct3 state
    let idex_pc        := SoCState.idex_pc state
    let idex_pc4       := SoCState.idex_pc4 state
    let idex_csrAddr   := SoCState.idex_csrAddr state
    let idex_csrFunct3 := SoCState.idex_csrFunct3 state
    let exwb_alu       := SoCState.exwb_alu state
    let exwb_physAddr  := SoCState.exwb_physAddr state
    let exwb_rd        := SoCState.exwb_rd state
    let exwb_regW      := SoCState.exwb_regW state
    let exwb_m2r       := SoCState.exwb_m2r state
    let exwb_pc4       := SoCState.exwb_pc4 state
    let exwb_jump      := SoCState.exwb_jump state
    let exwb_isCsr     := SoCState.exwb_isCsr state
    let exwb_csrRdata  := SoCState.exwb_csrRdata state
    let prev_wb_addr   := SoCState.prev_wb_addr state
    let prev_wb_data   := SoCState.prev_wb_data state
    let prev_wb_en     := SoCState.prev_wb_en state
    let prevStoreAddr  := SoCState.prevStoreAddr state
    let prevStoreData  := SoCState.prevStoreData state
    let prevStoreEn    := SoCState.prevStoreEn state
    let msipReg        := SoCState.msipReg state
    let mtimeLoReg     := SoCState.mtimeLoReg state
    let mtimeHiReg     := SoCState.mtimeHiReg state
    let mtimecmpLoReg  := SoCState.mtimecmpLoReg state
    let mtimecmpHiReg  := SoCState.mtimecmpHiReg state
    let mstatusReg     := SoCState.mstatusReg state
    let mieReg         := SoCState.mieReg state
    let mtvecReg       := SoCState.mtvecReg state
    let mscratchReg    := SoCState.mscratchReg state
    let mepcReg        := SoCState.mepcReg state
    let mcauseReg      := SoCState.mcauseReg state
    let mtvalReg       := SoCState.mtvalReg state
    let mipSoftReg     := SoCState.mipSoftReg state
    let aiStatusReg    := SoCState.aiStatusReg state
    let aiInputReg     := SoCState.aiInputReg state
    let exwb_funct3    := SoCState.exwb_funct3 state
    let idex_isMext    := SoCState.idex_isMext state
    let reservationValid := SoCState.reservationValid state
    let reservationAddr  := SoCState.reservationAddr state
    let idex_isAMO     := SoCState.idex_isAMO state
    let idex_amoOp     := SoCState.idex_amoOp state
    let exwb_isAMO     := SoCState.exwb_isAMO state
    let exwb_amoOp     := SoCState.exwb_amoOp state
    let pendingWriteEn   := SoCState.pendingWriteEn state
    let pendingWriteAddr := SoCState.pendingWriteAddr state
    let pendingWriteData := SoCState.pendingWriteData state
    -- S-mode CSRs + privilege (70-79)
    let privMode         := SoCState.privMode state
    let sieReg           := SoCState.sieReg state
    let stvecReg         := SoCState.stvecReg state
    let sscratchReg      := SoCState.sscratchReg state
    let sepcReg          := SoCState.sepcReg state
    let scauseReg        := SoCState.scauseReg state
    let stvalReg         := SoCState.stvalReg state
    let satpReg          := SoCState.satpReg state
    let medelegReg       := SoCState.medelegReg state
    let midelegReg       := SoCState.midelegReg state
    -- MMU TLB + PTW (80-107)
    let mmuStateReg      := SoCState.mmuStateReg state
    let ptwStateReg      := SoCState.ptwStateReg state
    let ptwVaddrReg      := SoCState.ptwVaddrReg state
    let ptwPteReg        := SoCState.ptwPteReg state
    let ptwMegaReg       := SoCState.ptwMegaReg state
    let replPtrReg       := SoCState.replPtrReg state
    let tlb0Valid        := SoCState.tlb0Valid state
    let tlb0VPN          := SoCState.tlb0VPN state
    let tlb0PPN          := SoCState.tlb0PPN state
    let tlb0Flags        := SoCState.tlb0Flags state
    let tlb0Mega         := SoCState.tlb0Mega state
    let tlb1Valid        := SoCState.tlb1Valid state
    let tlb1VPN          := SoCState.tlb1VPN state
    let tlb1PPN          := SoCState.tlb1PPN state
    let tlb1Flags        := SoCState.tlb1Flags state
    let tlb1Mega         := SoCState.tlb1Mega state
    let tlb2Valid        := SoCState.tlb2Valid state
    let tlb2VPN          := SoCState.tlb2VPN state
    let tlb2PPN          := SoCState.tlb2PPN state
    let tlb2Flags        := SoCState.tlb2Flags state
    let tlb2Mega         := SoCState.tlb2Mega state
    let tlb3Valid        := SoCState.tlb3Valid state
    let tlb3VPN          := SoCState.tlb3VPN state
    let tlb3PPN          := SoCState.tlb3PPN state
    let tlb3Flags        := SoCState.tlb3Flags state
    let tlb3Mega         := SoCState.tlb3Mega state
    let ptwIsIfetch      := SoCState.ptwIsIfetch state
    let ifetchFaultPending := SoCState.ifetchFaultPending state
    -- Pipeline additions (108-109)
    let idex_isSret      := SoCState.idex_isSret state
    let idex_isSFenceVMA := SoCState.idex_isSFenceVMA state
    -- UART 8250 registers (110-115)
    let uartLCRReg   := SoCState.uartLCRReg state
    let uartIERReg   := SoCState.uartIERReg state
    let uartMCRReg   := SoCState.uartMCRReg state
    let uartSCRReg   := SoCState.uartSCRReg state
    let uartDLLReg   := SoCState.uartDLLReg state
    let uartDLMReg   := SoCState.uartDLMReg state
    -- Counter CSRs (116-117)
    let mcounterenReg := SoCState.mcounterenReg state
    let scounterenReg := SoCState.scounterenReg state
    -- Divider state (118)
    let divPending       := SoCState.divPending state
    -- D-side TLB miss registers (119-121)
    let dMissPC          := SoCState.dMissPC state
    let dMissVaddr       := SoCState.dMissVaddr state
    let dMissIsStore     := SoCState.dMissIsStore state

    -- Phase 1-5: identical to rv32iSoC except IMEM uses memoryWithInit
    let wbRdNz := ~~~(exwb_rd === 0#5)
    let wb_addr := exwb_rd
    let wb_en   := exwb_regW &&& wbRdNz
    -- Forwarding-cycle approximate WB value (proven in Pipeline/Writeback.lean):
    -- 3-way mux excluding the load case (load result not yet available).
    let wb_data_non_mem :=
      Sparkle.IP.RV32.Pipeline.wbResultNonMemSignal
        exwb_isCsr exwb_csrRdata exwb_jump exwb_pc4 exwb_alu
    let fwd_rs1_match := wb_en &&& (wb_addr === idex_rs1Idx)
    let fwd_rs2_match := wb_en &&& (wb_addr === idex_rs2Idx)

    let fwd_val_approx := Signal.mux exwb_m2r idex_rs1Val wb_data_non_mem
    let ex_rs1_approx := Signal.mux fwd_rs1_match fwd_val_approx idex_rs1Val
    let fwd_val2_approx := Signal.mux exwb_m2r idex_rs2Val wb_data_non_mem
    let ex_rs2_approx := Signal.mux fwd_rs2_match fwd_val2_approx idex_rs2Val
    let alu_a_approx := Signal.mux idex_auipc idex_pc ex_rs1_approx
    let alu_b_approx := Signal.mux idex_aluSrcB idex_imm ex_rs2_approx
    let alu_result_approx := aluSignal idex_aluOp alu_a_approx alu_b_approx

    -- IMEM read data is provided by the caller (imem_rdata parameter).
    -- Must be combinational (not synchronous memory) so that imem_rdata.val t
    -- = IMEM[fetchPC.val t], aligning with ifid_pc_in = fetchPC.val t.

    -- =========================================================================
    -- MMU/PTW state decode and address computation (early, for DMEM addr mux)
    -- =========================================================================
    let satpMode := (satpReg.map (BitVec.extractLsb' 31 1 ·)) === 1#1
    let isMmode := privMode === 3#2
    let bypassMMU := isMmode ||| (~~~satpMode)
    -- MMU FSM: IDLE=0, TLB_LOOKUP=1, PTW_WALK=2, DONE=3, FAULT=4
    let isMMUIdle   := mmuStateReg === 0#3
    let isPTWWalk   := mmuStateReg === 2#3
    let isMMUDone   := mmuStateReg === 3#3
    let isMMUFault  := mmuStateReg === 4#3
    -- D-side MMU redirect: after PTW completes, re-execute the faulting instruction
    let dMMURedirect := isMMUDone &&& (~~~bypassMMU)
    -- PTW FSM: IDLE=0, L1_REQ=1, L1_WAIT=2, L0_REQ=3, L0_WAIT=4, DONE=5, FAULT=6
    let ptwIsIdle   := ptwStateReg === 0#3
    let ptwIsL1Req  := ptwStateReg === 1#3
    let ptwIsL1Wait := ptwStateReg === 2#3
    let ptwIsL0Req  := ptwStateReg === 3#3
    let ptwIsL0Wait := ptwStateReg === 4#3
    let ptwIsDone   := ptwStateReg === 5#3
    let ptwIsFault  := ptwStateReg === 6#3
    -- PTW memory address generation
    -- Sv32: L1 addr = {satpPPN[19:0], 12'd0} + {VPN1, 2'd0}
    --        L0 addr = {ptePPN[19:0], 12'd0} + {VPN0, 2'd0}
    let satpPPN20 := satpReg.map (BitVec.extractLsb' 0 20 ·)
    let satpPPNShifted := satpPPN20 ++ 0#12
    let ptwVPN1 := ptwVaddrReg.map (BitVec.extractLsb' 22 10 ·)
    let ptwVPN0 := ptwVaddrReg.map (BitVec.extractLsb' 12 10 ·)
    let ptwVPN1x4 := ptwVPN1 ++ 0#2
    let ptwVPN1Ext := 0#20 ++ ptwVPN1x4
    let l1Addr := satpPPNShifted + ptwVPN1Ext
    let ptePPNFull := ptwPteReg.map (BitVec.extractLsb' 10 22 ·)
    let ptePPN20 := ptePPNFull.map (BitVec.extractLsb' 0 20 ·)
    let ptePPNShifted := ptePPN20 ++ 0#12
    let ptwVPN0x4 := ptwVPN0 ++ 0#2
    let ptwVPN0Ext := 0#20 ++ ptwVPN0x4
    let l0Addr := ptePPNShifted + ptwVPN0Ext
    let ptwMemAddr := Signal.mux ptwIsL1Req l1Addr l0Addr
    let ptwMemActive := ptwIsL1Req ||| ptwIsL0Req
    let ptwMemWordAddr := ptwMemAddr.map (BitVec.extractLsb' 2 23 ·)
    -- MMU stall: busy (not IDLE/DONE/FAULT) and not bypassed
    let mmuBusy := ~~~((isMMUIdle ||| isMMUDone) ||| isMMUFault)
    let mmuStall := mmuBusy &&& (~~~bypassMMU)

    -- =========================================================================
    -- D-side TLB lookup (early, needed for effectiveAddr used by bus decode)
    -- =========================================================================
    let dVPN := alu_result_approx.map (BitVec.extractLsb' 12 20 ·)
    let dPageOffset := alu_result_approx.map (BitVec.extractLsb' 0 12 ·)

    let tlb0FullMatch := tlb0VPN === dVPN
    let tlb0MegaMatch := (tlb0VPN.map (BitVec.extractLsb' 10 10 ·)) === (dVPN.map (BitVec.extractLsb' 10 10 ·))
    let tlb0VPNMatch := Signal.mux tlb0Mega tlb0MegaMatch tlb0FullMatch
    let tlb0Hit := tlb0Valid &&& tlb0VPNMatch

    let tlb1FullMatch := tlb1VPN === dVPN
    let tlb1MegaMatch := (tlb1VPN.map (BitVec.extractLsb' 10 10 ·)) === (dVPN.map (BitVec.extractLsb' 10 10 ·))
    let tlb1VPNMatch := Signal.mux tlb1Mega tlb1MegaMatch tlb1FullMatch
    let tlb1Hit := tlb1Valid &&& tlb1VPNMatch

    let tlb2FullMatch := tlb2VPN === dVPN
    let tlb2MegaMatch := (tlb2VPN.map (BitVec.extractLsb' 10 10 ·)) === (dVPN.map (BitVec.extractLsb' 10 10 ·))
    let tlb2VPNMatch := Signal.mux tlb2Mega tlb2MegaMatch tlb2FullMatch
    let tlb2Hit := tlb2Valid &&& tlb2VPNMatch

    let tlb3FullMatch := tlb3VPN === dVPN
    let tlb3MegaMatch := (tlb3VPN.map (BitVec.extractLsb' 10 10 ·)) === (dVPN.map (BitVec.extractLsb' 10 10 ·))
    let tlb3VPNMatch := Signal.mux tlb3Mega tlb3MegaMatch tlb3FullMatch
    let tlb3Hit := tlb3Valid &&& tlb3VPNMatch

    let anyTLBHit := (tlb0Hit ||| tlb1Hit) ||| (tlb2Hit ||| tlb3Hit)

    let tlbPPN := Signal.mux tlb0Hit tlb0PPN
      (Signal.mux tlb1Hit tlb1PPN
      (Signal.mux tlb2Hit tlb2PPN
      (Signal.mux tlb3Hit tlb3PPN
        (Signal.pure 0#22))))

    let tlbMega := Signal.mux tlb0Hit tlb0Mega
      (Signal.mux tlb1Hit tlb1Mega
      (Signal.mux tlb2Hit tlb2Mega
      (Signal.mux tlb3Hit tlb3Mega
        (Signal.pure false))))

    -- D-side physical address from TLB. See I-side comment above for the
    -- Sv32 megapage / 4K formulas. Megapage uses PPN[1] (PPN bits [21:10])
    -- as PA[31:22]; vaddr[21:0] supplies the rest.
    let dtlbPPN_20 := tlbPPN.map (BitVec.extractLsb' 0 20 ·)
    let dtlbPPN_hi10 := tlbPPN.map (BitVec.extractLsb' 10 10 ·)
    let vaLow22 := alu_result_approx.map (BitVec.extractLsb' 0 22 ·)
    let dPhysAddrMega := dtlbPPN_hi10 ++ vaLow22
    let dPhysAddrReg := dtlbPPN_20 ++ dPageOffset
    let dPhysAddr := Signal.mux tlbMega dPhysAddrMega dPhysAddrReg
    -- Effective address: use translated physical when MMU active and TLB hit
    let useTranslatedAddr := (~~~bypassMMU) &&& anyTLBHit
    let effectiveAddr := Signal.mux useTranslatedAddr dPhysAddr alu_result_approx

    -- D-side TLB miss: need translation but no TLB hit (first cycle only, while MMU+PTW idle)
    let dMemAccess := idex_memRead ||| idex_memWrite
    let needTranslateD := dMemAccess &&& (~~~bypassMMU)
    let dTLBMiss := needTranslateD &&& ((~~~anyTLBHit) &&& (isMMUIdle &&& ptwIsIdle))

    -- Bus address decode uses effectiveAddr (physical after MMU translation).
    -- Spec proven in Bus/Decoder.lean: every address routes to exactly one
    -- of {CLINT, MMIO, UART, DMEM} (mutex + exhaustive).
    let isCLINT_ex := Sparkle.IP.RV32.Bus.isCLINTSignal effectiveAddr
    let is_mmio_ex := Sparkle.IP.RV32.Bus.isMmioSignal effectiveAddr
    let isUART_ex := Sparkle.IP.RV32.Bus.isUARTSignal effectiveAddr
    let isDMEM_ex := Sparkle.IP.RV32.Bus.isDMEMSignal isCLINT_ex is_mmio_ex isUART_ex

    let dmem_write_addr := effectiveAddr.map (BitVec.extractLsb' 2 23 ·)
    let pendWriteWordAddr := pendingWriteAddr.map (BitVec.extractLsb' 2 23 ·)
    let dmem_read_addr  := Signal.mux ptwMemActive ptwMemWordAddr
      (Signal.mux pendingWriteEn pendWriteWordAddr
        (effectiveAddr.map (BitVec.extractLsb' 2 23 ·)))
    -- SC fail at EX: if SC and reservation invalid OR addr mismatch, suppress
    -- the memory write. The PA at EX time may be raw (if no MMU) or translated
    -- (effectiveAddr is the chosen one); use that for reservation match.
    let idexIsSC_ex := idex_isAMO &&& (idex_amoOp === 0b00011#5)
    let scExAddrMatch := effectiveAddr === reservationAddr
    let scExFails := idexIsSC_ex &&& (~~~(reservationValid &&& scExAddrMatch))
    let dmem_we := idex_memWrite &&& (isDMEM_ex &&& (~~~dTLBMiss)) &&& (~~~scExFails)

    -- Sub-word store: byte-enable logic based on funct3 and addr[1:0]
    let storeByteOff := alu_result_approx.map (BitVec.extractLsb' 0 2 ·)
    let storeByteOff0 := storeByteOff === 0#2
    let storeByteOff1 := storeByteOff === 1#2
    let storeByteOff2 := storeByteOff === 2#2
    let storeByteOff3 := storeByteOff === 3#2
    let storeAddrBit1 := alu_result_approx.map (BitVec.extractLsb' 1 1 ·)
    let storeHalfLow := storeAddrBit1 === 0#1
    let storeHalfHigh := ~~~storeHalfLow
    let storeFunct3Low := idex_funct3.map (BitVec.extractLsb' 0 2 ·)
    let isSB := storeFunct3Low === 0#2
    let isSH := storeFunct3Low === 1#2
    let isSW := storeFunct3Low === 2#2
    -- Byte WE: SW => all bytes; SH lo/hi => 2 bytes; SB => 1 byte (per addr[1:0]).
    -- Spec proven in Bus/StoreWidth.lean.
    let b0we := Sparkle.IP.RV32.Bus.b0weSignal isSB isSH isSW storeHalfLow storeByteOff0
    let b1we := Sparkle.IP.RV32.Bus.b1weSignal isSB isSH isSW storeHalfLow storeByteOff1
    let b2we := Sparkle.IP.RV32.Bus.b2weSignal isSB isSH isSW storeHalfHigh storeByteOff2
    let b3we := Sparkle.IP.RV32.Bus.b3weSignal isSB isSH isSW storeHalfHigh storeByteOff3
    let byte0_we := dmem_we &&& b0we
    let byte1_we := dmem_we &&& b1we
    let byte2_we := dmem_we &&& b2we
    let byte3_we := dmem_we &&& b3we

    -- Byte write data: position rs2 bytes for each byte lane
    let rs2_byte0 := ex_rs2_approx.map (BitVec.extractLsb' 0 8 ·)
    let rs2_byte1 := ex_rs2_approx.map (BitVec.extractLsb' 8 8 ·)
    let rs2_byte2 := ex_rs2_approx.map (BitVec.extractLsb' 16 8 ·)
    let rs2_byte3 := ex_rs2_approx.map (BitVec.extractLsb' 24 8 ·)
    -- SB: all lanes get rs2[7:0]; SH: low/high half; SW: each lane gets its byte
    let byte0_wdata := rs2_byte0
    let byte1_wdata := Signal.mux isSB rs2_byte0 rs2_byte1
    let byte2_wdata := Signal.mux isSW rs2_byte2 rs2_byte0
    let byte3_wdata := Signal.mux isSW rs2_byte3 (Signal.mux isSB rs2_byte0 rs2_byte1)

    -- Pending AMO write: registered data from previous WB stage AMO computation
    -- pendingWriteEn/Addr/Data are registers set when non-LR/SC AMO was in WB
    -- (pendWriteWordAddr already defined above for dmem_read_addr mux)
    let pendByte0 := pendingWriteData.map (BitVec.extractLsb' 0 8 ·)
    let pendByte1 := pendingWriteData.map (BitVec.extractLsb' 8 8 ·)
    let pendByte2 := pendingWriteData.map (BitVec.extractLsb' 16 8 ·)
    let pendByte3 := pendingWriteData.map (BitVec.extractLsb' 24 8 ·)

    -- Final DMEM write: mux between normal EX store and pending AMO write
    let final_dmem_write_addr := Signal.mux pendingWriteEn pendWriteWordAddr dmem_write_addr
    let final_byte0_wdata := Signal.mux pendingWriteEn pendByte0 byte0_wdata
    let final_byte1_wdata := Signal.mux pendingWriteEn pendByte1 byte1_wdata
    let final_byte2_wdata := Signal.mux pendingWriteEn pendByte2 byte2_wdata
    let final_byte3_wdata := Signal.mux pendingWriteEn pendByte3 byte3_wdata
    let final_byte0_we := byte0_we ||| pendingWriteEn
    let final_byte1_we := byte1_we ||| pendingWriteEn
    let final_byte2_we := byte2_we ||| pendingWriteEn
    let final_byte3_we := byte3_we ||| pendingWriteEn

    -- External DMEM write port muxing (for firmware/data loading during reset)
    -- External writes take priority over pipeline writes when dmemExtWriteEn=true
    let dmem_ext_byte0 := dmemExtWriteData.map (BitVec.extractLsb' 0 8 ·)
    let dmem_ext_byte1 := dmemExtWriteData.map (BitVec.extractLsb' 8 8 ·)
    let dmem_ext_byte2 := dmemExtWriteData.map (BitVec.extractLsb' 16 8 ·)
    let dmem_ext_byte3 := dmemExtWriteData.map (BitVec.extractLsb' 24 8 ·)
    let actual_dmem_write_addr := Signal.mux dmemExtWriteEn dmemExtWriteAddr final_dmem_write_addr
    let actual_byte0_wdata := Signal.mux dmemExtWriteEn dmem_ext_byte0 final_byte0_wdata
    let actual_byte1_wdata := Signal.mux dmemExtWriteEn dmem_ext_byte1 final_byte1_wdata
    let actual_byte2_wdata := Signal.mux dmemExtWriteEn dmem_ext_byte2 final_byte2_wdata
    let actual_byte3_wdata := Signal.mux dmemExtWriteEn dmem_ext_byte3 final_byte3_wdata
    -- "Proto" actual_byte_we: includes the existing gating
    -- (idex_memWrite, isDMEM_ex, ¬dTLBMiss, ¬scExFails) plus
    -- pendingWriteEn (for AMO writeback) and dmemExtWriteEn (for
    -- external firmware loading).
    let proto_byte0_we := final_byte0_we ||| dmemExtWriteEn
    let proto_byte1_we := final_byte1_we ||| dmemExtWriteEn
    let proto_byte2_we := final_byte2_we ||| dmemExtWriteEn
    let proto_byte3_we := final_byte3_we ||| dmemExtWriteEn

    -- =========================================================================
    -- Hoisted trap_taken computation, for validEX-gating of DRAM writes.
    --
    -- This duplicates the pieces of trap_taken (~line 919) that are needed
    -- to compute validEX BEFORE the byte_we go into the four byte-wide
    -- DRAMs. The duplication is by design: trap_taken's full computation
    -- chain (CSR muxes, mtime comparisons, S-mode int paths) is too tangled
    -- to move wholesale, but each individual leaf is a simple bit-extract
    -- from a state register. We recompute exactly those leaves here, gate
    -- the byte_we, then let the original trap_taken further down stand on
    -- its own.
    --
    -- Why we need this: dmem_we (DRAM byte-enable) is the only side-effect
    -- bearing pipeline output that was NOT gated on `validEX`. CLINT, MMIO,
    -- and UART writes all use `&&& validEX`, so when a trap fires while a
    -- store is in IDEX, peripheral writes are dropped but the DRAM commit
    -- happens. After sret, mepc=idex_pc (fix 01c7177) re-runs the store,
    -- causing a double-commit. This block closes that asymmetry.
    --
    -- The witness is `dmemWe_not_gated_by_trap` in
    -- `IP/RV32/Pipeline/AbortGuarantee.lean`.
    -- =========================================================================
    let early_pageFault := isMMUFault &&& (~~~bypassMMU)
    let early_ifetchPageFault := ifetchFaultPending &&& (~~~bypassMMU)
    -- Timer / software / S-mode interrupt enables (mirror lines 870..919)
    let early_mstatusMIE := (mstatusReg.map (BitVec.extractLsb' 3 1 ·)) === 1#1
    let early_mstatusSIE := (mstatusReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let early_mieMTIE := (mieReg.map (BitVec.extractLsb' 7 1 ·)) === 1#1
    let early_mieMSIE := (mieReg.map (BitVec.extractLsb' 3 1 ·)) === 1#1
    let early_privIsM := privMode === 3#2
    let early_privIsS := privMode === 1#2
    let early_privIsU := privMode === 0#2
    let early_mTimerNotDeleg := ((midelegReg.map (BitVec.extractLsb' 7 1 ·)) === 0#1)
    let early_mSwNotDeleg := ((midelegReg.map (BitVec.extractLsb' 3 1 ·)) === 0#1)
    let early_hiGt := Signal.ult mtimecmpHiReg mtimeHiReg
    let early_hiEq := mtimeHiReg === mtimecmpHiReg
    let early_loGe := ~~~(Signal.ult mtimeLoReg mtimecmpLoReg)
    let early_timerIrq := early_hiGt ||| (early_hiEq &&& early_loGe)
    let early_swIrq := (msipReg.map (BitVec.extractLsb' 0 1 ·)) === 1#1
    -- M-mode IRQ-enable predicates (proven in Trap/IRQEnable.lean)
    let early_timerIntEn :=
      Sparkle.IP.RV32.Trap.mTimerIntEnabledSignal
        early_privIsM early_mstatusMIE early_mieMTIE early_timerIrq early_mTimerNotDeleg
    let early_swIntEn :=
      Sparkle.IP.RV32.Trap.mSwIntEnabledSignal
        early_privIsM early_mstatusMIE early_mieMSIE early_swIrq early_mSwNotDeleg
    -- S-mode bit decoding from sip/sie
    let early_stipPending := (mipSoftReg.map (BitVec.extractLsb' 5 1 ·)) === 1#1
    let early_ssipPending := (mipSoftReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let early_seipPending := (mipSoftReg.map (BitVec.extractLsb' 9 1 ·)) === 1#1
    let early_sieSTIE := (sieReg.map (BitVec.extractLsb' 5 1 ·)) === 1#1
    let early_sieSSIE := (sieReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let early_sieSEIE := (sieReg.map (BitVec.extractLsb' 9 1 ·)) === 1#1
    -- S-mode IRQ-enable predicates (proven in Trap/IRQEnable.lean)
    let early_sTimerIntEn :=
      Sparkle.IP.RV32.Trap.sTimerIntEnabledSignal
        early_privIsS early_privIsU early_mstatusSIE early_sieSTIE early_stipPending
    let early_sSwIntEn :=
      Sparkle.IP.RV32.Trap.sSwIntEnabledSignal
        early_privIsS early_privIsU early_mstatusSIE early_sieSSIE early_ssipPending
    let early_sExtIntEn :=
      Sparkle.IP.RV32.Trap.sExtIntEnabledSignal
        early_privIsS early_privIsU early_mstatusSIE early_sieSEIE early_seipPending
    -- Full trap_taken, computed early (proven in Trap/TrapTaken.lean).
    let early_trap_taken :=
      Sparkle.IP.RV32.Trap.trapTakenSignal
        early_ifetchPageFault idex_isEcall early_pageFault
        early_timerIntEn early_swIntEn early_sTimerIntEn
        early_sSwIntEn early_sExtIntEn
    -- DRAM-side `validEX` for the byte_we gate.
    --
    -- We deliberately EXCLUDE `pendingWriteEn` from this gate even
    -- though the full `validEX` (computed below at ~line 1254 over
    -- `suppressEXWBSignal`) does include it. Reason: the AMO
    -- writeback is implemented by holding the write data/addr in
    -- `pending*Reg` and re-driving `final_byte_we |= pendingWriteEn`
    -- (lines 568..571). If we gate on full `validEX`, we'd drop the
    -- AMO writeback's own commit, which is the very write we want to
    -- allow when `pendingWriteEn=true`. So this DRAM gate covers the
    -- *spurious* suppressors only:
    --   * trap_taken    — async/sync trap fires this cycle
    --   * mmuBusy       — PTW in flight; redirect will re-execute
    --   * dMMURedirect  — MMU FSM completed; instruction re-fetches
    -- `dTLBMiss` is already in `dmem_we`'s own gate (line 518).
    let early_dramSuppress := early_trap_taken ||| mmuBusy ||| dMMURedirect
    let early_dramValid := ~~~early_dramSuppress

    -- 4 byte-wide memories (each 23-bit addr × 8-bit data).
    -- DRAM byte_we gated on `early_dramValid`. External firmware-loading
    -- writes (`dmemExtWriteEn`) bypass the gate because they happen
    -- before the pipeline starts.
    let dramWriteGate := early_dramValid ||| dmemExtWriteEn
    let actual_byte0_we := proto_byte0_we &&& dramWriteGate
    let actual_byte1_we := proto_byte1_we &&& dramWriteGate
    let actual_byte2_we := proto_byte2_we &&& dramWriteGate
    let actual_byte3_we := proto_byte3_we &&& dramWriteGate
    let byte0_rdata := Signal.memory actual_dmem_write_addr actual_byte0_wdata actual_byte0_we dmem_read_addr
    let byte1_rdata := Signal.memory actual_dmem_write_addr actual_byte1_wdata actual_byte1_we dmem_read_addr
    let byte2_rdata := Signal.memory actual_dmem_write_addr actual_byte2_wdata actual_byte2_we dmem_read_addr
    let byte3_rdata := Signal.memory actual_dmem_write_addr actual_byte3_wdata actual_byte3_we dmem_read_addr

    -- Reconstruct full word from 4 bytes: {byte3, byte2, byte1, byte0}
    let dmem_word_lo := byte1_rdata ++ byte0_rdata
    let dmem_word_hi := byte3_rdata ++ byte2_rdata
    let dmem_rdata := dmem_word_hi ++ dmem_word_lo

    let storeAddrHi := prevStoreAddr.map (BitVec.extractLsb' 2 30 ·)
    let loadAddrHi := exwb_physAddr.map (BitVec.extractLsb' 2 30 ·)
    let addrMatch := storeAddrHi === loadAddrHi
    let storeLoadMatch := prevStoreEn &&& addrMatch
    let dmemRdataFwd := Signal.mux storeLoadMatch prevStoreData dmem_rdata
    let clintOffset_wb := exwb_physAddr.map (BitVec.extractLsb' 0 16 ·)
    let msipMatch_wb     := clintOffset_wb === 0x0000#16
    let mtimeLoMatch_wb  := clintOffset_wb === 0xBFF8#16
    let mtimeHiMatch_wb  := clintOffset_wb === 0xBFFC#16
    let mtimecmpLoMatch_wb := clintOffset_wb === 0x4000#16
    let mtimecmpHiMatch_wb := clintOffset_wb === 0x4004#16
    let clintRdata :=
      Signal.mux msipMatch_wb msipReg
      (Signal.mux mtimecmpLoMatch_wb mtimecmpLoReg
      (Signal.mux mtimecmpHiMatch_wb mtimecmpHiReg
      (Signal.mux mtimeLoMatch_wb mtimeLoReg
      (Signal.mux mtimeHiMatch_wb mtimeHiReg
        (Signal.pure 0#32)))))
    let busAddrHi_wb := exwb_physAddr.map (BitVec.extractLsb' 16 16 ·)
    let isCLINT_wb := busAddrHi_wb === 0x0200#16
    let mmioAddrBit30_wb := exwb_physAddr.map (BitVec.extractLsb' 30 1 ·)
    let is_mmio_wb := mmioAddrBit30_wb === 1#1
    let mmioOffset_wb := exwb_physAddr.map (BitVec.extractLsb' 0 4 ·)
    let mmioIsStatus_wb := mmioOffset_wb === 0x0#4
    let mmioIsOutput_wb := mmioOffset_wb === 0x8#4
    -- Level-1a BitNet peripheral: the AI input register feeds a
    -- combinational BitNet (dim=4, 1 layer) whose output becomes the
    -- value read back from offset 0x8. Writes to offset 0x4 latch the
    -- input; BitNet settles in the same cycle; the following `lw`
    -- instruction sees the fresh result. See IP/RV32/BitNetPeripheral.lean.
    let bitnetOut :=
      Sparkle.IP.RV32.BitNetPeripheral.bitNetPeripheral aiInputReg
    let mmioRdata := Signal.mux mmioIsStatus_wb aiStatusReg
                       (Signal.mux mmioIsOutput_wb bitnetOut
                         (Signal.pure 0#32))
    -- UART 8250 read logic (WB stage)
    let isUART_wb := (exwb_physAddr.map (BitVec.extractLsb' 24 8 ·)) === 0x10#8
    let uartOffset_wb := exwb_physAddr.map (BitVec.extractLsb' 0 3 ·)
    let uartDLAB_wb := (uartLCRReg.map (BitVec.extractLsb' 7 1 ·)) === 1#1
    -- Read data per offset (zero-extended to 32 bits)
    let uartRd0 := Signal.mux uartDLAB_wb
      (0#24 ++ uartDLLReg)
      (Signal.pure 0#32)  -- RBR = 0 (no RX in Lean sim)
    let uartRd1 := Signal.mux uartDLAB_wb
      (0#24 ++ uartDLMReg)
      (0#24 ++ uartIERReg)
    let uartRd2 := Signal.pure 0x00000001#32  -- IIR: no interrupt pending
    let uartRd3 := 0#24 ++ uartLCRReg
    let uartRd4 := 0#24 ++ uartMCRReg
    let uartRd5 := Signal.pure 0x00000060#32  -- LSR: THRE + TEMT (TX always ready)
    let uartRd7 := 0#24 ++ uartSCRReg
    -- Mux by offset
    let wbOff0 := uartOffset_wb === 0#3
    let wbOff1 := uartOffset_wb === 1#3
    let wbOff2 := uartOffset_wb === 2#3
    let wbOff3 := uartOffset_wb === 3#3
    let wbOff4 := uartOffset_wb === 4#3
    let wbOff5 := uartOffset_wb === 5#3
    let wbOff7 := uartOffset_wb === 7#3
    let uartRdata := Signal.mux wbOff0 uartRd0
      (Signal.mux wbOff1 uartRd1
      (Signal.mux wbOff2 uartRd2
      (Signal.mux wbOff3 uartRd3
      (Signal.mux wbOff4 uartRd4
      (Signal.mux wbOff5 uartRd5
      (Signal.mux wbOff7 uartRd7
        (Signal.pure 0#32)))))))

    -- Sub-word load extraction: select byte/halfword from bus read data
    let busRdataRaw := Signal.mux isCLINT_wb clintRdata
                         (Signal.mux isUART_wb uartRdata
                         (Signal.mux is_mmio_wb mmioRdata dmemRdataFwd))
    -- Byte / half select (proven in Bus/LoadWidth.lean).
    let loadByteOff := exwb_physAddr.map (BitVec.extractLsb' 0 2 ·)
    let loadByteOff0 := loadByteOff === 0#2
    let loadByteOff1 := loadByteOff === 1#2
    let loadByteOff2 := loadByteOff === 2#2
    let selByte :=
      Sparkle.IP.RV32.Bus.selByteSignal loadByteOff0 loadByteOff1 loadByteOff2 busRdataRaw
    let loadAddrBit1 := exwb_physAddr.map (BitVec.extractLsb' 1 1 ·)
    let isHalfLow := loadAddrBit1 === 0#1
    let selHalf := Sparkle.IP.RV32.Bus.selHalfSignal isHalfLow busRdataRaw
    -- Sign/zero extend byte
    let byteSgnBit := selByte.map (BitVec.extractLsb' 7 1 ·)
    let byteIsSgn := byteSgnBit === 1#1
    let byteSignExt := Signal.mux byteIsSgn (Signal.pure 0xFFFFFF#24) (Signal.pure 0#24)
    let byteSext := byteSignExt ++ selByte
    let byteZext := 0#24 ++ selByte
    -- Sign/zero extend halfword
    let halfSgnBit := selHalf.map (BitVec.extractLsb' 15 1 ·)
    let halfIsSgn := halfSgnBit === 1#1
    let halfSignExt := Signal.mux halfIsSgn (Signal.pure 0xFFFF#16) (Signal.pure 0#16)
    let halfSext := halfSignExt ++ selHalf
    let halfZext := 0#16 ++ selHalf
    -- Select based on exwb_funct3: 000=LB, 001=LH, 010=LW, 100=LBU, 101=LHU
    -- Only apply sub-word extraction for actual loads (exwb_m2r = true)
    let f3isLB  := exwb_funct3 === 0#3
    let f3isLH  := exwb_funct3 === 1#3
    let f3isLBU := exwb_funct3 === 4#3
    let f3isLHU := exwb_funct3 === 5#3
    -- 5-way load extractor (proven in Bus/LoadWidth.lean).
    let loadExtracted :=
      Sparkle.IP.RV32.Bus.loadExtractSignal
        f3isLB f3isLH f3isLBU f3isLHU
        byteSext byteZext halfSext halfZext busRdataRaw
    -- Gate: only use extracted value for DMEM loads; peripheral reads bypass sub-word extraction
    let isDMEM_wb := (~~~isCLINT_wb) &&& ((~~~isUART_wb) &&& (~~~is_mmio_wb))
    let busRdata := Signal.mux exwb_m2r
      (Signal.mux isDMEM_wb loadExtracted busRdataRaw) busRdataRaw

    -- A-ext WB stage: classify AMO type in WB
    let exwb_isLR := exwb_isAMO &&& (exwb_amoOp === 0b00010#5)
    let exwb_isSC := exwb_isAMO &&& (exwb_amoOp === 0b00011#5)
    let exwb_isAMOrw := exwb_isAMO &&& (~~~(exwb_isLR ||| exwb_isSC))

    -- AMO new value computation (Signal-level mux chain, synthesizable)
    -- busRdataRaw = old value at AMO's address (read 1 cycle ago)
    -- prevStoreData = AMO's rs2 (captured when AMO was in EX)
    let amoNewVal := amoComputeSignal exwb_amoOp busRdataRaw prevStoreData

    -- Pending write next values (set when non-LR/SC AMO is in WB)
    -- Bug fix: use exwb_physAddr (MMU-translated PA), not exwb_alu (virtual addr).
    -- AMO writeback was previously writing to the virtual address as if it were
    -- physical, dropping all atomic stores under Sv32 paging (the kernel's
    -- atomic_long_add etc. were lost, causing nr_free_pages=0 at boot).
    let pendingWriteEnNext := exwb_isAMOrw
    let pendingWriteAddrNext := Signal.mux exwb_isAMOrw exwb_physAddr pendingWriteAddr
    let pendingWriteDataNext := Signal.mux exwb_isAMOrw amoNewVal pendingWriteData

    -- SC.W: succeeds iff reservation is valid and matches target PA. Per
    -- RISC-V spec, traps (and other context switches) must invalidate the
    -- reservation; this is implemented in resValidNext below.
    let scAddrMatch := exwb_physAddr === reservationAddr
    let scSucceeds  := reservationValid &&& scAddrMatch
    -- Final WB-stage result (proven in Pipeline/Writeback.lean): 5-way priority
    -- SC > CSR > jump > load > ALU.
    let wb_result :=
      Sparkle.IP.RV32.Pipeline.wbResultSignal
        exwb_isSC scSucceeds
        exwb_isCsr exwb_csrRdata
        exwb_jump exwb_pc4
        exwb_m2r busRdata
        exwb_alu
    let wb_data := wb_result

    let ex_rs1 := Signal.mux fwd_rs1_match wb_data idex_rs1Val
    let ex_rs2 := Signal.mux fwd_rs2_match wb_data idex_rs2Val
    let alu_a := Signal.mux idex_auipc idex_pc ex_rs1
    let alu_b := Signal.mux idex_aluSrcB idex_imm ex_rs2
    let alu_result_raw := aluSignal idex_aluOp alu_a alu_b
    -- M-extension: MUL (1-cycle) uses synthesizable 64-bit multiply
    let mulResult := mulComputeSignal idex_funct3 ex_rs1 ex_rs2
    let isDivOp := (idex_funct3.map (BitVec.extractLsb' 2 1 ·)) === 1#1
    let branchCond := branchCompSignal idex_funct3 ex_rs1 ex_rs2
    let branchTaken := idex_branch &&& branchCond
    -- jumpTarget (proven in Pipeline/PCNext.lean): JALR clears bit 0.
    let jumpTarget :=
      Sparkle.IP.RV32.Pipeline.jumpTargetSignal idex_isJalr idex_pc ex_rs1 idex_imm

    let hiGt := Signal.ult mtimecmpHiReg mtimeHiReg
    let hiEq := mtimeHiReg === mtimecmpHiReg
    let loGe := ~~~(Signal.ult mtimeLoReg mtimecmpLoReg)
    let timerIrq := hiGt ||| (hiEq &&& loGe)
    let swIrq := (msipReg.map (BitVec.extractLsb' 0 1 ·)) === 1#1
    let mipTimerBit := Signal.mux timerIrq (Signal.pure 0x00000080#32) (Signal.pure 0#32)
    let mipSwBit := Signal.mux swIrq (Signal.pure 0x00000008#32) (Signal.pure 0#32)
    -- mipValue combines hardware bits (MTIP=7, MSIP=3) with software-writable
    -- S-mode pending bits (SSIP=1, STIP=5, SEIP=9) from `mipSoftReg`.
    let mipSoftMask : Signal dom (BitVec 32) := Signal.pure 0x00000222#32
    let mipValue := mipTimerBit ||| mipSwBit ||| (mipSoftReg &&& mipSoftMask)
    -- CSR address matching (M-mode)
    let csrIsMstatus  := idex_csrAddr === 0x300#12
    let csrIsMie      := idex_csrAddr === 0x304#12
    let csrIsMtvec    := idex_csrAddr === 0x305#12
    let csrIsMscratch := idex_csrAddr === 0x340#12
    let csrIsMepc     := idex_csrAddr === 0x341#12
    let csrIsMcause   := idex_csrAddr === 0x342#12
    let csrIsMtval    := idex_csrAddr === 0x343#12
    let csrIsMip      := idex_csrAddr === 0x344#12
    let csrIsMisa     := idex_csrAddr === 0x301#12
    let csrIsMhartid  := idex_csrAddr === 0xF14#12
    -- CSR address matching (S-mode)
    let csrIsSstatus  := idex_csrAddr === 0x100#12
    let csrIsSie      := idex_csrAddr === 0x104#12
    let csrIsStvec    := idex_csrAddr === 0x105#12
    let csrIsSscratch := idex_csrAddr === 0x140#12
    let csrIsSepc     := idex_csrAddr === 0x141#12
    let csrIsScause   := idex_csrAddr === 0x142#12
    let csrIsStval    := idex_csrAddr === 0x143#12
    let csrIsSip      := idex_csrAddr === 0x144#12
    let csrIsSatp     := idex_csrAddr === 0x180#12
    -- CSR address matching (delegation)
    let csrIsMedeleg  := idex_csrAddr === 0x302#12
    let csrIsMideleg  := idex_csrAddr === 0x303#12
    -- CSR address matching (counter enable)
    let csrIsMcounteren := idex_csrAddr === 0x306#12
    let csrIsScounteren := idex_csrAddr === 0x106#12
    -- Counter CSRs (read-only by S/U-mode if mcounteren/scounteren permits)
    let csrIsTime     := idex_csrAddr === 0xC01#12
    let csrIsTimeh    := idex_csrAddr === 0xC81#12
    let csrIsCycle    := idex_csrAddr === 0xC00#12
    let csrIsCycleh   := idex_csrAddr === 0xC80#12

    -- PMP CSR range detection (0x3A0-0x3EF): return 0, silently ignore writes
    let csrAddrHi := idex_csrAddr.map (BitVec.extractLsb' 4 8 ·)  -- bits [11:4]
    let csrIsPmp :=
      (csrAddrHi === 0x3A#8) |||
      (csrAddrHi === 0x3B#8) |||
      (csrAddrHi === 0x3C#8) |||
      (csrAddrHi === 0x3D#8) |||
      (csrAddrHi === 0x3E#8)

    -- SSTATUS: masked view of mstatus (bits SIE/SPIE/SPP/SUM/MXR)
    let sstatusMask : Signal dom (BitVec 32) := Signal.pure 0x000C0122#32
    let sstatusView := mstatusReg &&& sstatusMask

    -- CSR read mux (expanded with S-mode CSRs)
    let csr_rdata :=
      Signal.mux csrIsMstatus mstatusReg
      (Signal.mux csrIsMie mieReg
      (Signal.mux csrIsMtvec mtvecReg
      (Signal.mux csrIsMscratch mscratchReg
      (Signal.mux csrIsMepc mepcReg
      (Signal.mux csrIsMcause mcauseReg
      (Signal.mux csrIsMtval mtvalReg
      (Signal.mux csrIsMip mipValue
      (Signal.mux csrIsMisa (Signal.pure 0x40141101#32)
      (Signal.mux csrIsMhartid (Signal.pure 0#32)
      (Signal.mux csrIsMedeleg medelegReg
      (Signal.mux csrIsMideleg midelegReg
      (Signal.mux csrIsSstatus sstatusView
      (Signal.mux csrIsSie sieReg
      (Signal.mux csrIsStvec stvecReg
      (Signal.mux csrIsSscratch sscratchReg
      (Signal.mux csrIsSepc sepcReg
      (Signal.mux csrIsScause scauseReg
      (Signal.mux csrIsStval stvalReg
      (Signal.mux csrIsSip (mipValue &&& mipSoftMask)
      (Signal.mux csrIsSatp satpReg
      (Signal.mux csrIsMcounteren mcounterenReg
      (Signal.mux csrIsScounteren scounterenReg
      (Signal.mux csrIsTime mtimeLoReg     -- time CSR (0xC01) = mtime[31:0]
      (Signal.mux csrIsTimeh mtimeHiReg    -- timeh CSR (0xC81) = mtime[63:32]
      (Signal.mux csrIsCycle mtimeLoReg    -- cycle CSR (0xC00) ≈ mtime
      (Signal.mux csrIsCycleh mtimeHiReg   -- cycleh CSR (0xC80) ≈ mtime hi
      (Signal.mux csrIsPmp (Signal.pure 0#32)         -- PMP: return 0
        (Signal.pure 0#32))))))))))))))))))))))))))))

    -- Interrupt enable flags
    let mstatusMIE_flag := (mstatusReg.map (BitVec.extractLsb' 3 1 ·)) === 1#1
    let mstatusMPIE_flag := (mstatusReg.map (BitVec.extractLsb' 7 1 ·)) === 1#1
    let mstatusSIE_flag := (mstatusReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let mstatusSPIE_flag := (mstatusReg.map (BitVec.extractLsb' 5 1 ·)) === 1#1
    let mieMTIE_flag := (mieReg.map (BitVec.extractLsb' 7 1 ·)) === 1#1
    let mieMSIE_flag := (mieReg.map (BitVec.extractLsb' 3 1 ·)) === 1#1
    -- M-mode interrupt fires when: (priv==M && mstatus.MIE && mie.bit && pending),
    -- OR when priv<M && mie.bit && pending (regardless of mstatus.MIE), provided
    -- the interrupt is NOT delegated to S-mode (mideleg bit clear). If delegated,
    -- it's handled in S-mode by the S-mode interrupt path below.
    let privIsM_pre := privMode === 3#2
    let mTimerNotDelegated := ((midelegReg.map (BitVec.extractLsb' 7 1 ·)) === 0#1)
    let mSwNotDelegated := ((midelegReg.map (BitVec.extractLsb' 3 1 ·)) === 0#1)
    -- M-mode IRQ-enable predicates (proven in Trap/IRQEnable.lean).
    -- Spec: fires iff ((priv=M ∧ MIE) ∨ priv<M) ∧ mie.bit ∧ pending ∧ ¬delegated.
    let timerIntEnabled :=
      Sparkle.IP.RV32.Trap.mTimerIntEnabledSignal
        privIsM_pre mstatusMIE_flag mieMTIE_flag timerIrq mTimerNotDelegated
    let swIntEnabled :=
      Sparkle.IP.RV32.Trap.mSwIntEnabledSignal
        privIsM_pre mstatusMIE_flag mieMSIE_flag swIrq mSwNotDelegated
    -- S-mode bit decoding from sip/sie + privilege flags
    let privIsU0 := privMode === 0#2
    let privIsS0 := privMode === 1#2
    let stipPending := (mipSoftReg.map (BitVec.extractLsb' 5 1 ·)) === 1#1
    let ssipPending := (mipSoftReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let seipPending := (mipSoftReg.map (BitVec.extractLsb' 9 1 ·)) === 1#1
    let sieSTIE_flag := (sieReg.map (BitVec.extractLsb' 5 1 ·)) === 1#1
    let sieSSIE_flag := (sieReg.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let sieSEIE_flag := (sieReg.map (BitVec.extractLsb' 9 1 ·)) === 1#1
    -- S-mode IRQ-enable predicates (proven in Trap/IRQEnable.lean).
    -- Spec: fires iff ((priv=S ∧ SIE) ∨ priv=U) ∧ sie.bit ∧ mip.soft.bit.
    -- Delegation is enforced separately in Trap/Delegation.lean.
    let sTimerIntEnabled :=
      Sparkle.IP.RV32.Trap.sTimerIntEnabledSignal
        privIsS0 privIsU0 mstatusSIE_flag sieSTIE_flag stipPending
    let sSwIntEnabled :=
      Sparkle.IP.RV32.Trap.sSwIntEnabledSignal
        privIsS0 privIsU0 mstatusSIE_flag sieSSIE_flag ssipPending
    let sExtIntEnabled :=
      Sparkle.IP.RV32.Trap.sExtIntEnabledSignal
        privIsS0 privIsU0 mstatusSIE_flag sieSEIE_flag seipPending

    -- ECALL cause depends on privilege level (proven in Trap/Cause.lean).
    let privIsU := privMode === 0#2
    let privIsS := privMode === 1#2
    let ecallCause := Sparkle.IP.RV32.Trap.ecallCauseSignal privIsU privIsS

    -- Page fault from MMU FAULT state (D-side: load=13, store=15)
    let pageFault := isMMUFault &&& (~~~bypassMMU)
    let isStoreFault := pageFault &&& dMissIsStore
    let pageFaultCause := Sparkle.IP.RV32.Trap.pageFaultCauseSignal isStoreFault

    -- I-side page fault: PTW completed with fault for instruction fetch
    let ifetchPageFault := ifetchFaultPending &&& (~~~bypassMMU)

    -- trap_taken disjunction (proven in Trap/TrapTaken.lean).
    let trap_taken :=
      Sparkle.IP.RV32.Trap.trapTakenSignal
        ifetchPageFault idex_isEcall pageFault
        timerIntEnabled swIntEnabled sTimerIntEnabled sSwIntEnabled sExtIntEnabled
    -- Cause priority (per priv spec, proven in Trap/Cause.lean):
    -- ifetchPF > ecall > pageFault > MTI > MSI > SEI > SSI > STI.
    -- (MEI omitted: our SoC has no external M-mode IRQ.)
    let trapCause :=
      Sparkle.IP.RV32.Trap.trapCauseSignal
        ifetchPageFault
        idex_isEcall ecallCause
        pageFault pageFaultCause
        timerIntEnabled swIntEnabled sExtIntEnabled sSwIntEnabled sTimerIntEnabled

    -- Trap delegation: check medeleg/mideleg bits
    let isInterrupt := (trapCause.map (BitVec.extractLsb' 31 1 ·)) === 1#1
    let causeIdx := trapCause.map (BitVec.extractLsb' 0 5 ·)
    let causeIdxExt := 0#27 ++ causeIdx
    let medelegShifted := medelegReg >>> causeIdxExt
    let medelegBit := (medelegShifted.map (BitVec.extractLsb' 0 1 ·)) === 1#1
    let midelegShifted := midelegReg >>> causeIdxExt
    let midelegBit := (midelegShifted.map (BitVec.extractLsb' 0 1 ·)) === 1#1
    let delegated := Signal.mux isInterrupt midelegBit medelegBit
    -- Trap destination decoder: see `IP.RV32.Trap.Delegation`.
    -- Pure versions `trapToSPure`/`trapToMPure` and Signal-level
    -- versions are equivalent (theorems `trapToSSignal_eq_pure`,
    -- `trapToMSignal_eq_pure`). The Signal API is split into two
    -- functions because the synthesis backend does not handle Prod
    -- return types.
    let privGtS := Signal.ult (Signal.pure 1#2) privMode
    let privLeS := ~~~privGtS
    let trapToS :=
      Sparkle.IP.RV32.Trap.trapToSSignal trap_taken delegated privLeS
    let trapToM :=
      Sparkle.IP.RV32.Trap.trapToMSignal trap_taken delegated privLeS

    -- Trap target: S-mode or M-mode tvec
    let mtvecBase := mtvecReg &&& 0xFFFFFFFC#32
    let stvecBase := stvecReg &&& 0xFFFFFFFC#32
    let trap_target := Signal.mux trapToS stvecBase mtvecBase
    let mret_target := mepcReg
    let sret_target := sepcReg

    -- MPP and SPP for privilege mode transitions
    let mpp := mstatusReg.map (BitVec.extractLsb' 11 2 ·)
    let sppBit := mstatusReg.map (BitVec.extractLsb' 8 1 ·)
    let sretPriv := 0#1 ++ sppBit

    let flush := branchTaken ||| idex_jump ||| trap_taken ||| idex_isMret |||
                 idex_isSret ||| idex_isSFenceVMA ||| dMMURedirect
    let flushOrDelay := flush ||| flushDelay

    -- M-extension: DIV/REM (multi-cycle) uses restoring divider circuit
    let divWanted := idex_isMext &&& isDivOp
    let divIsSigned := ~~~((idex_funct3.map (BitVec.extractLsb' 0 1 ·)) === 1#1)
    let divIsRem := (idex_funct3.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let divAbort := flushOrDelay
    let divStart := divWanted &&& (~~~divPending)
    let divResultDone := Divider.dividerSignal ex_rs1 ex_rs2 divStart divIsSigned divIsRem divAbort
    let divResult := projN! divResultDone 2 0
    let divDone := projN! divResultDone 2 1
    -- Stall when DIV/REM wanted and result not yet valid
    -- (divPending && divDone) = true only on the done cycle → un-stall
    let divStall := divWanted &&& (~~~(divPending &&& divDone))
    -- M-extension result: MUL (immediate) or DIV/REM (multi-cycle)
    let mextResult := Signal.mux isDivOp divResult mulResult
    let alu_result := Signal.mux idex_isMext mextResult alu_result_raw

    let id_opcode := ifid_inst.map (BitVec.extractLsb' 0 7 ·)
    let id_rd     := ifid_inst.map (BitVec.extractLsb' 7 5 ·)
    let id_funct3 := ifid_inst.map (BitVec.extractLsb' 12 3 ·)
    let id_rs1    := ifid_inst.map (BitVec.extractLsb' 15 5 ·)
    let id_rs2    := ifid_inst.map (BitVec.extractLsb' 20 5 ·)
    let id_funct7 := ifid_inst.map (BitVec.extractLsb' 25 7 ·)
    let id_imm := immGenSignal ifid_inst id_opcode
    let id_aluOp := aluControlSignal id_opcode id_funct3 id_funct7
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
    let id_aluSrcB := ((id_isALUimm ||| id_isLoad) ||| (id_isStore ||| id_isLUI)) |||
                      ((id_isAUIPC ||| id_isJAL) ||| id_isJALR)
    let f3isZero := id_funct3 === 0#3
    let f3notZero := ~~~f3isZero
    let id_isCsr := id_isSystem &&& f3notZero
    let id_regWrite := ((id_isALUrr ||| id_isALUimm) ||| (id_isLoad ||| id_isLUI)) |||
                       ((id_isAUIPC ||| id_isJAL) ||| (id_isJALR ||| id_isCsr))
    let id_memRead  := id_isLoad
    let id_memWrite := id_isStore
    let id_memToReg := id_isLoad
    let id_jump     := id_isJAL ||| id_isJALR
    let id_auipc    := id_isAUIPC ||| id_isJAL
    let ecallField := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let isEcallField := ecallField === 0x000#12
    let id_isEcall := (id_isSystem &&& f3isZero) &&& isEcallField
    let id_csrAddr := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let mretField := ifid_inst.map (BitVec.extractLsb' 20 12 ·)
    let isMretField := mretField === 0x302#12
    let id_isMret := (id_isSystem &&& f3isZero) &&& isMretField
    -- SRET: funct12 = 0x102 (SYSTEM opcode, funct3 = 0)
    let isSretField := (ifid_inst.map (BitVec.extractLsb' 20 12 ·)) === 0x102#12
    let id_isSret := (id_isSystem &&& f3isZero) &&& isSretField
    -- SFENCE.VMA: funct7 = 0b0001001, funct3 = 0, SYSTEM opcode
    let id_isSFenceVMA := (id_isSystem &&& f3isZero) &&& (id_funct7 === 0b0001001#7)
    -- M-extension: R-type with funct7 = 0000001
    let id_isMext := id_isALUrr &&& (id_funct7 === 0b0000001#7)
    -- A-extension: opcode = 0101111
    let id_isAMO := id_opcode === 0b0101111#7
    let id_amoOp := ifid_inst.map (BitVec.extractLsb' 27 5 ·)  -- funct7[6:2]
    let id_isLR := id_isAMO &&& (id_amoOp === 0b00010#5)
    let id_isSC := id_isAMO &&& (id_amoOp === 0b00011#5)
    let id_isAMOrw := id_isAMO &&& (~~~(id_isLR ||| id_isSC))
    -- AMO control: LR=load, SC=store+regwrite, AMOrw=load+regwrite (delayed write)
    let id_regWrite := id_regWrite ||| id_isAMO
    let id_memRead  := id_memRead ||| (id_isLR ||| id_isAMOrw)
    let id_memToReg := id_memToReg ||| (id_isLR ||| id_isAMOrw)
    let id_memWrite := id_memWrite ||| id_isSC
    let id_aluSrcB  := id_aluSrcB ||| id_isAMO  -- use imm=0 for address
    -- Force immediate to 0 for AMO (R-type has no immediate field)
    let id_imm := Signal.mux id_isAMO (Signal.pure 0#32) id_imm

    -- AMO stall: non-LR/SC AMOs need a bubble for delayed write
    let idex_isLR := idex_isAMO &&& (idex_amoOp === 0b00010#5)
    let idex_isSC := idex_isAMO &&& (idex_amoOp === 0b00011#5)
    let idex_isAMOrw := idex_isAMO &&& (~~~(idex_isLR ||| idex_isSC))

    -- =========================================================================
    -- I-side TLB lookup (shared TLB entries, for instruction fetch translation)
    -- =========================================================================
    let iVPN := fetchPC.map (BitVec.extractLsb' 12 20 ·)

    -- iTLB hit logic: reuse same TLB entries as D-side
    let itlb0FullMatch := tlb0VPN === iVPN
    let itlb0MegaMatch := (tlb0VPN.map (BitVec.extractLsb' 10 10 ·)) === (iVPN.map (BitVec.extractLsb' 10 10 ·))
    let itlb0VPNMatch := Signal.mux tlb0Mega itlb0MegaMatch itlb0FullMatch
    let itlb0Hit := tlb0Valid &&& itlb0VPNMatch

    let itlb1FullMatch := tlb1VPN === iVPN
    let itlb1MegaMatch := (tlb1VPN.map (BitVec.extractLsb' 10 10 ·)) === (iVPN.map (BitVec.extractLsb' 10 10 ·))
    let itlb1VPNMatch := Signal.mux tlb1Mega itlb1MegaMatch itlb1FullMatch
    let itlb1Hit := tlb1Valid &&& itlb1VPNMatch

    let itlb2FullMatch := tlb2VPN === iVPN
    let itlb2MegaMatch := (tlb2VPN.map (BitVec.extractLsb' 10 10 ·)) === (iVPN.map (BitVec.extractLsb' 10 10 ·))
    let itlb2VPNMatch := Signal.mux tlb2Mega itlb2MegaMatch itlb2FullMatch
    let itlb2Hit := tlb2Valid &&& itlb2VPNMatch

    let itlb3FullMatch := tlb3VPN === iVPN
    let itlb3MegaMatch := (tlb3VPN.map (BitVec.extractLsb' 10 10 ·)) === (iVPN.map (BitVec.extractLsb' 10 10 ·))
    let itlb3VPNMatch := Signal.mux tlb3Mega itlb3MegaMatch itlb3FullMatch
    let itlb3Hit := tlb3Valid &&& itlb3VPNMatch

    let anyITLBHit := (itlb0Hit ||| itlb1Hit) ||| (itlb2Hit ||| itlb3Hit)

    -- iTLB output PPN (priority mux)
    let itlbPPN := Signal.mux itlb0Hit tlb0PPN
      (Signal.mux itlb1Hit tlb1PPN
      (Signal.mux itlb2Hit tlb2PPN
      (Signal.mux itlb3Hit tlb3PPN
        (Signal.pure 0#22))))

    -- iTLB megapage flag (priority mux)
    let itlbMega := Signal.mux itlb0Hit tlb0Mega
      (Signal.mux itlb1Hit tlb1Mega
      (Signal.mux itlb2Hit tlb2Mega
      (Signal.mux itlb3Hit tlb3Mega
        (Signal.pure false))))

    -- I-side physical address from iTLB.
    -- Sv32 page formats (RISC-V Privileged spec, Sv32 §10.3.2):
    --   Megapage (4 MB):  PA[31:22] = PTE.PPN[1]   (= PPN bits [21:10])
    --                     PA[21:0]  = VA[21:0]
    --                     (PTE.PPN[0] must be zero — superpage alignment)
    --   4K page:          PA[31:12] = PTE.PPN      (lower 20 bits used in 32-bit PA)
    --                     PA[11:0]  = VA[11:0]
    -- Earlier code reused the 4K formula for megapage, which produced
    -- a misaligned PA and trapped Linux at the very first kernel
    -- instruction after MMU bring-up. See itlb fault chain in
    -- IP/RV32/JITDebug-instrumented logs.
    let itlbPPN_20 := itlbPPN.map (BitVec.extractLsb' 0 20 ·)
    let itlbPPN_hi10 := itlbPPN.map (BitVec.extractLsb' 10 10 ·)
    let fetchPCLow22 := fetchPC.map (BitVec.extractLsb' 0 22 ·)
    let fetchPCLow12 := fetchPC.map (BitVec.extractLsb' 0 12 ·)
    let ifetchPhysAddrMega := itlbPPN_hi10 ++ fetchPCLow22
    let ifetchPhysAddrReg := itlbPPN_20 ++ fetchPCLow12
    let ifetchPhysAddr := Signal.mux itlbMega ifetchPhysAddrMega ifetchPhysAddrReg

    -- Need to translate instruction fetch? (S/U-mode with MMU enabled, DRAM region)
    let needTranslateI := satpMode &&& ((~~~isMmode) &&& ((fetchPC.map (BitVec.extractLsb' 31 1 ·)) === 1#1))
    let ifetchTranslated := needTranslateI &&& anyITLBHit
    let ifetchTLBMiss := needTranslateI &&& (~~~anyITLBHit)

    -- I-side stall on TLB miss (until PTW fills the entry)
    let ifetchStall := ifetchTLBMiss &&& (~~~ifetchFaultPending)

    let stall := ((hazardSignal idex_memRead idex_rd id_rs1 id_rs2) ||| mmuStall) |||
                   ((idex_isAMOrw ||| pendingWriteEn) ||| (divStall ||| ifetchStall))

    let rf_rs1_addr := Signal.mux stall id_rs1
                         (ifid_inst.map (BitVec.extractLsb' 15 5 ·))
    let rf_rs2_addr := Signal.mux stall id_rs2
                         (ifid_inst.map (BitVec.extractLsb' 20 5 ·))
    -- Register file uses combinational reads (same-cycle readAddr)
    -- so that rf_rs1_raw.val t reads the register addressed by rf_rs1_addr.val t,
    -- not rf_rs1_addr.val (t-1) as Signal.memory would.
    let rf_rs1_raw := Signal.memoryComboRead wb_addr wb_data wb_en rf_rs1_addr
    let rf_rs2_raw := Signal.memoryComboRead wb_addr wb_data wb_en rf_rs2_addr
    let wb_fwd_rs1 := wb_en &&& (wb_addr === id_rs1)
    let wb_fwd_rs2 := wb_en &&& (wb_addr === id_rs2)
    let prev_fwd_rs1 := prev_wb_en &&& (prev_wb_addr === id_rs1)
    let prev_fwd_rs2 := prev_wb_en &&& (prev_wb_addr === id_rs2)
    let rf_rs1_bypassed := Signal.mux wb_fwd_rs1 wb_data
                             (Signal.mux prev_fwd_rs1 prev_wb_data rf_rs1_raw)
    let rf_rs2_bypassed := Signal.mux wb_fwd_rs2 wb_data
                             (Signal.mux prev_fwd_rs2 prev_wb_data rf_rs2_raw)
    let id_rs1Val := Signal.mux (id_rs1 === 0#5)
                       (Signal.pure 0#32) rf_rs1_bypassed
    let id_rs2Val := Signal.mux (id_rs2 === 0#5)
                       (Signal.pure 0#32) rf_rs2_bypassed

    let pcPlus4 := pcReg + 4#32
    let fetchPCPlus4 := fetchPC + 4#32
    -- DRAM instruction fetch: 4 combo-read instances sharing DMEM write signals
    -- Use translated physical address when iTLB hit, else raw fetchPC
    let ifetch_word_addr := Signal.mux ifetchTranslated
      (ifetchPhysAddr.map (BitVec.extractLsb' 2 23 ·))
      (fetchPC.map (BitVec.extractLsb' 2 23 ·))
    let dram_ifetch_b0 := Signal.memoryComboRead actual_dmem_write_addr actual_byte0_wdata actual_byte0_we ifetch_word_addr
    let dram_ifetch_b1 := Signal.memoryComboRead actual_dmem_write_addr actual_byte1_wdata actual_byte1_we ifetch_word_addr
    let dram_ifetch_b2 := Signal.memoryComboRead actual_dmem_write_addr actual_byte2_wdata actual_byte2_we ifetch_word_addr
    let dram_ifetch_b3 := Signal.memoryComboRead actual_dmem_write_addr actual_byte3_wdata actual_byte3_we ifetch_word_addr
    let dram_ifetch_lo := dram_ifetch_b1 ++ dram_ifetch_b0
    let dram_ifetch_hi := dram_ifetch_b3 ++ dram_ifetch_b2
    let dram_ifetch_word := dram_ifetch_hi ++ dram_ifetch_lo
    -- Instruction source mux: DRAM if fetch address is in DRAM range, else firmware IMEM
    -- DRAM range: addresses >= 0x80000000 (bit 31 = 1)
    let fetchInDRAM := Signal.mux ifetchTranslated
      ((ifetchPhysAddr.map (BitVec.extractLsb' 31 1 ·)) === 1#1)
      ((fetchPC.map (BitVec.extractLsb' 31 1 ·)) === 1#1)
    let final_imem_rdata := Signal.mux fetchInDRAM dram_ifetch_word imem_rdata

    -- Bug fix (idex-double-latch on ifetchStall release): also NOP IFID
    -- during stallDelay so the duplicate fetch doesn't propagate. The
    -- stalled-cycle fetch and the post-stall-cycle fetch both return the
    -- same IMEM word (because fetchPC lags pcReg by one cycle on release);
    -- both would otherwise enter IFID and IDEX as separate but identical
    -- instructions. NOP-ing IFID at stallDelay drops the second copy.
    let ifid_inst_in := Signal.mux (flushOrDelay ||| stallDelay) (Signal.pure nopInst)
                          (Signal.mux stall ifid_inst final_imem_rdata)
    let ifid_pc_in := Signal.mux stall ifid_pc fetchPC
    let ifid_pc4_in := Signal.mux stall ifid_pc4 fetchPCPlus4
    -- Pipeline EX/WB suppression: see `IP.RV32.Pipeline.SuppressEXWB`.
    -- Pure versions `holdEXPure`, `suppressEXWBPure`, `validEXPure`
    -- are equivalent to the Signal-level versions (theorems
    -- `*Signal_eq_pure`); proven invariants:
    --   * each of trap_taken, dTLBMiss, pendingWriteEn, mmuBusy,
    --     dMMURedirect individually suppresses EX/WB.
    --   * validEX = ¬suppressEXWB; true iff all five are clear.
    let holdEX :=
      Sparkle.IP.RV32.Pipeline.holdEXSignal pendingWriteEn mmuBusy
    -- freezeIDEX: freeze ID/EX and EX/WB pipeline regs during pending write OR division
    let freezeIDEX := holdEX ||| (divStall &&& (~~~flushOrDelay))
    let suppressEXWB :=
      Sparkle.IP.RV32.Pipeline.suppressEXWBSignal
        trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
    let validEX :=
      Sparkle.IP.RV32.Pipeline.validEXSignal
        trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
    let idex_isCsr_valid := idex_isCsr &&& validEX
    -- Bug fix (idex-double-latch on ifetchStall release): when ifetchStall
    -- transitions from 1→0, fetchPC lags pcReg by one extra cycle, causing
    -- IFID to hold the same instruction for two cycles, propagating into
    -- IDEX twice. Adding `stallDelay` (= prev-cycle's ifetchStall) to
    -- squash NOPs out the duplicate. We only gate on ifetchStall (not
    -- general stall) because load-use data-hazard stalls don't have this
    -- issue — they don't desync fetchPC from pcReg.
    let squash := (stall &&& (~~~freezeIDEX)) ||| flushOrDelay ||| stallDelay

    let clintOffset := alu_result_approx.map (BitVec.extractLsb' 0 16 ·)
    let clintWE := idex_memWrite &&& (isCLINT_ex &&& validEX)
    let msipMatch     := clintOffset === 0x0000#16
    let mtimeLoMatch  := clintOffset === 0xBFF8#16
    let mtimeHiMatch  := clintOffset === 0xBFFC#16
    let mtimecmpLoMatch := clintOffset === 0x4000#16
    let mtimecmpHiMatch := clintOffset === 0x4004#16
    let mtimeLoInc := mtimeLoReg + 1#32
    let mtimeCarry := mtimeLoInc === 0#32
    let mtimeHiInc := Signal.mux mtimeCarry
                        (mtimeHiReg + 1#32) mtimeHiReg
    let msipNext := Signal.mux (clintWE &&& msipMatch)
                      ex_rs2_approx msipReg
    let mtimeLoNext := Signal.mux (clintWE &&& mtimeLoMatch)
                         ex_rs2_approx mtimeLoInc
    let mtimeHiNext := Signal.mux (clintWE &&& mtimeHiMatch)
                         ex_rs2_approx mtimeHiInc
    let mtimecmpLoNext := Signal.mux (clintWE &&& mtimecmpLoMatch)
                            ex_rs2_approx mtimecmpLoReg
    let mtimecmpHiNext := Signal.mux (clintWE &&& mtimecmpHiMatch)
                            ex_rs2_approx mtimecmpHiReg

    let mmioWE := idex_memWrite &&& (is_mmio_ex &&& validEX)
    let mmioOffset_ex := alu_result_approx.map (BitVec.extractLsb' 0 4 ·)
    let mmioIsStatus_ex := mmioOffset_ex === 0x0#4
    let mmioIsInput_ex  := mmioOffset_ex === 0x4#4
    let aiStatusNext := Signal.mux (mmioWE &&& mmioIsStatus_ex) ex_rs2_approx aiStatusReg
    let aiInputNext  := Signal.mux (mmioWE &&& mmioIsInput_ex)  ex_rs2_approx aiInputReg

    -- UART 8250 write logic (EX stage)
    let uartWE := idex_memWrite &&& (isUART_ex &&& validEX)
    let uartOffset_ex := alu_result_approx.map (BitVec.extractLsb' 0 3 ·)
    let uartDLAB := (uartLCRReg.map (BitVec.extractLsb' 7 1 ·)) === 1#1
    let uartWdata8 := ex_rs2_approx.map (BitVec.extractLsb' 0 8 ·)
    -- Offset matches
    let uartOff0 := uartOffset_ex === 0#3
    let uartOff1 := uartOffset_ex === 1#3
    let uartOff3 := uartOffset_ex === 3#3
    let uartOff4 := uartOffset_ex === 4#3
    let uartOff7 := uartOffset_ex === 7#3
    -- Register updates (DLAB-aware for offsets 0 and 1)
    let uartLCRNext := Signal.mux (uartWE &&& uartOff3)
      uartWdata8 uartLCRReg
    let uartIERNext := Signal.mux (uartWE &&& (uartOff1 &&& (~~~uartDLAB)))
      uartWdata8 uartIERReg
    let uartMCRNext := Signal.mux (uartWE &&& uartOff4)
      uartWdata8 uartMCRReg
    let uartSCRNext := Signal.mux (uartWE &&& uartOff7)
      uartWdata8 uartSCRReg
    let uartDLLNext := Signal.mux (uartWE &&& (uartOff0 &&& uartDLAB))
      uartWdata8 uartDLLReg
    let uartDLMNext := Signal.mux (uartWE &&& (uartOff1 &&& uartDLAB))
      uartWdata8 uartDLMReg

    let csrIsImm := (idex_csrFunct3.map (BitVec.extractLsb' 2 1 ·)) === 1#1
    let csrZimm := 0#27 ++ idex_rs1Idx
    let csrWdata := Signal.mux csrIsImm csrZimm ex_rs1
    let csrF3Low := idex_csrFunct3.map (BitVec.extractLsb' 0 2 ·)
    let csrIsRW := csrF3Low === 0b01#2
    let csrIsRS := csrF3Low === 0b10#2
    let csrIsRC := csrF3Low === 0b11#2
    -- Three-way RW/RS/RC selector (proven in CSR/NewValue.lean).
    let mkCsrNewVal (oldVal : Signal dom (BitVec 32)) :=
      Sparkle.IP.RV32.CSR.csrNewValSignal oldVal csrWdata csrIsRW csrIsRS csrIsRC
    -- CSR new values (M-mode)
    let mstatusNewCSR  := mkCsrNewVal mstatusReg
    let mieNewCSR      := mkCsrNewVal mieReg
    let mtvecNewCSR    := mkCsrNewVal mtvecReg
    let mscratchNewCSR := mkCsrNewVal mscratchReg
    let mepcNewCSR     := mkCsrNewVal mepcReg
    let mcauseNewCSR   := mkCsrNewVal mcauseReg
    let mtvalNewCSR    := mkCsrNewVal mtvalReg
    -- mip new value: for CSRRW/CSRRS/CSRRC the operand acts on the *current
    -- mipValue* (combined HW + soft bits), but only the soft-writable bits
    -- (SSIP=1, STIP=5, SEIP=9) actually update mipSoftReg.
    let mipNewCSR      := mkCsrNewVal mipValue
    let sipNewCSR      := mkCsrNewVal mipValue
    -- CSR new values (S-mode)
    let sieNewCSR      := mkCsrNewVal sieReg
    let stvecNewCSR    := mkCsrNewVal stvecReg
    let sscratchNewCSR := mkCsrNewVal sscratchReg
    let sepcNewCSR     := mkCsrNewVal sepcReg
    let scauseNewCSR   := mkCsrNewVal scauseReg
    let stvalNewCSR    := mkCsrNewVal stvalReg
    let satpNewCSR     := mkCsrNewVal satpReg
    -- CSR new values (delegation)
    let medelegNewCSR  := mkCsrNewVal medelegReg
    let midelegNewCSR  := mkCsrNewVal midelegReg
    -- CSR new values (counter enable)
    let mcounterenNewCSR := mkCsrNewVal mcounterenReg
    let scounterenNewCSR := mkCsrNewVal scounterenReg

    -- SSTATUS write: merge S-mode bits back into mstatus
    let sstatusNewVal  := mkCsrNewVal sstatusView
    let mstatusNonS := mstatusReg &&& (~~~sstatusMask)
    let sstatusMasked := sstatusNewVal &&& sstatusMask
    let sstatusWdataOut := mstatusNonS ||| sstatusMasked
    let sstatusWriteActive := idex_isCsr_valid &&& csrIsSstatus

    -- Trap-entry mstatus transformers: see `IP.RV32.CSR.MStatus`.
    -- Pure versions `mstatusTrapMVal_pure` / `mstatusTrapSVal_pure`
    -- are bv_decide-proven to satisfy the priv-spec bit-level rules
    -- (MIE←0/SIE←0; MPIE←old MIE / SPIE←old SIE; MPP←priv / SPP←priv[0]).
    let mstatusTrapMVal :=
      Sparkle.IP.RV32.CSR.mstatusTrapMValSignal
        mstatusReg mstatusMIE_flag privMode
    let mstatusTrapSVal :=
      Sparkle.IP.RV32.CSR.mstatusTrapSValSignal
        mstatusReg mstatusSIE_flag privMode

    let mstatusTrapVal := Signal.mux trapToS mstatusTrapSVal mstatusTrapMVal

    -- MRET / SRET mstatus transformers: see `IP.RV32.CSR.MStatus`.
    -- Pure versions `mstatusMretVal_pure` / `mstatusSretVal_pure` are
    -- proven (via `bv_decide`) to satisfy the bit-level priv-spec
    -- (MIE←MPIE, MPIE←1, MPP←0 for MRET; symmetric for SRET) and to
    -- equal the impl-style mask-and-or expressions below.
    let mstatusMretVal :=
      Sparkle.IP.RV32.CSR.mstatusMretValSignal mstatusReg mstatusMPIE_flag
    let mstatusSretVal :=
      Sparkle.IP.RV32.CSR.mstatusSretValSignal mstatusReg mstatusSPIE_flag

    -- Five-way priority mux: trap > mret > sret > sstatus-write > mstatus-write > hold.
    -- Proven in `IP/RV32/CSR/MStatusNext.lean` (priority + invariance).
    let mstatusNext :=
      Sparkle.IP.RV32.CSR.mstatusNextSignal
        trap_taken mstatusTrapVal
        idex_isMret mstatusMretVal
        idex_isSret mstatusSretVal
        sstatusWriteActive sstatusWdataOut
        (idex_isCsr_valid &&& csrIsMstatus) mstatusNewCSR
        mstatusReg
    -- Plain CSR write commits (proven in CSR/Commit.lean).
    let mieNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsMie) mieNewCSR mieReg
    let mtvecNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsMtvec) mtvecNewCSR mtvecReg
    let mscratchNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsMscratch) mscratchNewCSR mscratchReg
    -- mepc: use fetchPC for instruction page fault, dMissPC for d-side page fault.
    -- For asynchronous interrupts (timer/sw/ext, M-mode and S-mode), the trap
    -- is not associated with any in-flight instruction. We need to set mepc
    -- to the PC of the next instruction the kernel should run after sret.
    -- Two cases:
    --  (a) IDEX has a valid in-flight instruction: it was suppressed by
    --      suppressEXWB and never committed. mepc = idex_pc so it re-runs.
    --  (b) IDEX has been squashed (e.g., post-mret transition cycle), so
    --      idex_pc may point into stale (M-mode) territory. In that case,
    --      use pcReg (the redirected next-fetch PC) as mepc.
    -- We detect "IDEX has a valid live instruction" by checking the OR of the
    -- IDEX side-effect-bearing control bits — if none are set, IDEX is a NOP
    -- (squashed) and pcReg is the right choice.
    let isAsyncInt := timerIntEnabled ||| swIntEnabled ||| sTimerIntEnabled |||
                      sSwIntEnabled ||| sExtIntEnabled
    let idexLive := idex_regWrite ||| idex_memRead ||| idex_memWrite |||
                    idex_jump ||| idex_branch ||| idex_isCsr |||
                    idex_isEcall ||| idex_isMret ||| idex_isSret |||
                    idex_isAMO ||| idex_isMext ||| idex_isSFenceVMA
    -- Trap-PC selector: see `IP.RV32.Trap.TrapPC`. The pure version
    -- `trapPCPure` and the Signal-level `trapPCSignal` are equivalent
    -- (theorem `trapPCSignal_eq_pure`); this call inherits the proven
    -- spec (ifetchPF→fetchPC, dPF→dMissPC, async+live→idex_pc,
    -- async+dead→pcReg, sync→idex_pc).
    let trapPC :=
      Sparkle.IP.RV32.Trap.trapPCSignal
        ifetchPageFault pageFault isAsyncInt idexLive
        fetchPC dMissPC idex_pc pcReg
    -- Trap-overridable CSR commits (proven in CSR/Commit.lean):
    -- trapTo > write > hold.
    let mepcNext :=
      Sparkle.IP.RV32.CSR.csrTrapOverrideNextSignal
        trapToM trapPC (idex_isCsr_valid &&& csrIsMepc) mepcNewCSR mepcReg
    let mcauseNext :=
      Sparkle.IP.RV32.CSR.csrTrapOverrideNextSignal
        trapToM trapCause (idex_isCsr_valid &&& csrIsMcause) mcauseNewCSR mcauseReg
    -- trapVal: fetchPC for ifetchPageFault, dMissVaddr for d-side pageFault, else 0
    let trapVal := Signal.mux ifetchPageFault fetchPC
      (Signal.mux pageFault dMissVaddr (Signal.pure 0#32))
    let mtvalNext :=
      Sparkle.IP.RV32.CSR.csrTrapOverrideNextSignal
        trapToM trapVal (idex_isCsr_valid &&& csrIsMtval) mtvalNewCSR mtvalReg
    -- mipSoftReg next-state: only SSIP/STIP/SEIP bits update from CSR writes
    -- (mip CSR or sip CSR). All other bits keep their prior soft value.
    let mipSoftWriteMask : Signal dom (BitVec 32) := Signal.pure 0x00000222#32
    let mipWriteEn := idex_isCsr_valid &&& csrIsMip
    let sipWriteEn := idex_isCsr_valid &&& csrIsSip
    let mipMaskedNew := mipNewCSR &&& mipSoftWriteMask
    let sipMaskedNew := sipNewCSR &&& mipSoftWriteMask
    let mipSoftKept  := mipSoftReg &&& (~~~mipSoftWriteMask)
    let mipSoftNext :=
      Signal.mux mipWriteEn (mipSoftKept ||| mipMaskedNew)
      (Signal.mux sipWriteEn (mipSoftKept ||| sipMaskedNew) mipSoftReg)

    -- S-mode CSR next-state (same proven patterns from CSR/Commit.lean).
    let sieNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsSie) sieNewCSR sieReg
    let stvecNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsStvec) stvecNewCSR stvecReg
    let sscratchNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsSscratch) sscratchNewCSR sscratchReg
    let sepcNext :=
      Sparkle.IP.RV32.CSR.csrTrapOverrideNextSignal
        trapToS trapPC (idex_isCsr_valid &&& csrIsSepc) sepcNewCSR sepcReg
    let scauseNext :=
      Sparkle.IP.RV32.CSR.csrTrapOverrideNextSignal
        trapToS trapCause (idex_isCsr_valid &&& csrIsScause) scauseNewCSR scauseReg
    let stvalNext :=
      Sparkle.IP.RV32.CSR.csrTrapOverrideNextSignal
        trapToS trapVal (idex_isCsr_valid &&& csrIsStval) stvalNewCSR stvalReg
    let satpNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsSatp) satpNewCSR satpReg

    -- Delegation register next-state
    let medelegNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsMedeleg) medelegNewCSR medelegReg
    let midelegNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsMideleg) midelegNewCSR midelegReg
    -- Counter enable next-state
    let mcounterenNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsMcounteren) mcounterenNewCSR mcounterenReg
    let scounterenNext :=
      Sparkle.IP.RV32.CSR.csrPlainNextSignal
        (idex_isCsr_valid &&& csrIsScounteren) scounterenNewCSR scounterenReg

    -- Privilege mode next-state: see `IP.RV32.Privilege.PrivMode`.
    -- Pure version `privModeNextPure` and Signal-level
    -- `privModeNextSignal` are equivalent (theorem
    -- `privModeNextSignal_eq_pure`); this call inherits the proven
    -- spec (trap→M/S, mret→mpp, sret→spp, hold otherwise).
    let privModeNext :=
      Sparkle.IP.RV32.Privilege.privModeNextSignal
        trapToM trapToS idex_isMret idex_isSret mpp sretPriv privMode

    -- A-ext: Reservation management.
    -- LR sets the reservation. SC always clears it (whether it succeeded or not,
    -- per RISC-V spec). Traps and SFENCE.VMA also invalidate the reservation —
    -- this is critical for correctness of LR/SC across interrupts and
    -- privilege transitions, since otherwise an LR followed by an interrupt
    -- followed by an SC would silently succeed despite intervening code that
    -- may have modified the reservation set.
    -- Use exwb_physAddr (translated PA) for consistency with the AMO writeback.
    -- Reservation next-state: see `IP.RV32.AMO.Reservation`.
    -- The pure version `resValidNextPure` and the Signal-level
    -- `resValidNextSignal` are equivalent (theorem
    -- `resValidNextSignal_eq_pure`); this call inherits the proven
    -- invariants (trap → invalid, LR → valid, SC → invalid, hold).
    let resValidNext :=
      Sparkle.IP.RV32.AMO.resValidNextSignal
        trap_taken exwb_isLR exwb_isSC reservationValid
    let resAddrNext := Signal.mux exwb_isLR exwb_physAddr reservationAddr

    -- I-side PTW request: ifetch miss when PTW is idle and no D-side miss taking priority.
    -- Also gate on ~trap_taken: when a trap is firing this cycle, fetchPC still
    -- holds the OLD value (the trapping VA) while pcReg is being redirected to
    -- the trap target. Letting PTW start on the old VA would walk a known-bad
    -- address and immediately re-fault, masquerading as a fault on the trap
    -- target's PC. The trap-target ifetch will request PTW one cycle later
    -- after fetchPC catches up.
    let ifetchPTWReq := ifetchTLBMiss &&&
      (ptwIsIdle &&& ((~~~dTLBMiss) &&& (isMMUIdle &&& (~~~trap_taken))))

    -- PTW request: D-side TLB miss OR I-side PTW request
    let ptwReq := dTLBMiss ||| ifetchPTWReq

    -- PTW latch vaddr on start: D-side has priority
    let ptwVaddrOnStart := Signal.mux dTLBMiss alu_result_approx fetchPC
    let ptwVaddrNext := Signal.mux (ptwIsIdle &&& ptwReq)
      ptwVaddrOnStart ptwVaddrReg

    -- PTE fields decoded from dmem_rdata (valid in L1_WAIT/L0_WAIT states)
    let dmemPteValid := (dmem_rdata.map (BitVec.extractLsb' 0 1 ·)) === 1#1
    let dmemPteRBit := (dmem_rdata.map (BitVec.extractLsb' 1 1 ·)) === 1#1
    let dmemPteXBit := (dmem_rdata.map (BitVec.extractLsb' 3 1 ·)) === 1#1
    let dmemPteIsLeaf := dmemPteRBit ||| dmemPteXBit
    let dmemPteInvalid := ~~~dmemPteValid
    let pteFlags := ptwPteReg.map (BitVec.extractLsb' 0 8 ·)

    -- PTE latching: in WAIT states, latch dmem_rdata (has PTE from prior REQ addr)
    let isDataReady := ptwIsL1Wait ||| ptwIsL0Wait
    let ptwPteNext := Signal.mux isDataReady dmem_rdata ptwPteReg

    -- PTW state transitions (7-state FSM with DMEM read latency handling)
    -- IDLE(0) → L1_REQ(1) on TLB miss
    let nextFromPtwIdle := Signal.mux ptwReq (Signal.pure 1#3) (Signal.pure 0#3)
    -- L1_REQ(1) → L1_WAIT(2): always wait 1 cycle for DMEM read
    -- L1_WAIT(2): dmem_rdata has L1 PTE → DONE(5)/L0_REQ(3)/FAULT(6)
    let nextFromL1Wait := Signal.mux dmemPteInvalid (Signal.pure 6#3)
      (Signal.mux dmemPteIsLeaf (Signal.pure 5#3) (Signal.pure 3#3))
    -- L0_REQ(3) → L0_WAIT(4): always wait 1 cycle for DMEM read
    -- L0_WAIT(4): dmem_rdata has L0 PTE → DONE(5)/FAULT(6)
    let nextFromL0Wait := Signal.mux dmemPteInvalid (Signal.pure 6#3)
      (Signal.mux dmemPteIsLeaf (Signal.pure 5#3) (Signal.pure 6#3))
    let ptwStateNext := Signal.mux ptwIsIdle nextFromPtwIdle
      (Signal.mux ptwIsL1Req (Signal.pure 2#3)
      (Signal.mux ptwIsL1Wait nextFromL1Wait
      (Signal.mux ptwIsL0Req (Signal.pure 4#3)
      (Signal.mux ptwIsL0Wait nextFromL0Wait
        (Signal.pure 0#3)))))

    -- Megapage tracking: leaf found at L1 level
    let ptwMegaNext := Signal.mux (ptwIsL1Wait &&& (dmemPteIsLeaf &&& (~~~dmemPteInvalid)))
      (Signal.pure true)
      (Signal.mux ptwIsIdle (Signal.pure false) ptwMegaReg)

    -- TLB fill on PTW completion
    let tlbFill := ptwIsDone
    let fillVPN := ptwVaddrReg.map (BitVec.extractLsb' 12 20 ·)

    -- Replacement pointer: which entry to fill
    let replIs0 := replPtrReg === 0#2
    let replIs1 := replPtrReg === 1#2
    let replIs2 := replPtrReg === 2#2
    let replIs3 := replPtrReg === 3#2
    let doFill0 := tlbFill &&& replIs0
    let doFill1 := tlbFill &&& replIs1
    let doFill2 := tlbFill &&& replIs2
    let doFill3 := tlbFill &&& replIs3

    -- SFENCE.VMA clears all TLB entries
    let sfenceVMA := idex_isSFenceVMA

    -- TLB entry next-state
    let tlb0ValidNext := Signal.mux sfenceVMA (Signal.pure false) (Signal.mux doFill0 (Signal.pure true) tlb0Valid)
    let tlb0VPNNext := Signal.mux doFill0 fillVPN tlb0VPN
    let tlb0PPNNext := Signal.mux doFill0 ptePPNFull tlb0PPN
    let tlb0FlagsNext := Signal.mux doFill0 pteFlags tlb0Flags
    let tlb0MegaNext := Signal.mux doFill0 ptwMegaReg tlb0Mega

    let tlb1ValidNext := Signal.mux sfenceVMA (Signal.pure false) (Signal.mux doFill1 (Signal.pure true) tlb1Valid)
    let tlb1VPNNext := Signal.mux doFill1 fillVPN tlb1VPN
    let tlb1PPNNext := Signal.mux doFill1 ptePPNFull tlb1PPN
    let tlb1FlagsNext := Signal.mux doFill1 pteFlags tlb1Flags
    let tlb1MegaNext := Signal.mux doFill1 ptwMegaReg tlb1Mega

    let tlb2ValidNext := Signal.mux sfenceVMA (Signal.pure false) (Signal.mux doFill2 (Signal.pure true) tlb2Valid)
    let tlb2VPNNext := Signal.mux doFill2 fillVPN tlb2VPN
    let tlb2PPNNext := Signal.mux doFill2 ptePPNFull tlb2PPN
    let tlb2FlagsNext := Signal.mux doFill2 pteFlags tlb2Flags
    let tlb2MegaNext := Signal.mux doFill2 ptwMegaReg tlb2Mega

    let tlb3ValidNext := Signal.mux sfenceVMA (Signal.pure false) (Signal.mux doFill3 (Signal.pure true) tlb3Valid)
    let tlb3VPNNext := Signal.mux doFill3 fillVPN tlb3VPN
    let tlb3PPNNext := Signal.mux doFill3 ptePPNFull tlb3PPN
    let tlb3FlagsNext := Signal.mux doFill3 pteFlags tlb3Flags
    let tlb3MegaNext := Signal.mux doFill3 ptwMegaReg tlb3Mega

    -- Replacement pointer: increment on fill
    let replPtrNext := Signal.mux tlbFill
      (replPtrReg + 1#2) replPtrReg

    -- MMU state transitions (D-side only)
    -- On dTLBMiss: skip TLB_LOOKUP, go directly to PTW_WALK (state 2)
    let nextFromMMUIdle := Signal.mux dTLBMiss (Signal.pure 2#3) (Signal.pure 0#3)
    let nextFromPTWWalk := Signal.mux ptwIsDone (Signal.pure 3#3)
      (Signal.mux ptwIsFault (Signal.pure 4#3) (Signal.pure 2#3))
    let mmuStateNext := Signal.mux isMMUIdle nextFromMMUIdle
      (Signal.mux isPTWWalk nextFromPTWWalk
        (Signal.pure 0#3))

    -- Track whether PTW is serving an I-side miss
    let ptwIsIfetchNext := Signal.mux ptwIsIdle
      (Signal.mux (ifetchPTWReq &&& (~~~dTLBMiss))
        (Signal.pure true) (Signal.pure false))
      ptwIsIfetch

    -- I-side page fault pending: set when PTW faults for ifetch, clear on trap or M-mode
    let ifetchFaultPendingNext := Signal.mux ifetchPageFault (Signal.pure false)
      (Signal.mux bypassMMU (Signal.pure false)
        (Signal.mux (ptwIsFault &&& ptwIsIfetch) (Signal.pure true)
          ifetchFaultPending))

    -- 8-way priority redirect mux (proven in Pipeline/PCNext.lean):
    -- trap > mret > sret > dMMURedirect > sfence > flush > stall > pc+4.
    let pcNext :=
      Sparkle.IP.RV32.Pipeline.pcNextSignal
        trap_taken trap_target
        idex_isMret mret_target
        idex_isSret sret_target
        dMMURedirect dMissPC
        idex_isSFenceVMA idex_pc4
        flush jumpTarget
        stall pcReg
        pcPlus4

    -- Bug fix #3: fetchPC must take pcReg_next (= pcNext) on flush
    let fetchPCIn := Signal.mux flush pcNext (Signal.mux stall fetchPC pcReg)

    -- Divider pending: set on start, cleared on done or flush
    let divPendingNext := Signal.mux flushOrDelay (Signal.pure false)
      (Signal.mux divStart (Signal.pure true)
        (Signal.mux divDone (Signal.pure false)
          divPending))

    -- D-side TLB miss registers: latch on dTLBMiss, hold otherwise
    let dMissPCNext := Signal.mux dTLBMiss idex_pc dMissPC
    let dMissVaddrNext := Signal.mux dTLBMiss alu_result_approx dMissVaddr
    let dMissIsStoreNext := Signal.mux dTLBMiss idex_memWrite dMissIsStore

    bundleAll! [
      Signal.register 0#32 pcNext,                                          -- 0: pcReg
      Signal.register 0#32 fetchPCIn,                                       -- 1: fetchPC
      Signal.register false flush,                                          -- 2: flushDelay
      Signal.register 0x00000013#32 ifid_inst_in,                           -- 3: ifid_inst
      Signal.register 0#32 ifid_pc_in,                                     -- 4: ifid_pc
      Signal.register 0#32 ifid_pc4_in,                                    -- 5: ifid_pc4
      -- ID/EX (freezeIDEX freeze: hold current when freezeIDEX, else squash or pass)
      Signal.register 0#4 (Signal.mux freezeIDEX idex_aluOp (Signal.mux squash (Signal.pure 0#4) id_aluOp)),       -- 6
      Signal.register false (Signal.mux freezeIDEX idex_regWrite (Signal.mux squash (Signal.pure false) id_regWrite)),
      Signal.register false (Signal.mux freezeIDEX idex_memRead (Signal.mux squash (Signal.pure false) id_memRead)),
      Signal.register false (Signal.mux freezeIDEX idex_memWrite (Signal.mux squash (Signal.pure false) id_memWrite)),
      Signal.register false (Signal.mux freezeIDEX idex_memToReg (Signal.mux squash (Signal.pure false) id_memToReg)),
      Signal.register false (Signal.mux freezeIDEX idex_branch (Signal.mux squash (Signal.pure false) id_isBranch)),
      Signal.register false (Signal.mux freezeIDEX idex_jump (Signal.mux squash (Signal.pure false) id_jump)),
      Signal.register false (Signal.mux freezeIDEX idex_auipc (Signal.mux squash (Signal.pure false) id_auipc)),
      Signal.register false (Signal.mux freezeIDEX idex_aluSrcB (Signal.mux squash (Signal.pure false) id_aluSrcB)),
      Signal.register false (Signal.mux freezeIDEX idex_isJalr (Signal.mux squash (Signal.pure false) id_isJALR)),
      Signal.register false (Signal.mux freezeIDEX idex_isCsr (Signal.mux squash (Signal.pure false) id_isCsr)),
      Signal.register false (Signal.mux freezeIDEX idex_isEcall (Signal.mux squash (Signal.pure false) id_isEcall)),
      Signal.register false (Signal.mux freezeIDEX idex_isMret (Signal.mux squash (Signal.pure false) id_isMret)),
      Signal.register 0#32 (Signal.mux freezeIDEX idex_rs1Val id_rs1Val),       -- 19
      Signal.register 0#32 (Signal.mux freezeIDEX idex_rs2Val id_rs2Val),       -- 20
      Signal.register 0#32 (Signal.mux freezeIDEX idex_imm id_imm),             -- 21
      Signal.register 0#5 (Signal.mux freezeIDEX idex_rd (Signal.mux squash (Signal.pure 0#5) id_rd)),
      Signal.register 0#5 (Signal.mux freezeIDEX idex_rs1Idx id_rs1),
      Signal.register 0#5 (Signal.mux freezeIDEX idex_rs2Idx id_rs2),
      Signal.register 0#3 (Signal.mux freezeIDEX idex_funct3 id_funct3),
      Signal.register 0#32 (Signal.mux freezeIDEX idex_pc ifid_pc),
      Signal.register 0#32 (Signal.mux freezeIDEX idex_pc4 ifid_pc4),
      Signal.register 0#12 (Signal.mux freezeIDEX idex_csrAddr id_csrAddr),
      Signal.register 0#3 (Signal.mux freezeIDEX idex_csrFunct3 id_funct3),
      -- EX/WB (suppress side-effects during suppressEXWB = dTLBMiss | holdEX, freeze data during freezeIDEX)
      Signal.register 0#32 (Signal.mux freezeIDEX exwb_alu alu_result),          -- 30: exwb_alu
      Signal.register 0#32 (Signal.mux freezeIDEX exwb_physAddr effectiveAddr),  -- 31: exwb_physAddr
      Signal.register 0#5 (Signal.mux suppressEXWB (Signal.pure 0#5) idex_rd),    -- 32: exwb_rd
      Signal.register false (Signal.mux suppressEXWB (Signal.pure false) idex_regWrite), -- 33: exwb_regW
      Signal.register false (Signal.mux suppressEXWB (Signal.pure false) idex_memToReg), -- 34: exwb_m2r
      Signal.register 0#32 (Signal.mux freezeIDEX exwb_pc4 idex_pc4),           -- 35: exwb_pc4
      Signal.register false (Signal.mux suppressEXWB (Signal.pure false) idex_jump),     -- 36: exwb_jump
      Signal.register false (Signal.mux suppressEXWB (Signal.pure false) idex_isCsr),    -- 37: exwb_isCsr
      Signal.register 0#32 (Signal.mux freezeIDEX exwb_csrRdata csr_rdata),     -- 38: exwb_csrRdata
      Signal.register 0#5 wb_addr,                                          -- 39: prev_wb_addr
      Signal.register 0#32 wb_data,                                         -- 40: prev_wb_data
      Signal.register false wb_en,                                           -- 41: prev_wb_en
      Signal.register 0#32 (Signal.mux useTranslatedAddr dPhysAddr alu_result),  -- 42: prevStoreAddr (use phys)
      Signal.register 0#32 ex_rs2,                                          -- 43: prevStoreData
      Signal.register false (Signal.mux suppressEXWB (Signal.pure false) idex_memWrite), -- 44: prevStoreEn
      Signal.register 0#32 msipNext,                                        -- 45
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
      Signal.register 0#32 mtvalNext,
      Signal.register 0#32 aiStatusNext,
      Signal.register 0#32 aiInputNext,
      -- Sub-word + M-ext (holdEX aware)
      Signal.register 0#3 (Signal.mux freezeIDEX exwb_funct3 idex_funct3),      -- 59: exwb_funct3
      Signal.register false (Signal.mux freezeIDEX idex_isMext (Signal.mux squash (Signal.pure false) id_isMext)),  -- 60
      -- A-ext registers (61-69)
      Signal.register false resValidNext,
      Signal.register 0#32 resAddrNext,
      Signal.register false (Signal.mux freezeIDEX idex_isAMO (Signal.mux squash (Signal.pure false) id_isAMO)),
      Signal.register 0#5 (Signal.mux freezeIDEX idex_amoOp (Signal.mux squash (Signal.pure 0#5) id_amoOp)),
      Signal.register false (Signal.mux suppressEXWB (Signal.pure false) idex_isAMO),   -- exwb_isAMO
      Signal.register 0#5 (Signal.mux freezeIDEX exwb_amoOp idex_amoOp),              -- exwb_amoOp
      Signal.register false pendingWriteEnNext,
      Signal.register 0#32 pendingWriteAddrNext,
      Signal.register 0#32 pendingWriteDataNext,
      -- S-mode CSRs + privilege (70-79)
      Signal.register 3#2 privModeNext,
      Signal.register 0#32 sieNext,
      Signal.register 0#32 stvecNext,
      Signal.register 0#32 sscratchNext,
      Signal.register 0#32 sepcNext,
      Signal.register 0#32 scauseNext,
      Signal.register 0#32 stvalNext,
      Signal.register 0#32 satpNext,
      Signal.register 0#32 medelegNext,
      Signal.register 0#32 midelegNext,
      -- MMU TLB + PTW (80-107)
      Signal.register 0#3 mmuStateNext,
      Signal.register 0#3 ptwStateNext,
      Signal.register 0#32 ptwVaddrNext,
      Signal.register 0#32 ptwPteNext,
      Signal.register false ptwMegaNext,
      Signal.register 0#2 replPtrNext,
      Signal.register false tlb0ValidNext,
      Signal.register 0#20 tlb0VPNNext,
      Signal.register 0#22 tlb0PPNNext,
      Signal.register 0#8 tlb0FlagsNext,
      Signal.register false tlb0MegaNext,
      Signal.register false tlb1ValidNext,
      Signal.register 0#20 tlb1VPNNext,
      Signal.register 0#22 tlb1PPNNext,
      Signal.register 0#8 tlb1FlagsNext,
      Signal.register false tlb1MegaNext,
      Signal.register false tlb2ValidNext,
      Signal.register 0#20 tlb2VPNNext,
      Signal.register 0#22 tlb2PPNNext,
      Signal.register 0#8 tlb2FlagsNext,
      Signal.register false tlb2MegaNext,
      Signal.register false tlb3ValidNext,
      Signal.register 0#20 tlb3VPNNext,
      Signal.register 0#22 tlb3PPNNext,
      Signal.register 0#8 tlb3FlagsNext,
      Signal.register false tlb3MegaNext,
      Signal.register false ptwIsIfetchNext,
      Signal.register false ifetchFaultPendingNext,
      -- Pipeline additions (108-109)
      Signal.register false (Signal.mux freezeIDEX idex_isSret (Signal.mux squash (Signal.pure false) id_isSret)),
      Signal.register false (Signal.mux freezeIDEX idex_isSFenceVMA (Signal.mux squash (Signal.pure false) id_isSFenceVMA)),
      -- UART 8250 registers (110-115)
      Signal.register 0#8 uartLCRNext,
      Signal.register 0#8 uartIERNext,
      Signal.register 0#8 uartMCRNext,
      Signal.register 0#8 uartSCRNext,
      Signal.register 0#8 uartDLLNext,
      Signal.register 0#8 uartDLMNext,
      -- Counter CSRs (116-117)
      Signal.register 0#32 mcounterenNext,
      Signal.register 0#32 scounterenNext,
      -- Divider pending (118)
      Signal.register false divPendingNext,
      -- D-side TLB miss registers (119-121)
      Signal.register 0#32 dMissPCNext,
      Signal.register 0#32 dMissVaddrNext,
      Signal.register false dMissIsStoreNext,
      Signal.register false ifetchStall,  -- stallDelay (kept stable; new state below)
      Signal.register 0#32 mipSoftNext     -- mipSoftReg (123): SW-writable mip bits
    ]

/-- Backward-compatible wrapper using firmware function for IMEM read. -/
private def rv32iSoCWithFirmwareBody {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    (state : Signal dom SoCState) : Signal dom SoCState :=
  let fetchPC := SoCState.fetchPC state
  let imem_addr := fetchPC.map (BitVec.extractLsb' 2 12 ·)
  let imem_rdata := imem_addr.map firmware
  rv32iSoCBody imem_rdata (state := state)

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
    State indices: 0=PC, 42=storeAddr, 43=storeData, 44=storeEn
    122 registers total (incl. S-mode, MMU, trap delegation, UART 8250, counter CSRs, divider). -/
def rv32iSoCSimulateFull {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    : IO (Signal dom SoCState) := do
  Signal.loopMemo (rv32iSoCWithFirmwareBody firmware)

/-- Non-memoized full state for debugging -/
def rv32iSoCDebugFull {dom : DomainConfig}
    (firmware : BitVec 12 → BitVec 32)
    : Signal dom SoCState :=
  Signal.loop (rv32iSoCWithFirmwareBody firmware)

-- ============================================================================
-- JIT-accelerated simulation via named output wires
-- ============================================================================
--
-- Uses wires that feed the top-level output in rv32iSoCSynth (SoCVerilog.lean).
-- These are stable: they can't be DCE'd and their names don't collide.
-- Note: JIT.getOutput doesn't work because the CppSim backend skips
-- >64-bit packed output assignments. Use JIT.getWire with named wires instead.

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop

/-- Wire names for SoC output observation.
    These correspond to the values computed in rv32iSoCSynth and are stable
    because they feed the top-level output (immune to DCE).

    The trap-related wires (`_gen_trap_taken`, `_gen_trapCause`,
    `_gen_mepcReg` / `_gen_mtvalReg` / `_gen_sepcReg` / `_gen_scauseReg` /
    `_gen_stvalReg`) give the JIT runner the same observability that
    Verilator's tb_soc.cpp gets via internal-signal probes. With them, a
    JIT harness can print "TRAP at cycle N: PC=... cause=... tval=..."
    just like Verilator does, instead of relying on UART side effects to
    infer that something went wrong. -/
def SoCOutput.wireNames : Array String :=
  #[ "_gen_pcReg"            -- 0
   , "_gen_uartValidBV"      -- 1
   , "_gen_prevStoreData"    -- 2
   , "_gen_satpReg"          -- 3
   , "_gen_ptwPteReg"        -- 4
   , "_gen_ptwVaddrReg"      -- 5
   , "_gen_trap_taken"       -- 6  combinational: 1 cycle pulse on a trap
   , "_gen_trapCause"        -- 7  cause value committed on the same cycle
   , "_gen_mepcReg"          -- 8  M-mode trap context (after commit)
   , "_gen_mcauseReg"        -- 9
   , "_gen_mtvalReg"         -- 10
   , "_gen_sepcReg"          -- 11 S-mode trap context (after commit)
   , "_gen_scauseReg"        -- 12
   , "_gen_stvalReg"         -- 13
   , "_gen_aiInputReg"       -- 14 BitNet peripheral pipeline observability
   , "_gen_gateAcc"          -- 15
   , "_gen_gateScaled"       -- 16
   , "_gen_gateActivated"    -- 17
   , "_gen_upAcc"            -- 18
   , "_gen_upScaled"         -- 19
   , "_gen_elemResult"       -- 20
   , "_gen_downScaled"       -- 21
   ]

/-- SoC output snapshot — one cycle's worth of observable values -/
structure SoCOutput where
  pc        : BitVec 32
  uartValid : Bool
  uartData  : BitVec 32
  satp      : BitVec 32
  ptwPte    : BitVec 32
  ptwVaddr  : BitVec 32
  -- Trap observation (matches Verilator tb_soc.cpp's internal-signal probes)
  trapTaken : Bool
  trapCause : BitVec 32
  mepc      : BitVec 32
  mcause    : BitVec 32
  mtval     : BitVec 32
  sepc      : BitVec 32
  scause    : BitVec 32
  stval     : BitVec 32
  deriving Inhabited

def SoCOutput.fromWireValues (vals : Array UInt64) : SoCOutput :=
  { pc        := BitVec.ofNat 32 (vals[0]?.getD 0).toNat
    uartValid := (vals[1]?.getD 0) != 0
    uartData  := BitVec.ofNat 32 (vals[2]?.getD 0).toNat
    satp      := BitVec.ofNat 32 (vals[3]?.getD 0).toNat
    ptwPte    := BitVec.ofNat 32 (vals[4]?.getD 0).toNat
    ptwVaddr  := BitVec.ofNat 32 (vals[5]?.getD 0).toNat
    trapTaken := (vals[6]?.getD 0) != 0
    trapCause := BitVec.ofNat 32 (vals[7]?.getD 0).toNat
    mepc      := BitVec.ofNat 32 (vals[8]?.getD 0).toNat
    mcause    := BitVec.ofNat 32 (vals[9]?.getD 0).toNat
    mtval     := BitVec.ofNat 32 (vals[10]?.getD 0).toNat
    sepc      := BitVec.ofNat 32 (vals[11]?.getD 0).toNat
    scause    := BitVec.ofNat 32 (vals[12]?.getD 0).toNat
    stval     := BitVec.ofNat 32 (vals[13]?.getD 0).toNat }

/-- JIT-accelerated SoC simulation returning output wires as a Signal.
    Uses named output wires — immune to DCE and name collisions.

    Parameters:
    - `jitCppPath`: Path to the pre-generated JIT .cpp file
    - `firmware`: Array of 32-bit instruction words to load into IMEM -/
def rv32iSoCJITSimulate {dom : DomainConfig}
    (jitCppPath : String)
    (firmware : Array (BitVec 32))
    : IO (Signal dom SoCOutput) := do
  Signal.loopMemoJIT
    (jitCppPath := jitCppPath)
    (wireNames := SoCOutput.wireNames)
    (loadMem := fun h => do
      let memSize := min firmware.size (1 <<< 12)
      for i in [:memSize] do
        let word := if hi : i < firmware.size then firmware[i] else 0#32
        JIT.setMem h 0 i.toUInt32 word.toNat.toUInt32)
    (reconstruct := fun _h vals => pure (SoCOutput.fromWireValues vals))

/-- JIT streaming simulation — O(1) memory, no caching.
    Runs the SoC for up to `cycles` cycles, calling `callback` each cycle.
    The callback receives (cycle, wire values) and returns false to stop.

    Parameters:
    - `jitCppPath`: Path to the pre-generated JIT .cpp file
    - `firmware`: Array of 32-bit instruction words to load into IMEM
    - `cycles`: Maximum number of cycles to run
    - `callback`: Per-cycle callback; receives (cycle, wire values as UInt64 array) -/
def rv32iSoCJITRun
    (jitCppPath : String)
    (firmware : Array (BitVec 32))
    (cycles : Nat)
    (callback : Nat → Array UInt64 → IO Bool)
    : IO Unit := do
  let handle ← JIT.compileAndLoad jitCppPath
  -- Load firmware into IMEM (memory index 0)
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if hi : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32
  -- Resolve wire indices and run streaming simulation
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  JIT.run handle cycles wireIndices callback
  JIT.destroy handle

end Sparkle.IP.RV32.SoC
