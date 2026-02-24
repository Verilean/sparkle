/-
  RV32I Supervisor-mode CSR Register File

  Adds S-mode CSRs alongside the M-mode CSR file.
  sstatus is a restricted view of mstatus.
  Includes privilege mode tracking and satp register.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192

namespace Sparkle.Examples.RV32.CSR.Supervisor

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- Generate S-mode CSR registers and privilege mode tracking.

    Inputs:
      clk, rst
      csr_addr[11:0]     - CSR address to read/write
      csr_funct3[2:0]    - CSR operation type
      csr_wdata[31:0]    - Write data
      csr_we             - Write enable
      -- Trap signals
      trap_to_s          - Trap targets S-mode
      trap_cause[31:0]   - Trap cause code
      trap_pc[31:0]      - PC of trapping instruction
      trap_val[31:0]     - Trap value
      -- SRET signal
      sret_taken         - SRET strobe
      -- Privilege transitions
      trap_to_m          - Trap targets M-mode (for priv update)
      mret_taken         - MRET strobe (for priv update)
      -- M-mode mstatus for sstatus view
      mstatus_in[31:0]   - Current mstatus value

    Outputs:
      csr_rdata[31:0]    - S-mode CSR read data
      csr_hit            - Address matched an S-mode CSR
      stvec_out[31:0]    - S-mode trap vector
      sepc_out[31:0]     - S-mode exception PC
      satp_out[31:0]     - SATP register value
      priv_mode[1:0]     - Current privilege mode
      -- sstatus write-back to mstatus
      sstatus_write      - sstatus was written
      sstatus_wdata[31:0]- New mstatus value from sstatus write
-/
def generateSupervisorCSRs : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "csr_addr" (.bitVector 12)
  addInput "csr_funct3" (.bitVector 3)
  addInput "csr_wdata" (.bitVector 32)
  addInput "csr_we" .bit
  addInput "trap_to_s" .bit
  addInput "trap_cause" (.bitVector 32)
  addInput "trap_pc" (.bitVector 32)
  addInput "trap_val" (.bitVector 32)
  addInput "sret_taken" .bit
  addInput "trap_to_m" .bit
  addInput "mret_taken" .bit
  addInput "mstatus_in" (.bitVector 32)

  addOutput "csr_rdata" (.bitVector 32)
  addOutput "csr_hit" .bit
  addOutput "stvec_out" (.bitVector 32)
  addOutput "sepc_out" (.bitVector 32)
  addOutput "satp_out" (.bitVector 32)
  addOutput "priv_mode" (.bitVector 2)
  addOutput "sstatus_write" .bit
  addOutput "sstatus_wdata" (.bitVector 32)

  let csrAddr := Expr.ref "csr_addr"
  let csrF3 := Expr.ref "csr_funct3"
  let csrWdata := Expr.ref "csr_wdata"
  let csrWE := Expr.ref "csr_we"

  -- =========================================================================
  -- Privilege Mode Register (2-bit: 0=U, 1=S, 3=M)
  -- =========================================================================
  let privNext ← makeWire "priv_next" (.bitVector 2)
  let privReg ← emitRegister "priv_mode_reg" "clk" "rst" (.ref privNext) (privM) (.bitVector 2)

  -- Privilege transitions:
  -- trap_to_m: priv → M (3)
  -- trap_to_s: priv → S (1)
  -- mret: priv → mstatus.MPP
  -- sret: priv → mstatus.SPP (expanded to 2 bits)
  let mpp ← makeWire "cur_mpp" (.bitVector 2)
  emitAssign mpp (.slice (.ref "mstatus_in") mstatusMPP_HI mstatusMPP_LO)

  let spp ← makeWire "cur_spp" .bit
  emitAssign spp (.slice (.ref "mstatus_in") mstatusSPP mstatusSPP)
  let sppExt ← makeWire "spp_ext" (.bitVector 2)
  emitAssign sppExt (.concat [.const 0 1, .ref spp])

  emitAssign privNext
    (Expr.mux (.ref "trap_to_m") (.const privM 2)
    (Expr.mux (.ref "trap_to_s") (.const privS 2)
    (Expr.mux (.ref "mret_taken") (.ref mpp)
    (Expr.mux (.ref "sret_taken") (.ref sppExt)
      (.ref privReg)))))

  emitAssign "priv_mode" (.ref privReg)

  -- =========================================================================
  -- CSR Address Match Signals
  -- =========================================================================
  let isSstatus ← makeWire "is_sstatus" .bit
  emitAssign isSstatus (.op .eq [csrAddr, .const csrSSTATUS 12])
  let isSie ← makeWire "is_sie" .bit
  emitAssign isSie (.op .eq [csrAddr, .const csrSIE 12])
  let isStvec ← makeWire "is_stvec" .bit
  emitAssign isStvec (.op .eq [csrAddr, .const csrSTVEC 12])
  let isSscratch ← makeWire "is_sscratch" .bit
  emitAssign isSscratch (.op .eq [csrAddr, .const csrSSCRATCH 12])
  let isSepc ← makeWire "is_sepc" .bit
  emitAssign isSepc (.op .eq [csrAddr, .const csrSEPC 12])
  let isScause ← makeWire "is_scause" .bit
  emitAssign isScause (.op .eq [csrAddr, .const csrSCAUSE 12])
  let isStval ← makeWire "is_stval" .bit
  emitAssign isStval (.op .eq [csrAddr, .const csrSTVAL 12])
  let isSip ← makeWire "is_sip" .bit
  emitAssign isSip (.op .eq [csrAddr, .const csrSIP 12])
  let isSatp ← makeWire "is_satp" .bit
  emitAssign isSatp (.op .eq [csrAddr, .const csrSATP 12])

  -- Combined hit signal
  let csrHit ← makeWire "scsr_hit" .bit
  emitAssign csrHit (.op .or [.ref isSstatus,
    .op .or [.ref isSie,
    .op .or [.ref isStvec,
    .op .or [.ref isSscratch,
    .op .or [.ref isSepc,
    .op .or [.ref isScause,
    .op .or [.ref isStval,
    .op .or [.ref isSip, .ref isSatp]]]]]]]])
  emitAssign "csr_hit" (.ref csrHit)

  -- =========================================================================
  -- CSR Write Value Computation (same as M-mode)
  -- =========================================================================
  let f3is1 ← makeWire "sf3_1" .bit
  emitAssign f3is1 (.op .eq [csrF3, .const 1 3])
  let f3is2 ← makeWire "sf3_2" .bit
  emitAssign f3is2 (.op .eq [csrF3, .const 2 3])
  let f3is3 ← makeWire "sf3_3" .bit
  emitAssign f3is3 (.op .eq [csrF3, .const 3 3])
  let f3is5 ← makeWire "sf3_5" .bit
  emitAssign f3is5 (.op .eq [csrF3, .const 5 3])
  let f3is6 ← makeWire "sf3_6" .bit
  emitAssign f3is6 (.op .eq [csrF3, .const 6 3])
  let f3is7 ← makeWire "sf3_7" .bit
  emitAssign f3is7 (.op .eq [csrF3, .const 7 3])

  let isRW ← makeWire "s_is_rw" .bit
  emitAssign isRW (.op .or [.ref f3is1, .ref f3is5])
  let isRS ← makeWire "s_is_rs" .bit
  emitAssign isRS (.op .or [.ref f3is2, .ref f3is6])
  let isRC ← makeWire "s_is_rc" .bit
  emitAssign isRC (.op .or [.ref f3is3, .ref f3is7])

  let csrDoWrite ← makeWire "s_csr_do_write" .bit
  emitAssign csrDoWrite (.op .and [csrWE, .op .or [.ref isRW, .op .or [.ref isRS, .ref isRC]]])

  -- =========================================================================
  -- S-mode CSR Registers
  -- =========================================================================

  -- SSTATUS: restricted view of mstatus
  -- sstatus exposes: SIE(1), SPIE(5), SPP(8), MXR(19), SUM(18)
  -- Mask for S-mode visible bits in mstatus
  let sstatusMask : Int := (1 <<< mstatusSIE) ||| (1 <<< mstatusSPIE) |||
    (1 <<< mstatusSPP) ||| (1 <<< mstatusMXR) ||| (1 <<< mstatusSUM)
  let sstatusView ← makeWire "sstatus_view" (.bitVector 32)
  emitAssign sstatusView (.op .and [.ref "mstatus_in", .const sstatusMask 32])

  -- Writing sstatus only modifies S-mode bits in mstatus
  let sstatusWr ← makeWire "sstatus_wr" .bit
  emitAssign sstatusWr (.op .and [.ref csrDoWrite, .ref isSstatus])

  -- Compute new sstatus write value
  let sstatusSetVal ← makeWire "sstatus_set_val" (.bitVector 32)
  emitAssign sstatusSetVal (.op .or [.ref sstatusView, csrWdata])
  let sstatusNotWdata ← makeWire "sstatus_not_wdata" (.bitVector 32)
  emitAssign sstatusNotWdata (.op .not [csrWdata])
  let sstatusClearVal ← makeWire "sstatus_clear_val" (.bitVector 32)
  emitAssign sstatusClearVal (.op .and [.ref sstatusView, .ref sstatusNotWdata])

  let sstatusNewVal ← makeWire "sstatus_new_val" (.bitVector 32)
  emitAssign sstatusNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref sstatusSetVal)
    (Expr.mux (.ref isRC) (.ref sstatusClearVal)
      csrWdata)))

  -- Merge new S-mode bits into mstatus (preserve M-mode bits)
  let mstatusNonS ← makeWire "mstatus_non_s" (.bitVector 32)
  emitAssign mstatusNonS (.op .and [.ref "mstatus_in",
    .const (0xFFFFFFFF - sstatusMask) 32])
  let sstatusMasked ← makeWire "sstatus_masked" (.bitVector 32)
  emitAssign sstatusMasked (.op .and [.ref sstatusNewVal, .const sstatusMask 32])
  let sstatusWdataOut ← makeWire "sstatus_wdata_out" (.bitVector 32)
  emitAssign sstatusWdataOut (.op .or [.ref mstatusNonS, .ref sstatusMasked])

  emitAssign "sstatus_write" (.ref sstatusWr)
  emitAssign "sstatus_wdata" (.ref sstatusWdataOut)

  -- SIE register (S-mode interrupt enable, restricted view of mie)
  let sieNext ← makeWire "sie_next" (.bitVector 32)
  let sieReg ← emitRegister "sie_reg" "clk" "rst" (.ref sieNext) 0 (.bitVector 32)
  let sieWr ← makeWire "sie_wr" .bit
  emitAssign sieWr (.op .and [.ref csrDoWrite, .ref isSie])

  -- CSR write value for sie
  let sieSetVal ← makeWire "sie_set_val" (.bitVector 32)
  emitAssign sieSetVal (.op .or [.ref sieReg, csrWdata])
  let sieNotWdata ← makeWire "sie_not_wdata" (.bitVector 32)
  emitAssign sieNotWdata (.op .not [csrWdata])
  let sieClearVal ← makeWire "sie_clear_val" (.bitVector 32)
  emitAssign sieClearVal (.op .and [.ref sieReg, .ref sieNotWdata])
  let sieNewVal ← makeWire "sie_new_val" (.bitVector 32)
  emitAssign sieNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref sieSetVal)
    (Expr.mux (.ref isRC) (.ref sieClearVal)
      csrWdata)))
  emitAssign sieNext (Expr.mux (.ref sieWr) (.ref sieNewVal) (.ref sieReg))

  -- STVEC register
  let stvecNext ← makeWire "stvec_next" (.bitVector 32)
  let stvecReg ← emitRegister "stvec_reg" "clk" "rst" (.ref stvecNext) 0 (.bitVector 32)
  let stvecWr ← makeWire "stvec_wr" .bit
  emitAssign stvecWr (.op .and [.ref csrDoWrite, .ref isStvec])
  let stvecSetVal ← makeWire "stvec_set_val" (.bitVector 32)
  emitAssign stvecSetVal (.op .or [.ref stvecReg, csrWdata])
  let stvecNotWdata ← makeWire "stvec_not_wdata" (.bitVector 32)
  emitAssign stvecNotWdata (.op .not [csrWdata])
  let stvecClearVal ← makeWire "stvec_clear_val" (.bitVector 32)
  emitAssign stvecClearVal (.op .and [.ref stvecReg, .ref stvecNotWdata])
  let stvecNewVal ← makeWire "stvec_new_val" (.bitVector 32)
  emitAssign stvecNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref stvecSetVal)
    (Expr.mux (.ref isRC) (.ref stvecClearVal)
      csrWdata)))
  emitAssign stvecNext (Expr.mux (.ref stvecWr) (.ref stvecNewVal) (.ref stvecReg))

  -- SSCRATCH register
  let sscratchNext ← makeWire "sscratch_next" (.bitVector 32)
  let sscratchReg ← emitRegister "sscratch_reg" "clk" "rst" (.ref sscratchNext) 0 (.bitVector 32)
  let sscratchWr ← makeWire "sscratch_wr" .bit
  emitAssign sscratchWr (.op .and [.ref csrDoWrite, .ref isSscratch])
  let sscratchSetVal ← makeWire "sscratch_set_val" (.bitVector 32)
  emitAssign sscratchSetVal (.op .or [.ref sscratchReg, csrWdata])
  let sscratchNotWdata ← makeWire "sscratch_not_wdata" (.bitVector 32)
  emitAssign sscratchNotWdata (.op .not [csrWdata])
  let sscratchClearVal ← makeWire "sscratch_clear_val" (.bitVector 32)
  emitAssign sscratchClearVal (.op .and [.ref sscratchReg, .ref sscratchNotWdata])
  let sscratchNewVal ← makeWire "sscratch_new_val" (.bitVector 32)
  emitAssign sscratchNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref sscratchSetVal)
    (Expr.mux (.ref isRC) (.ref sscratchClearVal)
      csrWdata)))
  emitAssign sscratchNext (Expr.mux (.ref sscratchWr) (.ref sscratchNewVal) (.ref sscratchReg))

  -- SEPC register (set on S-mode trap, writable via CSR)
  let sepcNext ← makeWire "sepc_next" (.bitVector 32)
  let sepcReg ← emitRegister "sepc_reg" "clk" "rst" (.ref sepcNext) 0 (.bitVector 32)
  let sepcWr ← makeWire "sepc_wr" .bit
  emitAssign sepcWr (.op .and [.ref csrDoWrite, .ref isSepc])
  let sepcSetVal ← makeWire "sepc_set_val" (.bitVector 32)
  emitAssign sepcSetVal (.op .or [.ref sepcReg, csrWdata])
  let sepcNotWdata ← makeWire "sepc_not_wdata" (.bitVector 32)
  emitAssign sepcNotWdata (.op .not [csrWdata])
  let sepcClearVal ← makeWire "sepc_clear_val" (.bitVector 32)
  emitAssign sepcClearVal (.op .and [.ref sepcReg, .ref sepcNotWdata])
  let sepcNewVal ← makeWire "sepc_new_val" (.bitVector 32)
  emitAssign sepcNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref sepcSetVal)
    (Expr.mux (.ref isRC) (.ref sepcClearVal)
      csrWdata)))
  emitAssign sepcNext
    (Expr.mux (.ref "trap_to_s") (.ref "trap_pc")
    (Expr.mux (.ref sepcWr) (.ref sepcNewVal)
      (.ref sepcReg)))

  -- SCAUSE register
  let scauseNext ← makeWire "scause_next" (.bitVector 32)
  let scauseReg ← emitRegister "scause_reg" "clk" "rst" (.ref scauseNext) 0 (.bitVector 32)
  let scauseWr ← makeWire "scause_wr" .bit
  emitAssign scauseWr (.op .and [.ref csrDoWrite, .ref isScause])
  let scauseSetVal ← makeWire "scause_set_val" (.bitVector 32)
  emitAssign scauseSetVal (.op .or [.ref scauseReg, csrWdata])
  let scauseNotWdata ← makeWire "scause_not_wdata" (.bitVector 32)
  emitAssign scauseNotWdata (.op .not [csrWdata])
  let scauseClearVal ← makeWire "scause_clear_val" (.bitVector 32)
  emitAssign scauseClearVal (.op .and [.ref scauseReg, .ref scauseNotWdata])
  let scauseNewVal ← makeWire "scause_new_val" (.bitVector 32)
  emitAssign scauseNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref scauseSetVal)
    (Expr.mux (.ref isRC) (.ref scauseClearVal)
      csrWdata)))
  emitAssign scauseNext
    (Expr.mux (.ref "trap_to_s") (.ref "trap_cause")
    (Expr.mux (.ref scauseWr) (.ref scauseNewVal)
      (.ref scauseReg)))

  -- STVAL register
  let stvalNext ← makeWire "stval_next" (.bitVector 32)
  let stvalReg ← emitRegister "stval_reg" "clk" "rst" (.ref stvalNext) 0 (.bitVector 32)
  let stvalWr ← makeWire "stval_wr" .bit
  emitAssign stvalWr (.op .and [.ref csrDoWrite, .ref isStval])
  let stvalSetVal ← makeWire "stval_set_val" (.bitVector 32)
  emitAssign stvalSetVal (.op .or [.ref stvalReg, csrWdata])
  let stvalNotWdata ← makeWire "stval_not_wdata" (.bitVector 32)
  emitAssign stvalNotWdata (.op .not [csrWdata])
  let stvalClearVal ← makeWire "stval_clear_val" (.bitVector 32)
  emitAssign stvalClearVal (.op .and [.ref stvalReg, .ref stvalNotWdata])
  let stvalNewVal ← makeWire "stval_new_val" (.bitVector 32)
  emitAssign stvalNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref stvalSetVal)
    (Expr.mux (.ref isRC) (.ref stvalClearVal)
      csrWdata)))
  emitAssign stvalNext
    (Expr.mux (.ref "trap_to_s") (.ref "trap_val")
    (Expr.mux (.ref stvalWr) (.ref stvalNewVal)
      (.ref stvalReg)))

  -- SIP register (restricted view of mip - read-only for S-mode)
  -- For now, just read zeros
  let sipVal ← makeWire "sip_val" (.bitVector 32)
  emitAssign sipVal (.const 0 32)

  -- SATP register (page table base + mode)
  let satpNext ← makeWire "satp_next" (.bitVector 32)
  let satpReg ← emitRegister "satp_reg" "clk" "rst" (.ref satpNext) 0 (.bitVector 32)
  let satpWr ← makeWire "satp_wr" .bit
  emitAssign satpWr (.op .and [.ref csrDoWrite, .ref isSatp])
  let satpSetVal ← makeWire "satp_set_val" (.bitVector 32)
  emitAssign satpSetVal (.op .or [.ref satpReg, csrWdata])
  let satpNotWdata ← makeWire "satp_not_wdata" (.bitVector 32)
  emitAssign satpNotWdata (.op .not [csrWdata])
  let satpClearVal ← makeWire "satp_clear_val" (.bitVector 32)
  emitAssign satpClearVal (.op .and [.ref satpReg, .ref satpNotWdata])
  let satpNewVal ← makeWire "satp_new_val" (.bitVector 32)
  emitAssign satpNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref satpSetVal)
    (Expr.mux (.ref isRC) (.ref satpClearVal)
      csrWdata)))
  emitAssign satpNext (Expr.mux (.ref satpWr) (.ref satpNewVal) (.ref satpReg))

  -- =========================================================================
  -- CSR Read Mux
  -- =========================================================================
  emitAssign "csr_rdata"
    (Expr.mux (.ref isSstatus) (.ref sstatusView)
    (Expr.mux (.ref isSie) (.ref sieReg)
    (Expr.mux (.ref isStvec) (.ref stvecReg)
    (Expr.mux (.ref isSscratch) (.ref sscratchReg)
    (Expr.mux (.ref isSepc) (.ref sepcReg)
    (Expr.mux (.ref isScause) (.ref scauseReg)
    (Expr.mux (.ref isStval) (.ref stvalReg)
    (Expr.mux (.ref isSip) (.ref sipVal)
    (Expr.mux (.ref isSatp) (.ref satpReg)
      (.const 0 32))))))))))

  -- Output ports
  emitAssign "stvec_out" (.ref stvecReg)
  emitAssign "sepc_out" (.ref sepcReg)
  emitAssign "satp_out" (.ref satpReg)

/-- Build the Supervisor CSR module -/
def buildSupervisorCSRs : Module :=
  CircuitM.runModule "RV32I_SupervisorCSRs" do
    generateSupervisorCSRs

end Sparkle.Examples.RV32.CSR.Supervisor
