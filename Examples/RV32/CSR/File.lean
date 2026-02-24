/-
  RV32I CSR Register File

  Implements M-mode CSR registers with read/write/trap logic.
  Each CSR is an individual register (emitRegister).
  Supports CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI operations,
  trap entry (writing mepc, mcause, mtval, mstatus), and MRET.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192

namespace Sparkle.Examples.RV32.CSR.File

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- Generate the M-mode CSR register file.

    Inputs:
      clk, rst
      csr_addr[11:0]     - CSR address to read/write
      csr_funct3[2:0]    - CSR operation type
      csr_wdata[31:0]    - Write data (rs1 value or zimm)
      csr_we             - CSR write enable (from pipeline valid)
      -- Trap entry signals
      trap_taken         - Trap entry strobe
      trap_cause[31:0]   - Cause code for trap
      trap_pc[31:0]      - PC of trapping instruction
      trap_val[31:0]     - Trap value (faulting address, etc.)
      -- MRET signal
      mret_taken         - MRET strobe
      -- External interrupt pending
      ext_timer_irq      - Timer interrupt from CLINT
      ext_sw_irq         - Software interrupt from CLINT

    Outputs:
      csr_rdata[31:0]    - CSR read data
      mtvec_out[31:0]    - Trap vector base (for PC redirect)
      mepc_out[31:0]     - Exception PC (for MRET return)
      mstatus_mie        - Global M-mode interrupt enable
      mie_mtie           - Timer interrupt enable
      mie_msie           - Software interrupt enable
      mip_mtip           - Timer interrupt pending
      mip_msip           - Software interrupt pending
-/
def generateCSRFile : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "csr_addr" (.bitVector 12)
  addInput "csr_funct3" (.bitVector 3)
  addInput "csr_wdata" (.bitVector 32)
  addInput "csr_we" .bit
  addInput "trap_taken" .bit
  addInput "trap_cause" (.bitVector 32)
  addInput "trap_pc" (.bitVector 32)
  addInput "trap_val" (.bitVector 32)
  addInput "mret_taken" .bit
  addInput "ext_timer_irq" .bit
  addInput "ext_sw_irq" .bit

  addOutput "csr_rdata" (.bitVector 32)
  addOutput "mtvec_out" (.bitVector 32)
  addOutput "mepc_out" (.bitVector 32)
  addOutput "mstatus_mie" .bit
  addOutput "mie_mtie" .bit
  addOutput "mie_msie" .bit
  addOutput "mip_mtip" .bit
  addOutput "mip_msip" .bit

  let csrAddr := Expr.ref "csr_addr"
  let csrF3 := Expr.ref "csr_funct3"
  let csrWdata := Expr.ref "csr_wdata"
  let csrWE := Expr.ref "csr_we"

  -- =========================================================================
  -- CSR Address Match Signals
  -- =========================================================================
  let isMstatus ← makeWire "is_mstatus" .bit
  emitAssign isMstatus (.op .eq [csrAddr, .const csrMSTATUS 12])
  let isMie ← makeWire "is_mie" .bit
  emitAssign isMie (.op .eq [csrAddr, .const csrMIE 12])
  let isMtvec ← makeWire "is_mtvec" .bit
  emitAssign isMtvec (.op .eq [csrAddr, .const csrMTVEC 12])
  let isMscratch ← makeWire "is_mscratch" .bit
  emitAssign isMscratch (.op .eq [csrAddr, .const csrMSCRATCH 12])
  let isMepc ← makeWire "is_mepc" .bit
  emitAssign isMepc (.op .eq [csrAddr, .const csrMEPC 12])
  let isMcause ← makeWire "is_mcause" .bit
  emitAssign isMcause (.op .eq [csrAddr, .const csrMCAUSE 12])
  let isMtval ← makeWire "is_mtval" .bit
  emitAssign isMtval (.op .eq [csrAddr, .const csrMTVAL 12])
  let isMip ← makeWire "is_mip" .bit
  emitAssign isMip (.op .eq [csrAddr, .const csrMIP 12])
  let isMisa ← makeWire "is_misa" .bit
  emitAssign isMisa (.op .eq [csrAddr, .const csrMISA 12])
  let isMhartid ← makeWire "is_mhartid" .bit
  emitAssign isMhartid (.op .eq [csrAddr, .const csrMHARTID 12])

  -- =========================================================================
  -- CSR Write Value Computation
  -- =========================================================================
  -- funct3: 001=CSRRW, 010=CSRRS, 011=CSRRC, 101=CSRRWI, 110=CSRRSI, 111=CSRRCI
  -- For RS/RC operations, we need the current CSR value
  -- We'll compute the write value after reading current values

  let f3is1 ← makeWire "csr_f3_1" .bit
  emitAssign f3is1 (.op .eq [csrF3, .const 1 3])
  let f3is2 ← makeWire "csr_f3_2" .bit
  emitAssign f3is2 (.op .eq [csrF3, .const 2 3])
  let f3is3 ← makeWire "csr_f3_3" .bit
  emitAssign f3is3 (.op .eq [csrF3, .const 3 3])
  let f3is5 ← makeWire "csr_f3_5" .bit
  emitAssign f3is5 (.op .eq [csrF3, .const 5 3])
  let f3is6 ← makeWire "csr_f3_6" .bit
  emitAssign f3is6 (.op .eq [csrF3, .const 6 3])
  let f3is7 ← makeWire "csr_f3_7" .bit
  emitAssign f3is7 (.op .eq [csrF3, .const 7 3])

  -- CSRRW/CSRRWI: write value = wdata
  let isRW ← makeWire "is_rw" .bit
  emitAssign isRW (.op .or [.ref f3is1, .ref f3is5])
  -- CSRRS/CSRRSI: write value = current | wdata (set bits)
  let isRS ← makeWire "is_rs" .bit
  emitAssign isRS (.op .or [.ref f3is2, .ref f3is6])
  -- CSRRC/CSRRCI: write value = current & ~wdata (clear bits)
  let isRC ← makeWire "is_rc" .bit
  emitAssign isRC (.op .or [.ref f3is3, .ref f3is7])

  -- =========================================================================
  -- CSR Registers
  -- =========================================================================

  -- MSTATUS register
  -- Fields: MIE (bit 3), MPIE (bit 7), MPP (bits 12:11)
  -- On trap: MPIE←MIE, MIE←0, MPP←current_priv (always M=11 for now)
  -- On MRET: MIE←MPIE, MPIE←1, MPP←U (00)
  let mstatusNext ← makeWire "mstatus_next" (.bitVector 32)
  let mstatusReg ← emitRegister "mstatus_reg" "clk" "rst" (.ref mstatusNext) 0 (.bitVector 32)

  -- Current MIE and MPIE bits
  let curMIE ← makeWire "cur_mie" .bit
  emitAssign curMIE (.slice (.ref mstatusReg) mstatusMIE mstatusMIE)
  let curMPIE ← makeWire "cur_mpie" .bit
  emitAssign curMPIE (.slice (.ref mstatusReg) mstatusMPIE mstatusMPIE)

  -- MIE register
  let mieNext ← makeWire "mie_next" (.bitVector 32)
  let mieReg ← emitRegister "mie_reg" "clk" "rst" (.ref mieNext) 0 (.bitVector 32)

  -- MTVEC register
  let mtvecNext ← makeWire "mtvec_next" (.bitVector 32)
  let mtvecReg ← emitRegister "mtvec_reg" "clk" "rst" (.ref mtvecNext) 0 (.bitVector 32)

  -- MSCRATCH register
  let mscratchNext ← makeWire "mscratch_next" (.bitVector 32)
  let mscratchReg ← emitRegister "mscratch_reg" "clk" "rst" (.ref mscratchNext) 0 (.bitVector 32)

  -- MEPC register
  let mepcNext ← makeWire "mepc_next" (.bitVector 32)
  let mepcReg ← emitRegister "mepc_reg" "clk" "rst" (.ref mepcNext) 0 (.bitVector 32)

  -- MCAUSE register
  let mcauseNext ← makeWire "mcause_next" (.bitVector 32)
  let mcauseReg ← emitRegister "mcause_reg" "clk" "rst" (.ref mcauseNext) 0 (.bitVector 32)

  -- MTVAL register
  let mtvalNext ← makeWire "mtval_next" (.bitVector 32)
  let mtvalReg ← emitRegister "mtval_reg" "clk" "rst" (.ref mtvalNext) 0 (.bitVector 32)

  -- MIP register (mostly read-only, driven by external interrupts)
  -- MIP.MTIP = ext_timer_irq, MIP.MSIP = ext_sw_irq
  let mipVal ← makeWire "mip_val" (.bitVector 32)
  -- Construct MIP: bit 7 = MTIP, bit 3 = MSIP
  let mipMtipBit ← makeWire "mip_mtip_bit" (.bitVector 32)
  emitAssign mipMtipBit (Expr.mux (.ref "ext_timer_irq")
    (.const (1 <<< mieMTIE) 32) (.const 0 32))
  let mipMsipBit ← makeWire "mip_msip_bit" (.bitVector 32)
  emitAssign mipMsipBit (Expr.mux (.ref "ext_sw_irq")
    (.const (1 <<< mieMSIE) 32) (.const 0 32))
  emitAssign mipVal (.op .or [.ref mipMtipBit, .ref mipMsipBit])

  -- =========================================================================
  -- CSR Read Mux
  -- =========================================================================
  let csrReadVal ← makeWire "csr_read_val" (.bitVector 32)
  emitAssign csrReadVal
    (Expr.mux (.ref isMstatus) (.ref mstatusReg)
    (Expr.mux (.ref isMisa) (.const misaValue 32)
    (Expr.mux (.ref isMie) (.ref mieReg)
    (Expr.mux (.ref isMtvec) (.ref mtvecReg)
    (Expr.mux (.ref isMscratch) (.ref mscratchReg)
    (Expr.mux (.ref isMepc) (.ref mepcReg)
    (Expr.mux (.ref isMcause) (.ref mcauseReg)
    (Expr.mux (.ref isMtval) (.ref mtvalReg)
    (Expr.mux (.ref isMip) (.ref mipVal)
    (Expr.mux (.ref isMhartid) (.const 0 32)
      (.const 0 32)))))))))))

  emitAssign "csr_rdata" (.ref csrReadVal)

  -- =========================================================================
  -- CSR Write Value (depends on read value)
  -- =========================================================================
  -- set_val = current | wdata
  let setVal ← makeWire "csr_set_val" (.bitVector 32)
  emitAssign setVal (.op .or [.ref csrReadVal, csrWdata])

  -- clear_val = current & ~wdata
  let notWdata ← makeWire "csr_not_wdata" (.bitVector 32)
  emitAssign notWdata (.op .not [csrWdata])
  let clearVal ← makeWire "csr_clear_val" (.bitVector 32)
  emitAssign clearVal (.op .and [.ref csrReadVal, .ref notWdata])

  -- Final write value: RW→wdata, RS→set, RC→clear
  let csrNewVal ← makeWire "csr_new_val" (.bitVector 32)
  emitAssign csrNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref setVal)
    (Expr.mux (.ref isRC) (.ref clearVal)
      csrWdata)))

  -- Write enable for each CSR
  let csrDoWrite ← makeWire "csr_do_write" .bit
  emitAssign csrDoWrite (.op .and [csrWE, .op .or [.ref isRW, .op .or [.ref isRS, .ref isRC]]])

  -- =========================================================================
  -- MSTATUS Update Logic
  -- =========================================================================
  -- Priority: trap > mret > csr_write > hold
  -- On trap: MPIE←MIE, MIE←0, MPP←11 (M-mode)
  let mstatusTrap ← makeWire "mstatus_trap" (.bitVector 32)
  -- Build trapped mstatus: clear MIE (bit 3), set MPIE (bit 7) to old MIE,
  -- set MPP (bits 12:11) to 11 (M-mode)
  -- Start from current mstatus
  let msClearMIE ← makeWire "ms_clear_mie" (.bitVector 32)
  emitAssign msClearMIE (.op .and [.ref mstatusReg,
    .const (0xFFFFFFFF - (1 <<< mstatusMIE)) 32])  -- clear bit 3
  let msSetMPIE ← makeWire "ms_set_mpie" (.bitVector 32)
  emitAssign msSetMPIE (Expr.mux (.ref curMIE)
    (.op .or [.ref msClearMIE, .const (1 <<< mstatusMPIE) 32])  -- set MPIE if MIE was 1
    (.op .and [.ref msClearMIE, .const (0xFFFFFFFF - (1 <<< mstatusMPIE)) 32]))  -- clear MPIE if MIE was 0
  let msSetMPP ← makeWire "ms_set_mpp" (.bitVector 32)
  emitAssign msSetMPP (.op .or [.ref msSetMPIE, .const (3 <<< mstatusMPP_LO) 32])  -- MPP = 11
  emitAssign mstatusTrap (.ref msSetMPP)

  -- On MRET: MIE←MPIE, MPIE←1, MPP←00
  let mstatusMret ← makeWire "mstatus_mret" (.bitVector 32)
  -- Clear MPP bits
  let msClearMPP ← makeWire "ms_clear_mpp" (.bitVector 32)
  emitAssign msClearMPP (.op .and [.ref mstatusReg,
    .const (0xFFFFFFFF - (3 <<< mstatusMPP_LO)) 32])
  -- Set MIE to old MPIE value
  let msRestoreMIE ← makeWire "ms_restore_mie" (.bitVector 32)
  emitAssign msRestoreMIE (Expr.mux (.ref curMPIE)
    (.op .or [.ref msClearMPP, .const (1 <<< mstatusMIE) 32])
    (.op .and [.ref msClearMPP, .const (0xFFFFFFFF - (1 <<< mstatusMIE)) 32]))
  -- Set MPIE to 1
  let msSetMPIE1 ← makeWire "ms_set_mpie1" (.bitVector 32)
  emitAssign msSetMPIE1 (.op .or [.ref msRestoreMIE, .const (1 <<< mstatusMPIE) 32])
  emitAssign mstatusMret (.ref msSetMPIE1)

  -- CSR write to mstatus
  let mstatusCSRWrite ← makeWire "mstatus_csr_wr" .bit
  emitAssign mstatusCSRWrite (.op .and [.ref csrDoWrite, .ref isMstatus])

  emitAssign mstatusNext
    (Expr.mux (.ref "trap_taken") (.ref mstatusTrap)
    (Expr.mux (.ref "mret_taken") (.ref mstatusMret)
    (Expr.mux (.ref mstatusCSRWrite) (.ref csrNewVal)
      (.ref mstatusReg))))

  -- =========================================================================
  -- MIE Update Logic
  -- =========================================================================
  let mieCSRWrite ← makeWire "mie_csr_wr" .bit
  emitAssign mieCSRWrite (.op .and [.ref csrDoWrite, .ref isMie])
  emitAssign mieNext
    (Expr.mux (.ref mieCSRWrite) (.ref csrNewVal) (.ref mieReg))

  -- =========================================================================
  -- MTVEC Update Logic
  -- =========================================================================
  let mtvecCSRWrite ← makeWire "mtvec_csr_wr" .bit
  emitAssign mtvecCSRWrite (.op .and [.ref csrDoWrite, .ref isMtvec])
  emitAssign mtvecNext
    (Expr.mux (.ref mtvecCSRWrite) (.ref csrNewVal) (.ref mtvecReg))

  -- =========================================================================
  -- MSCRATCH Update Logic
  -- =========================================================================
  let mscratchCSRWrite ← makeWire "mscratch_csr_wr" .bit
  emitAssign mscratchCSRWrite (.op .and [.ref csrDoWrite, .ref isMscratch])
  emitAssign mscratchNext
    (Expr.mux (.ref mscratchCSRWrite) (.ref csrNewVal) (.ref mscratchReg))

  -- =========================================================================
  -- MEPC Update Logic
  -- Priority: trap > csr_write > hold
  -- =========================================================================
  let mepcCSRWrite ← makeWire "mepc_csr_wr" .bit
  emitAssign mepcCSRWrite (.op .and [.ref csrDoWrite, .ref isMepc])
  emitAssign mepcNext
    (Expr.mux (.ref "trap_taken") (.ref "trap_pc")
    (Expr.mux (.ref mepcCSRWrite) (.ref csrNewVal)
      (.ref mepcReg)))

  -- =========================================================================
  -- MCAUSE Update Logic
  -- =========================================================================
  let mcauseCSRWrite ← makeWire "mcause_csr_wr" .bit
  emitAssign mcauseCSRWrite (.op .and [.ref csrDoWrite, .ref isMcause])
  emitAssign mcauseNext
    (Expr.mux (.ref "trap_taken") (.ref "trap_cause")
    (Expr.mux (.ref mcauseCSRWrite) (.ref csrNewVal)
      (.ref mcauseReg)))

  -- =========================================================================
  -- MTVAL Update Logic
  -- =========================================================================
  let mtvalCSRWrite ← makeWire "mtval_csr_wr" .bit
  emitAssign mtvalCSRWrite (.op .and [.ref csrDoWrite, .ref isMtval])
  emitAssign mtvalNext
    (Expr.mux (.ref "trap_taken") (.ref "trap_val")
    (Expr.mux (.ref mtvalCSRWrite) (.ref csrNewVal)
      (.ref mtvalReg)))

  -- =========================================================================
  -- Output Ports
  -- =========================================================================
  emitAssign "mtvec_out" (.ref mtvecReg)
  emitAssign "mepc_out" (.ref mepcReg)
  emitAssign "mstatus_mie" (.ref curMIE)
  emitAssign "mie_mtie" (.slice (.ref mieReg) mieMTIE mieMTIE)
  emitAssign "mie_msie" (.slice (.ref mieReg) mieMSIE mieMSIE)
  emitAssign "mip_mtip" (.slice (.ref mipVal) mieMTIE mieMTIE)
  emitAssign "mip_msip" (.slice (.ref mipVal) mieMSIE mieMSIE)

/-- Build the CSR file module -/
def buildCSRFile : Module :=
  CircuitM.runModule "RV32I_CSRFile" do
    generateCSRFile

end Sparkle.Examples.RV32.CSR.File
