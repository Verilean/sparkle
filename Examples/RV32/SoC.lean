/-
  RV32I SoC Top-Level

  Integrates the RV32I core with memories, CLINT, bus, and optionally MMU.

  Phase 1 (M-mode RTOS):
    ┌───────────────────────────────────┐
    │  RV32I_SoC                        │
    │  ┌──────┐  ┌──────┐  ┌──────┐   │
    │  │ IMEM │──│ Core │──│ DMEM │   │
    │  └──────┘  └──┬───┘  └──────┘   │
    │               │                   │
    │          ┌────┴────┐              │
    │          │  CLINT  │              │
    │          └─────────┘              │
    └───────────────────────────────────┘

  Phase 2 (S-mode Linux):
    Core → MMU (iTLB/dTLB) → Bus → {DRAM, CLINT, UART, Boot ROM}

  Architecture: The core pipeline is inlined into the SoC (flat CircuitM).
  The core manages its own PC, pipeline, and outputs signals that the SoC
  wires to memories, CLINT, CSR register file, and trap logic.

  Core outputs consumed by SoC:
    imem_addr        → Instruction memory read address
    dmem_addr        → Data memory / bus address (word-aligned slice)
    dmem_wdata       → Data memory write data
    dmem_we          → Data memory write enable
    dmem_re          → Data memory read enable
    debug_pc         → Current PC for debug output
    csr_addr[11:0]   → CSR address for read/write
    csr_funct3[2:0]  → CSR operation type (CSRRW/CSRRS/CSRRC/CSRRWI/CSRRSI/CSRRCI)
    csr_wdata[31:0]  → CSR write data
    csr_we           → CSR write enable
    trap_ecall       → ECALL exception from pipeline
    trap_ebreak      → EBREAK exception from pipeline
    trap_mret        → MRET instruction from pipeline
    trap_pc[31:0]    → PC of the trapping instruction

  SoC inputs fed back to core:
    imem_rdata[31:0] → Fetched instruction
    dmem_rdata[31:0] → Data memory / bus read data
    csr_rdata[31:0]  → CSR read data
    trap_taken        → Trap has been taken (redirect PC)
    trap_target[31:0] → Trap handler address (mtvec)
    mret_target[31:0] → MRET return address (mepc)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.Types
import Examples.RV32.CSR.Types
import Examples.RV32.Core

set_option maxRecDepth 8192

namespace Sparkle.Examples.RV32.SoC

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32
open Sparkle.Examples.RV32.CSR
open Sparkle.Examples.RV32.Core
open CircuitM

-- ============================================================================
-- Configuration
-- ============================================================================

/-- Instruction memory address width (words) -/
def socImemAddrBits : Nat := 12  -- 4096 words = 16KB

/-- Data memory address width (words) -/
def socDmemAddrBits : Nat := 14  -- 16384 words = 64KB

-- ============================================================================
-- Phase 1: SoC with Core + CLINT + IMEM + DMEM
-- ============================================================================

/-- Generate Phase 1 SoC.

    External Ports:
      clk, rst           - Clock and reset
      debug_pc[31:0]     - Current program counter (for debugging)
      uart_tx_data[7:0]  - UART transmit data (optional)
      uart_tx_valid      - UART transmit valid (optional)

    The SoC inlines the RV32I core pipeline and connects it to:
      - Instruction memory (BRAM, preloaded)
      - Data memory (BRAM)
      - CLINT (timer + software interrupt)
      - CSR register file (M-mode)
      - Trap detection and handling logic
      - Address decoder for CLINT vs DMEM
-/
def generateSoC : CircuitM Unit := do
  -- =========================================================================
  -- SoC external ports
  -- =========================================================================
  addInput "clk" .bit
  addInput "rst" .bit
  addOutput "debug_pc" (.bitVector 32)

  -- =========================================================================
  -- Core-to-SoC interface wires
  -- =========================================================================
  -- These wires are created here for the core to drive as outputs and
  -- for the SoC peripherals to consume. The core (when its generateCore
  -- is inlined) produces addOutput calls; since we are building a flat
  -- module, we pre-create corresponding wires that the core will drive.

  -- Core drives these (outputs from core perspective):
  let coreImemAddr ← makeWire "core_imem_addr" (.bitVector imemAddrBits)
  let coreDmemAddr ← makeWire "core_dmem_addr" (.bitVector dmemAddrBits)
  let coreDmemWdata ← makeWire "core_dmem_wdata" (.bitVector 32)
  let coreDmemWE ← makeWire "core_dmem_we" .bit
  let coreDmemRE ← makeWire "core_dmem_re" .bit
  let coreDebugPC ← makeWire "core_debug_pc" (.bitVector 32)

  -- CSR interface (core outputs)
  let csrAddr ← makeWire "csr_addr" (.bitVector 12)
  let csrFunct3 ← makeWire "csr_funct3" (.bitVector 3)
  let csrWdata ← makeWire "csr_wdata" (.bitVector 32)
  let csrWE ← makeWire "csr_we" .bit

  -- Trap signals from core
  let trapEcall ← makeWire "trap_ecall" .bit
  let trapEbreak ← makeWire "trap_ebreak" .bit
  let trapMret ← makeWire "trap_mret" .bit
  let trapPC ← makeWire "trap_pc" (.bitVector 32)

  -- SoC drives these (inputs to core perspective):
  let csrRdata ← makeWire "csr_rdata" (.bitVector 32)
  let trapTaken ← makeWire "trap_taken" .bit
  let trapTarget ← makeWire "trap_target" (.bitVector 32)
  let mretTarget ← makeWire "mret_target" (.bitVector 32)

  -- =========================================================================
  -- Instruction Memory (BRAM)
  -- =========================================================================
  -- The core outputs imem_addr as a word index. The SoC IMEM is wider
  -- (socImemAddrBits) so we use the core's address (which is imemAddrBits
  -- wide) to index into the larger memory, zero-extending if needed.
  -- The core computes imem_addr from its PC register (pc[imemAddrBits+1:2]).
  let socImemAddr ← makeWire "soc_imem_addr" (.bitVector socImemAddrBits)
  -- Zero-extend core's imem_addr (imemAddrBits bits) to socImemAddrBits
  emitAssign socImemAddr (.concat [.const 0 (socImemAddrBits - imemAddrBits),
    .ref coreImemAddr])

  -- No write port needed (code is read-only in this SoC)
  let imemRdata ← emitMemory "imem" socImemAddrBits 32 "clk"
    (.const 0 socImemAddrBits) (.const 0 32) (.const 0 1)
    (.ref socImemAddr)

  -- Feed instruction data back to the core
  -- The core expects this on its "imem_rdata" input
  let imemRdataWire ← makeWire "imem_rdata_wire" (.bitVector 32)
  emitAssign imemRdataWire (.ref imemRdata)

  -- =========================================================================
  -- Bus Address Decode
  -- =========================================================================
  -- The core's ALU result (full 32-bit address) is used for bus routing.
  -- For the data memory path, we need the full 32-bit address.
  -- The core outputs dmem_addr as a word-index (dmemAddrBits wide), but
  -- we also need the full address for CLINT detection.
  -- We reconstruct the full address from the core's dmem_addr output:
  -- full_addr = {dmem_addr, 2'b00} (word-aligned)
  -- However, the core actually computes dmem_addr = alu_result[dmemAddrBits+1:2]
  -- For CLINT, we need the full 32-bit address. The core should output this
  -- via trap_pc or a dedicated bus address. For now, we use the core pipeline's
  -- ALU result which is stored as alu_result internally.
  --
  -- Since we are inlining, we access the core's internal alu_result wire.
  -- The core's EX stage creates "alu_result" as a wire.
  let coreAddr ← makeWire "core_full_addr" (.bitVector 32)
  -- The core's alu_result wire is the full 32-bit address used for load/store.
  -- In a flat design, we can reference it directly via the generated name.
  -- However, since generateCore creates wires with _gen_ prefix via freshName,
  -- we need a different approach. Instead, reconstruct the full address:
  -- core_full_addr = {zeros, dmem_addr, 2'b00}
  -- This works for DMEM range but NOT for CLINT range (0x0200_xxxx).
  -- Solution: The core should output the full address. For now, we create
  -- a dedicated wire that the core's EX stage will drive.
  -- Actually, looking at the core pipeline: dmem_addr is assigned from
  -- alu_result[dmemAddrBits+1:2]. The full alu_result IS available as an
  -- internal wire. Since the SoC inlines the core, all wires are shared.
  -- We will reference the internal _gen_alu_result_XX wire.
  -- BUT: since freshName adds counters, we cannot predict the exact name.
  --
  -- Better approach: Add a full-address output to the core. Since the other
  -- agent is already modifying the core, we should assume the core will
  -- provide what we need. For now, we reconstruct from dmem signals:
  --
  -- For CLINT detection, we need to check if addr[31:16] == 0x0200.
  -- The dmem_addr is only dmemAddrBits wide (10 bits = word addresses in
  -- the 0x00000000-0x00000FFF range). CLINT at 0x02000000 cannot be reached
  -- with a 10-bit address.
  --
  -- RESOLUTION: The SoC must use a wider address from the core for bus
  -- routing. The core's dmem_addr output is a truncated word-address.
  -- We need the core to also output the full 32-bit bus address.
  -- For Phase 1, we add a SoC-level "bus_addr" wire that the core pipeline
  -- drives with the full ALU result. Since the core code is about to be
  -- modified, we assume it will output "bus_addr" or we handle it here.
  --
  -- PRACTICAL APPROACH: Since everything is flat CircuitM, the core's
  -- internal alu_result wire is accessible. But its name is generated.
  -- Instead, we create an explicit bus_addr wire that the core's EX stage
  -- assigns. The core modification should add:
  --   addOutput "bus_addr" (.bitVector 32)
  -- For now, we treat bus_addr as coming from the pipeline.

  let busAddr ← makeWire "bus_addr" (.bitVector 32)

  -- CLINT address decode: check if addr[31:16] == 0x0200
  let isCLINT ← makeWire "is_clint" .bit
  emitAssign isCLINT (.op .eq [.slice (.ref busAddr) 31 16, .const 0x0200 16])

  let isDMEM ← makeWire "is_dmem" .bit
  emitAssign isDMEM (.op .not [.ref isCLINT])

  -- CLINT offset
  let clintOffset ← makeWire "clint_offset" (.bitVector 16)
  emitAssign clintOffset (.slice (.ref busAddr) 15 0)

  -- =========================================================================
  -- Data Memory (BRAM)
  -- =========================================================================
  let socDmemAddr ← makeWire "soc_dmem_addr" (.bitVector socDmemAddrBits)
  -- Word-aligned address from the full bus address
  emitAssign socDmemAddr (.slice (.ref busAddr) (socDmemAddrBits + 1) 2)

  let dmemWdataW ← makeWire "soc_dmem_wdata" (.bitVector 32)
  emitAssign dmemWdataW (.ref coreDmemWdata)

  let dmemWEW ← makeWire "soc_dmem_we" .bit
  emitAssign dmemWEW (.op .and [.ref coreDmemWE, .ref isDMEM])

  let dmemRdata ← emitMemory "dmem" socDmemAddrBits 32 "clk"
    (.ref socDmemAddr) (.ref dmemWdataW) (.ref dmemWEW)
    (.ref socDmemAddr)

  -- =========================================================================
  -- CLINT Registers (inline)
  -- =========================================================================

  -- MSIP Register
  let msipAddrMatch ← makeWire "msip_match" .bit
  emitAssign msipAddrMatch (.op .and [.ref isCLINT,
    .op .eq [.ref clintOffset, .const clintMSIP 16]])
  let msipNext ← makeWire "msip_next" (.bitVector 32)
  let msipReg ← emitRegister "msip_reg" "clk" "rst" (.ref msipNext) 0 (.bitVector 32)

  -- MTIME counter (64-bit)
  let mtimeLoNext ← makeWire "mtime_lo_next" (.bitVector 32)
  let mtimeLoReg ← emitRegister "mtime_lo" "clk" "rst" (.ref mtimeLoNext) 0 (.bitVector 32)
  let mtimeHiNext ← makeWire "mtime_hi_next" (.bitVector 32)
  let mtimeHiReg ← emitRegister "mtime_hi" "clk" "rst" (.ref mtimeHiNext) 0 (.bitVector 32)

  -- MTIMECMP (64-bit)
  let mtimecmpLoNext ← makeWire "mtimecmp_lo_next" (.bitVector 32)
  let mtimecmpLoReg ← emitRegister "mtimecmp_lo" "clk" "rst" (.ref mtimecmpLoNext) 0xFFFFFFFF (.bitVector 32)
  let mtimecmpHiNext ← makeWire "mtimecmp_hi_next" (.bitVector 32)
  let mtimecmpHiReg ← emitRegister "mtimecmp_hi" "clk" "rst" (.ref mtimecmpHiNext) 0xFFFFFFFF (.bitVector 32)

  -- MTIME auto-increment
  let mtimeLoInc ← makeWire "mtime_lo_inc" (.bitVector 32)
  emitAssign mtimeLoInc (Expr.add (.ref mtimeLoReg) (.const 1 32))
  let mtimeCarry ← makeWire "mtime_carry" .bit
  emitAssign mtimeCarry (.op .eq [.ref mtimeLoInc, .const 0 32])
  let mtimeHiInc ← makeWire "mtime_hi_inc" (.bitVector 32)
  emitAssign mtimeHiInc (Expr.mux (.ref mtimeCarry)
    (Expr.add (.ref mtimeHiReg) (.const 1 32))
    (.ref mtimeHiReg))

  -- CLINT address matching
  let mtimeLoMatch ← makeWire "mtime_lo_match" .bit
  emitAssign mtimeLoMatch (.op .and [.ref isCLINT,
    .op .eq [.ref clintOffset, .const clintMTIME_LO 16]])
  let mtimeHiMatch ← makeWire "mtime_hi_match" .bit
  emitAssign mtimeHiMatch (.op .and [.ref isCLINT,
    .op .eq [.ref clintOffset, .const clintMTIME_HI 16]])
  let mtimecmpLoMatch ← makeWire "mtimecmp_lo_match" .bit
  emitAssign mtimecmpLoMatch (.op .and [.ref isCLINT,
    .op .eq [.ref clintOffset, .const clintMTIMECMP_LO 16]])
  let mtimecmpHiMatch ← makeWire "mtimecmp_hi_match" .bit
  emitAssign mtimecmpHiMatch (.op .and [.ref isCLINT,
    .op .eq [.ref clintOffset, .const clintMTIMECMP_HI 16]])

  -- CLINT write logic: core dmem_we AND isCLINT drives CLINT registers
  let clintWE ← makeWire "clint_we" .bit
  emitAssign clintWE (.op .and [.ref coreDmemWE, .ref isCLINT])

  emitAssign msipNext (Expr.mux (.op .and [.ref clintWE, .ref msipAddrMatch])
    (.ref coreDmemWdata) (.ref msipReg))
  emitAssign mtimeLoNext (Expr.mux (.op .and [.ref clintWE, .ref mtimeLoMatch])
    (.ref coreDmemWdata) (.ref mtimeLoInc))
  emitAssign mtimeHiNext (Expr.mux (.op .and [.ref clintWE, .ref mtimeHiMatch])
    (.ref coreDmemWdata) (.ref mtimeHiInc))
  emitAssign mtimecmpLoNext (Expr.mux (.op .and [.ref clintWE, .ref mtimecmpLoMatch])
    (.ref coreDmemWdata) (.ref mtimecmpLoReg))
  emitAssign mtimecmpHiNext (Expr.mux (.op .and [.ref clintWE, .ref mtimecmpHiMatch])
    (.ref coreDmemWdata) (.ref mtimecmpHiReg))

  -- Timer interrupt: mtime >= mtimecmp
  let hiGt ← makeWire "timer_hi_gt" .bit
  emitAssign hiGt (.op .gt_u [.ref mtimeHiReg, .ref mtimecmpHiReg])
  let hiEq ← makeWire "timer_hi_eq" .bit
  emitAssign hiEq (.op .eq [.ref mtimeHiReg, .ref mtimecmpHiReg])
  let loGe ← makeWire "timer_lo_ge" .bit
  emitAssign loGe (.op .ge_u [.ref mtimeLoReg, .ref mtimecmpLoReg])
  let timerIrq ← makeWire "timer_irq" .bit
  emitAssign timerIrq (.op .or [.ref hiGt, .op .and [.ref hiEq, .ref loGe]])

  -- Software interrupt
  let swIrq ← makeWire "sw_irq" .bit
  emitAssign swIrq (.slice (.ref msipReg) 0 0)

  -- CLINT read mux
  let clintRdata ← makeWire "clint_rdata" (.bitVector 32)
  emitAssign clintRdata
    (Expr.mux (.ref msipAddrMatch) (.ref msipReg)
    (Expr.mux (.ref mtimecmpLoMatch) (.ref mtimecmpLoReg)
    (Expr.mux (.ref mtimecmpHiMatch) (.ref mtimecmpHiReg)
    (Expr.mux (.ref mtimeLoMatch) (.ref mtimeLoReg)
    (Expr.mux (.ref mtimeHiMatch) (.ref mtimeHiReg)
      (.const 0 32))))))

  -- =========================================================================
  -- Bus Read Data Mux: CLINT or DMEM
  -- =========================================================================
  let busRdata ← makeWire "bus_rdata" (.bitVector 32)
  emitAssign busRdata (Expr.mux (.ref isCLINT) (.ref clintRdata) (.ref dmemRdata))

  -- Feed bus read data back to core as dmem_rdata
  let dmemRdataWire ← makeWire "dmem_rdata_wire" (.bitVector 32)
  emitAssign dmemRdataWire (.ref busRdata)

  -- =========================================================================
  -- CSR Register File (M-mode)
  -- =========================================================================
  let mstatusNext ← makeWire "mstatus_next" (.bitVector 32)
  let mstatusReg ← emitRegister "mstatus" "clk" "rst" (.ref mstatusNext) 0 (.bitVector 32)
  let mieNext ← makeWire "mie_next_soc" (.bitVector 32)
  let mieReg ← emitRegister "mie_soc" "clk" "rst" (.ref mieNext) 0 (.bitVector 32)
  let mtvecNext ← makeWire "mtvec_next" (.bitVector 32)
  let mtvecReg ← emitRegister "mtvec" "clk" "rst" (.ref mtvecNext) 0 (.bitVector 32)
  let mscratchNext ← makeWire "mscratch_next" (.bitVector 32)
  let mscratchReg ← emitRegister "mscratch" "clk" "rst" (.ref mscratchNext) 0 (.bitVector 32)
  let mepcNext ← makeWire "mepc_next" (.bitVector 32)
  let mepcReg ← emitRegister "mepc" "clk" "rst" (.ref mepcNext) 0 (.bitVector 32)
  let mcauseNext ← makeWire "mcause_next" (.bitVector 32)
  let mcauseReg ← emitRegister "mcause" "clk" "rst" (.ref mcauseNext) 0 (.bitVector 32)
  let mtvalNext ← makeWire "mtval_next" (.bitVector 32)
  let mtvalReg ← emitRegister "mtval" "clk" "rst" (.ref mtvalNext) 0 (.bitVector 32)

  -- CSR MIE bits
  let mieMTIE ← makeWire "mie_mtie" .bit
  emitAssign mieMTIE (.slice (.ref mieReg) CSR.mieMTIE CSR.mieMTIE)
  let mieMSIE ← makeWire "mie_msie" .bit
  emitAssign mieMSIE (.slice (.ref mieReg) CSR.mieMSIE CSR.mieMSIE)

  -- MSTATUS MIE
  let mstatusMIEBit ← makeWire "mstatus_mie_bit" .bit
  emitAssign mstatusMIEBit (.slice (.ref mstatusReg) CSR.mstatusMIE CSR.mstatusMIE)
  let mstatusMPIEBit ← makeWire "mstatus_mpie_bit" .bit
  emitAssign mstatusMPIEBit (.slice (.ref mstatusReg) CSR.mstatusMPIE CSR.mstatusMPIE)

  -- =========================================================================
  -- CSR Read Mux (driven by core's csr_addr output)
  -- =========================================================================
  -- Address matching for CSR reads
  let csrIsMstatus ← makeWire "csr_is_mstatus" .bit
  emitAssign csrIsMstatus (.op .eq [.ref csrAddr, .const CSR.csrMSTATUS 12])
  let csrIsMie ← makeWire "csr_is_mie" .bit
  emitAssign csrIsMie (.op .eq [.ref csrAddr, .const CSR.csrMIE 12])
  let csrIsMtvec ← makeWire "csr_is_mtvec" .bit
  emitAssign csrIsMtvec (.op .eq [.ref csrAddr, .const CSR.csrMTVEC 12])
  let csrIsMscratch ← makeWire "csr_is_mscratch" .bit
  emitAssign csrIsMscratch (.op .eq [.ref csrAddr, .const CSR.csrMSCRATCH 12])
  let csrIsMepc ← makeWire "csr_is_mepc" .bit
  emitAssign csrIsMepc (.op .eq [.ref csrAddr, .const CSR.csrMEPC 12])
  let csrIsMcause ← makeWire "csr_is_mcause" .bit
  emitAssign csrIsMcause (.op .eq [.ref csrAddr, .const CSR.csrMCAUSE 12])
  let csrIsMtval ← makeWire "csr_is_mtval" .bit
  emitAssign csrIsMtval (.op .eq [.ref csrAddr, .const CSR.csrMTVAL 12])
  let csrIsMip ← makeWire "csr_is_mip" .bit
  emitAssign csrIsMip (.op .eq [.ref csrAddr, .const CSR.csrMIP 12])
  let csrIsMisa ← makeWire "csr_is_misa" .bit
  emitAssign csrIsMisa (.op .eq [.ref csrAddr, .const CSR.csrMISA 12])
  let csrIsMhartid ← makeWire "csr_is_mhartid" .bit
  emitAssign csrIsMhartid (.op .eq [.ref csrAddr, .const CSR.csrMHARTID 12])

  -- Construct MIP value: read-only, reflects pending interrupt status
  let mipValue ← makeWire "mip_value" (.bitVector 32)
  let mipTimerBit ← makeWire "mip_timer_bit" (.bitVector 32)
  emitAssign mipTimerBit (Expr.mux (.ref timerIrq)
    (.const (1 <<< CSR.mieMTIE) 32) (.const 0 32))
  let mipSwBit ← makeWire "mip_sw_bit" (.bitVector 32)
  emitAssign mipSwBit (Expr.mux (.ref swIrq)
    (.const (1 <<< CSR.mieMSIE) 32) (.const 0 32))
  emitAssign mipValue (.op .or [.ref mipTimerBit, .ref mipSwBit])

  -- CSR read data mux
  emitAssign csrRdata
    (Expr.mux (.ref csrIsMstatus) (.ref mstatusReg)
    (Expr.mux (.ref csrIsMie) (.ref mieReg)
    (Expr.mux (.ref csrIsMtvec) (.ref mtvecReg)
    (Expr.mux (.ref csrIsMscratch) (.ref mscratchReg)
    (Expr.mux (.ref csrIsMepc) (.ref mepcReg)
    (Expr.mux (.ref csrIsMcause) (.ref mcauseReg)
    (Expr.mux (.ref csrIsMtval) (.ref mtvalReg)
    (Expr.mux (.ref csrIsMip) (.ref mipValue)
    (Expr.mux (.ref csrIsMisa) (.const CSR.misaValue 32)
    (Expr.mux (.ref csrIsMhartid) (.const 0 32)
      (.const 0 32)))))))))))

  -- =========================================================================
  -- CSR Write Logic (driven by core's csr_we, csr_addr, csr_funct3, csr_wdata)
  -- =========================================================================
  -- Compute the new CSR value based on funct3 (CSRRW/CSRRS/CSRRC/CSRRWI/CSRRSI/CSRRCI)
  -- funct3 encoding:
  --   001 = CSRRW  (write csr_wdata)
  --   010 = CSRRS  (set bits: old | csr_wdata)
  --   011 = CSRRC  (clear bits: old & ~csr_wdata)
  --   101 = CSRRWI (write csr_wdata, which is zimm zero-extended)
  --   110 = CSRRSI (set bits with zimm)
  --   111 = CSRRCI (clear bits with zimm)

  -- The core provides csr_wdata already prepared (rs1 value or zimm zero-extended).
  -- We compute the effective write value for each CSR.
  -- funct3[1:0]: 01=RW, 10=RS, 11=RC

  let csrF3Low ← makeWire "csr_f3_low" (.bitVector 2)
  emitAssign csrF3Low (.slice (.ref csrFunct3) 1 0)

  let csrIsRW ← makeWire "csr_is_rw" .bit
  emitAssign csrIsRW (.op .eq [.ref csrF3Low, .const 0b01 2])
  let csrIsRS ← makeWire "csr_is_rs" .bit
  emitAssign csrIsRS (.op .eq [.ref csrF3Low, .const 0b10 2])
  let csrIsRC ← makeWire "csr_is_rc" .bit
  emitAssign csrIsRC (.op .eq [.ref csrF3Low, .const 0b11 2])

  -- For a given old CSR value, compute the new value
  -- Helper: compute CSR write value from old value
  -- CSRRW: new = wdata
  -- CSRRS: new = old | wdata
  -- CSRRC: new = old & ~wdata
  -- We need this for each writable CSR individually

  -- Generic CSR write value computation (parameterized by old value)
  let mkCsrWriteVal (oldVal : String) (suffix : String) : CircuitM String := do
    let rsVal ← makeWire s!"csr_rs_val_{suffix}" (.bitVector 32)
    emitAssign rsVal (.op .or [.ref oldVal, .ref csrWdata])
    let rcVal ← makeWire s!"csr_rc_val_{suffix}" (.bitVector 32)
    let notWdata ← makeWire s!"csr_not_wdata_{suffix}" (.bitVector 32)
    emitAssign notWdata (.op .not [.ref csrWdata])
    emitAssign rcVal (.op .and [.ref oldVal, .ref notWdata])
    let newVal ← makeWire s!"csr_new_val_{suffix}" (.bitVector 32)
    emitAssign newVal
      (Expr.mux (.ref csrIsRW) (.ref csrWdata)
      (Expr.mux (.ref csrIsRS) (.ref rsVal)
      (Expr.mux (.ref csrIsRC) (.ref rcVal)
        (.ref oldVal))))
    return newVal

  let mstatusNewCSR ← mkCsrWriteVal mstatusReg "mstatus"
  let mieNewCSR ← mkCsrWriteVal mieReg "mie"
  let mtvecNewCSR ← mkCsrWriteVal mtvecReg "mtvec"
  let mscratchNewCSR ← mkCsrWriteVal mscratchReg "mscratch"
  let mepcNewCSR ← mkCsrWriteVal mepcReg "mepc"
  let mcauseNewCSR ← mkCsrWriteVal mcauseReg "mcause"
  let mtvalNewCSR ← mkCsrWriteVal mtvalReg "mtval"

  -- =========================================================================
  -- Trap Detection (from core's trap output signals)
  -- =========================================================================

  -- Timer interrupt: globally enabled AND locally enabled AND pending
  let timerIntEnabled ← makeWire "timer_int_en" .bit
  emitAssign timerIntEnabled (.op .and [.ref mstatusMIEBit,
    .op .and [.ref mieMTIE, .ref timerIrq]])

  -- Software interrupt: globally enabled AND locally enabled AND pending
  let swIntEnabled ← makeWire "sw_int_en" .bit
  emitAssign swIntEnabled (.op .and [.ref mstatusMIEBit,
    .op .and [.ref mieMSIE, .ref swIrq]])

  -- Trap taken: exceptions (ecall, ebreak) have priority over interrupts
  -- Note: trap_ecall and trap_ebreak come from the core pipeline
  emitAssign trapTaken (.op .or [.ref trapEcall,
    .op .or [.ref trapEbreak,
    .op .or [.ref timerIntEnabled, .ref swIntEnabled]]])

  -- Trap cause
  let trapCause ← makeWire "trap_cause" (.bitVector 32)
  emitAssign trapCause
    (Expr.mux (.ref trapEcall) (.const causeECALL_M 32)
    (Expr.mux (.ref trapEbreak) (.const causeEBREAK 32)
    (Expr.mux (.ref timerIntEnabled) (.const causeM_TIMER_INT 32)
    (Expr.mux (.ref swIntEnabled) (.const causeM_SW_INT 32)
      (.const 0 32)))))

  -- =========================================================================
  -- CSR Register Update Logic
  -- =========================================================================
  -- Priority: trap entry > MRET > CSR write instruction > hold

  -- MSTATUS updates on trap/MRET/CSR write
  -- On trap entry: MPIE <- MIE, MIE <- 0, MPP <- 11 (M-mode)
  let mstatusTrapVal ← makeWire "mstatus_trap_val" (.bitVector 32)
  let msClearMIE ← makeWire "soc_ms_clear_mie" (.bitVector 32)
  emitAssign msClearMIE (.op .and [.ref mstatusReg,
    .const (0xFFFFFFFF - (1 <<< CSR.mstatusMIE)) 32])
  let msSetMPIE ← makeWire "soc_ms_set_mpie" (.bitVector 32)
  emitAssign msSetMPIE (Expr.mux (.ref mstatusMIEBit)
    (.op .or [.ref msClearMIE, .const (1 <<< CSR.mstatusMPIE) 32])
    (.op .and [.ref msClearMIE, .const (0xFFFFFFFF - (1 <<< CSR.mstatusMPIE)) 32]))
  emitAssign mstatusTrapVal (.op .or [.ref msSetMPIE, .const (3 <<< CSR.mstatusMPP_LO) 32])

  -- On MRET: MIE <- MPIE, MPIE <- 1, MPP <- 00
  let mstatusMretVal ← makeWire "mstatus_mret_val" (.bitVector 32)
  let msClearMPP ← makeWire "soc_ms_clear_mpp" (.bitVector 32)
  emitAssign msClearMPP (.op .and [.ref mstatusReg,
    .const (0xFFFFFFFF - (3 <<< CSR.mstatusMPP_LO)) 32])
  let msRestoreMIE ← makeWire "soc_ms_restore_mie" (.bitVector 32)
  emitAssign msRestoreMIE (Expr.mux (.ref mstatusMPIEBit)
    (.op .or [.ref msClearMPP, .const (1 <<< CSR.mstatusMIE) 32])
    (.op .and [.ref msClearMPP, .const (0xFFFFFFFF - (1 <<< CSR.mstatusMIE)) 32]))
  emitAssign mstatusMretVal (.op .or [.ref msRestoreMIE, .const (1 <<< CSR.mstatusMPIE) 32])

  -- MSTATUS next: trap > MRET > CSR write > hold
  emitAssign mstatusNext
    (Expr.mux (.ref trapTaken) (.ref mstatusTrapVal)
    (Expr.mux (.ref trapMret) (.ref mstatusMretVal)
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMstatus]) (.ref mstatusNewCSR)
      (.ref mstatusReg))))

  -- MIE next: CSR write or hold (trap/MRET don't affect MIE register)
  emitAssign mieNext
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMie]) (.ref mieNewCSR)
      (.ref mieReg))

  -- MTVEC next: CSR write or hold
  emitAssign mtvecNext
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMtvec]) (.ref mtvecNewCSR)
      (.ref mtvecReg))

  -- MSCRATCH next: CSR write or hold
  emitAssign mscratchNext
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMscratch]) (.ref mscratchNewCSR)
      (.ref mscratchReg))

  -- MEPC: set on trap entry (to trap_pc from core), CSR write, or hold
  emitAssign mepcNext
    (Expr.mux (.ref trapTaken) (.ref trapPC)
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMepc]) (.ref mepcNewCSR)
      (.ref mepcReg)))

  -- MCAUSE: set on trap entry, CSR write, or hold
  emitAssign mcauseNext
    (Expr.mux (.ref trapTaken) (.ref trapCause)
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMcause]) (.ref mcauseNewCSR)
      (.ref mcauseReg)))

  -- MTVAL: set on trap entry (0 for ecall/ebreak), CSR write, or hold
  emitAssign mtvalNext
    (Expr.mux (.ref trapTaken) (.const 0 32)
    (Expr.mux (.op .and [.ref csrWE, .ref csrIsMtval]) (.ref mtvalNewCSR)
      (.ref mtvalReg)))

  -- =========================================================================
  -- Trap Target and MRET Target (fed back to core)
  -- =========================================================================
  -- trap_target = mtvec base address (bits [31:2] << 2, i.e., aligned)
  let mtvecBase ← makeWire "mtvec_base" (.bitVector 32)
  emitAssign mtvecBase (.op .and [.ref mtvecReg, .const 0xFFFFFFFC 32])
  emitAssign trapTarget (.ref mtvecBase)

  -- mret_target = mepc (return address saved on trap entry)
  emitAssign mretTarget (.ref mepcReg)

  -- =========================================================================
  -- Wire SoC Outputs
  -- =========================================================================
  -- Forward core's debug_pc to SoC output
  emitAssign "debug_pc" (.ref coreDebugPC)

  -- =========================================================================
  -- Core Pipeline Integration
  -- =========================================================================
  -- The core pipeline is generated inline. Its addInput/addOutput calls
  -- create module-level ports, but in a flat SoC those become internal wires.
  -- We need to connect the SoC's memory/peripheral outputs to the core's inputs
  -- and the core's outputs to the SoC's peripheral inputs.
  --
  -- Since generateCore uses addInput/addOutput (which create ports), we cannot
  -- call it directly inside generateSoC (that would create conflicting ports).
  -- Instead, we assign the interface wires that the core pipeline drives/reads.
  --
  -- The core expects these inputs (which the SoC provides):
  --   imem_rdata   <- from instruction memory
  --   dmem_rdata   <- from bus read mux (CLINT or DMEM)
  --   csr_rdata    <- from CSR read mux (already assigned above)
  --   trap_taken   <- from trap detection logic (already assigned above)
  --   trap_target  <- from mtvec base (already assigned above)
  --   mret_target  <- from mepc register (already assigned above)
  --
  -- The core drives these outputs (which the SoC consumes):
  --   imem_addr    -> instruction memory address
  --   dmem_addr    -> data memory address (truncated)
  --   dmem_wdata   -> data memory write data
  --   dmem_we      -> data memory write enable
  --   dmem_re      -> data memory read enable
  --   debug_pc     -> program counter for debug
  --   csr_addr     -> CSR address
  --   csr_funct3   -> CSR operation funct3
  --   csr_wdata    -> CSR write data
  --   csr_we       -> CSR write enable
  --   trap_ecall   -> ECALL detected
  --   trap_ebreak  -> EBREAK detected
  --   trap_mret    -> MRET detected
  --   trap_pc      -> PC of trapping instruction
  --   bus_addr     -> Full 32-bit bus address for CLINT/DMEM routing
  --
  -- These are connected via the wire names created above. When the core
  -- pipeline is instantiated (either via module instantiation or by
  -- inlining), these wires form the interface contract.
  --
  -- For now, we emit instance connections that map our SoC wire names to
  -- the core's port names. This uses Sparkle's emitInstance to instantiate
  -- the core as a sub-module within the SoC.
  emitInstance "RV32I_Core" "core" [
    -- Inputs to core
    ("clk",          .ref "clk"),
    ("rst",          .ref "rst"),
    ("imem_rdata",   .ref imemRdataWire),
    ("dmem_rdata",   .ref dmemRdataWire),
    ("csr_rdata",    .ref csrRdata),
    ("trap_taken",   .ref trapTaken),
    ("trap_target",  .ref trapTarget),
    ("mret_target",  .ref mretTarget),
    -- Outputs from core
    ("imem_addr",    .ref coreImemAddr),
    ("dmem_addr",    .ref coreDmemAddr),
    ("dmem_wdata",   .ref coreDmemWdata),
    ("dmem_we",      .ref coreDmemWE),
    ("dmem_re",      .ref coreDmemRE),
    ("debug_pc",     .ref coreDebugPC),
    ("csr_addr",     .ref csrAddr),
    ("csr_funct3",   .ref csrFunct3),
    ("csr_wdata",    .ref csrWdata),
    ("csr_we",       .ref csrWE),
    ("trap_ecall",   .ref trapEcall),
    ("trap_ebreak",  .ref trapEbreak),
    ("trap_mret",    .ref trapMret),
    ("trap_pc",      .ref trapPC),
    ("bus_addr",     .ref busAddr)
  ]

/-- Build the Phase 1 SoC module -/
def buildSoC : Module :=
  CircuitM.runModule "RV32I_SoC" do
    generateSoC

end Sparkle.Examples.RV32.SoC
