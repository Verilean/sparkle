/-
  Trap Delegation Logic

  Extends trap handling for M→S delegation using medeleg/mideleg registers.
  When a trap cause bit is set in medeleg/mideleg and the current privilege
  is ≤ S, the trap is routed to the S-mode handler instead of M-mode.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.Trap

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- Generate the trap delegation unit.

    Inputs:
      clk, rst
      -- Delegation registers (writable via CSR interface)
      csr_addr[11:0]     - CSR address for medeleg/mideleg writes
      csr_wdata[31:0]    - CSR write data
      csr_we             - CSR write enable
      csr_funct3[2:0]    - CSR operation type
      -- Trap info
      trap_valid         - A trap is being taken
      trap_cause[31:0]   - Trap cause code (bit 31 = interrupt)
      priv_mode[1:0]     - Current privilege mode
      -- Trap vector addresses
      mtvec[31:0]        - M-mode trap vector
      stvec[31:0]        - S-mode trap vector
      -- Return addresses
      mepc[31:0]         - M-mode exception PC
      sepc[31:0]         - S-mode exception PC

    Outputs:
      trap_to_m          - Trap should go to M-mode
      trap_to_s          - Trap should go to S-mode
      trap_target[31:0]  - Trap handler address
      -- Delegation register read values
      medeleg_out[31:0]  - Exception delegation register
      mideleg_out[31:0]  - Interrupt delegation register
      -- CSR read
      deleg_rdata[31:0]  - Read data for medeleg/mideleg
      deleg_hit          - Address matched medeleg/mideleg
-/
def generateTrapDelegation : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "csr_addr" (.bitVector 12)
  addInput "csr_wdata" (.bitVector 32)
  addInput "csr_we" .bit
  addInput "csr_funct3" (.bitVector 3)
  addInput "trap_valid" .bit
  addInput "trap_cause" (.bitVector 32)
  addInput "priv_mode" (.bitVector 2)
  addInput "mtvec" (.bitVector 32)
  addInput "stvec" (.bitVector 32)
  addInput "mepc" (.bitVector 32)
  addInput "sepc" (.bitVector 32)

  addOutput "trap_to_m" .bit
  addOutput "trap_to_s" .bit
  addOutput "trap_target" (.bitVector 32)
  addOutput "medeleg_out" (.bitVector 32)
  addOutput "mideleg_out" (.bitVector 32)
  addOutput "deleg_rdata" (.bitVector 32)
  addOutput "deleg_hit" .bit

  let csrAddr := Expr.ref "csr_addr"
  let csrWdata := Expr.ref "csr_wdata"

  -- =========================================================================
  -- CSR Write Logic
  -- =========================================================================
  let csrF3 := Expr.ref "csr_funct3"
  let f3is1 ← makeWire "df3_1" .bit
  emitAssign f3is1 (.op .eq [csrF3, .const 1 3])
  let f3is2 ← makeWire "df3_2" .bit
  emitAssign f3is2 (.op .eq [csrF3, .const 2 3])
  let f3is3 ← makeWire "df3_3" .bit
  emitAssign f3is3 (.op .eq [csrF3, .const 3 3])
  let f3is5 ← makeWire "df3_5" .bit
  emitAssign f3is5 (.op .eq [csrF3, .const 5 3])
  let f3is6 ← makeWire "df3_6" .bit
  emitAssign f3is6 (.op .eq [csrF3, .const 6 3])
  let f3is7 ← makeWire "df3_7" .bit
  emitAssign f3is7 (.op .eq [csrF3, .const 7 3])
  let isRW ← makeWire "d_is_rw" .bit
  emitAssign isRW (.op .or [.ref f3is1, .ref f3is5])
  let isRS ← makeWire "d_is_rs" .bit
  emitAssign isRS (.op .or [.ref f3is2, .ref f3is6])
  let isRC ← makeWire "d_is_rc" .bit
  emitAssign isRC (.op .or [.ref f3is3, .ref f3is7])
  let dDoWrite ← makeWire "d_do_write" .bit
  emitAssign dDoWrite (.op .and [.ref "csr_we",
    .op .or [.ref isRW, .op .or [.ref isRS, .ref isRC]]])

  -- =========================================================================
  -- MEDELEG Register
  -- =========================================================================
  let isMedeleg ← makeWire "is_medeleg" .bit
  emitAssign isMedeleg (.op .eq [csrAddr, .const csrMEDELEG 12])

  let medelegNext ← makeWire "medeleg_next" (.bitVector 32)
  let medelegReg ← emitRegister "medeleg_reg" "clk" "rst" (.ref medelegNext) 0 (.bitVector 32)

  let medelegSetVal ← makeWire "medeleg_set" (.bitVector 32)
  emitAssign medelegSetVal (.op .or [.ref medelegReg, csrWdata])
  let medelegNotWdata ← makeWire "medeleg_notw" (.bitVector 32)
  emitAssign medelegNotWdata (.op .not [csrWdata])
  let medelegClearVal ← makeWire "medeleg_clear" (.bitVector 32)
  emitAssign medelegClearVal (.op .and [.ref medelegReg, .ref medelegNotWdata])

  let medelegNewVal ← makeWire "medeleg_new" (.bitVector 32)
  emitAssign medelegNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref medelegSetVal)
    (Expr.mux (.ref isRC) (.ref medelegClearVal)
      csrWdata)))

  let medelegWr ← makeWire "medeleg_wr" .bit
  emitAssign medelegWr (.op .and [.ref dDoWrite, .ref isMedeleg])
  emitAssign medelegNext (Expr.mux (.ref medelegWr) (.ref medelegNewVal) (.ref medelegReg))
  emitAssign "medeleg_out" (.ref medelegReg)

  -- =========================================================================
  -- MIDELEG Register
  -- =========================================================================
  let isMideleg ← makeWire "is_mideleg" .bit
  emitAssign isMideleg (.op .eq [csrAddr, .const csrMIDELEG 12])

  let midelegNext ← makeWire "mideleg_next" (.bitVector 32)
  let midelegReg ← emitRegister "mideleg_reg" "clk" "rst" (.ref midelegNext) 0 (.bitVector 32)

  let midelegSetVal ← makeWire "mideleg_set" (.bitVector 32)
  emitAssign midelegSetVal (.op .or [.ref midelegReg, csrWdata])
  let midelegNotWdata ← makeWire "mideleg_notw" (.bitVector 32)
  emitAssign midelegNotWdata (.op .not [csrWdata])
  let midelegClearVal ← makeWire "mideleg_clear" (.bitVector 32)
  emitAssign midelegClearVal (.op .and [.ref midelegReg, .ref midelegNotWdata])

  let midelegNewVal ← makeWire "mideleg_new" (.bitVector 32)
  emitAssign midelegNewVal
    (Expr.mux (.ref isRW) csrWdata
    (Expr.mux (.ref isRS) (.ref midelegSetVal)
    (Expr.mux (.ref isRC) (.ref midelegClearVal)
      csrWdata)))

  let midelegWr ← makeWire "mideleg_wr" .bit
  emitAssign midelegWr (.op .and [.ref dDoWrite, .ref isMideleg])
  emitAssign midelegNext (Expr.mux (.ref midelegWr) (.ref midelegNewVal) (.ref midelegReg))
  emitAssign "mideleg_out" (.ref midelegReg)

  -- CSR read hit
  let delegHit ← makeWire "deleg_csr_hit" .bit
  emitAssign delegHit (.op .or [.ref isMedeleg, .ref isMideleg])
  emitAssign "deleg_hit" (.ref delegHit)
  emitAssign "deleg_rdata"
    (Expr.mux (.ref isMedeleg) (.ref medelegReg)
    (Expr.mux (.ref isMideleg) (.ref midelegReg)
      (.const 0 32)))

  -- =========================================================================
  -- Delegation Decision
  -- =========================================================================
  -- Is this an interrupt? (bit 31 set)
  let isInterrupt ← makeWire "is_interrupt" .bit
  emitAssign isInterrupt (.slice (.ref "trap_cause") 31 31)

  -- Extract cause index (bits [4:0], sufficient for standard causes)
  let causeIdx ← makeWire "cause_idx" (.bitVector 5)
  emitAssign causeIdx (.slice (.ref "trap_cause") 4 0)

  -- Check delegation bit
  -- For exceptions: check medeleg[cause]
  -- For interrupts: check mideleg[cause]
  -- We use a shift-and-mask approach: (deleg_reg >> cause_idx) & 1
  let causeIdxExt ← makeWire "cause_idx_ext" (.bitVector 32)
  emitAssign causeIdxExt (.concat [.const 0 27, .ref causeIdx])

  let medelegShifted ← makeWire "medeleg_shifted" (.bitVector 32)
  emitAssign medelegShifted (.op .shr [.ref medelegReg, .ref causeIdxExt])
  let medelegBit ← makeWire "medeleg_bit" .bit
  emitAssign medelegBit (.slice (.ref medelegShifted) 0 0)

  let midelegShifted ← makeWire "mideleg_shifted" (.bitVector 32)
  emitAssign midelegShifted (.op .shr [.ref midelegReg, .ref causeIdxExt])
  let midelegBit ← makeWire "mideleg_bit" .bit
  emitAssign midelegBit (.slice (.ref midelegShifted) 0 0)

  -- Select delegation bit based on interrupt/exception
  let delegated ← makeWire "delegated" .bit
  emitAssign delegated (Expr.mux (.ref isInterrupt) (.ref midelegBit) (.ref medelegBit))

  -- Trap goes to S-mode if: delegated AND current_priv ≤ S
  let privLeS ← makeWire "priv_le_s" .bit
  emitAssign privLeS (.op .le_u [.ref "priv_mode", .const privS 2])

  let toSmode ← makeWire "to_smode" .bit
  emitAssign toSmode (.op .and [.ref "trap_valid",
    .op .and [.ref delegated, .ref privLeS]])

  let toMmode ← makeWire "to_mmode" .bit
  emitAssign toMmode (.op .and [.ref "trap_valid", .op .not [.ref toSmode]])

  emitAssign "trap_to_m" (.ref toMmode)
  emitAssign "trap_to_s" (.ref toSmode)

  -- =========================================================================
  -- Trap Target Address
  -- =========================================================================
  -- Direct mode (tvec[1:0]=00): PC = tvec_base
  -- Vectored mode (tvec[1:0]=01): PC = tvec_base + 4*cause (interrupts only)
  -- For simplicity, we support direct mode only for now
  let trapTarget ← makeWire "trap_target_w" (.bitVector 32)
  -- Clear bottom 2 bits of tvec for base address
  let mtvecBase ← makeWire "mtvec_base" (.bitVector 32)
  emitAssign mtvecBase (.op .and [.ref "mtvec", .const 0xFFFFFFFC 32])
  let stvecBase ← makeWire "stvec_base" (.bitVector 32)
  emitAssign stvecBase (.op .and [.ref "stvec", .const 0xFFFFFFFC 32])

  emitAssign trapTarget
    (Expr.mux (.ref toSmode) (.ref stvecBase) (.ref mtvecBase))
  emitAssign "trap_target" (.ref trapTarget)

/-- Build the trap delegation module -/
def buildTrapDelegation : Module :=
  CircuitM.runModule "RV32I_TrapDelegation" do
    generateTrapDelegation

end Sparkle.Examples.RV32.Trap
