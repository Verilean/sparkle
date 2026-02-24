/-
  CLINT (Core Local Interruptor)

  Memory-mapped timer and software interrupt controller.
  Base address: 0x02000000

  Register Map:
    0x0000       MSIP        - Software interrupt pending (bit 0)
    0x4000-4004  MTIMECMP    - Timer compare (64-bit)
    0xBFF8-BFFC  MTIME       - Timer counter (64-bit)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.CLINT

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- Generate the CLINT module.

    Inputs:
      clk, rst           - Clock and reset
      bus_addr[15:0]      - Bus address (offset from CLINT base)
      bus_wdata[31:0]     - Bus write data
      bus_we              - Bus write enable
      bus_re              - Bus read enable

    Outputs:
      bus_rdata[31:0]     - Bus read data
      timer_irq           - Timer interrupt (mtime >= mtimecmp)
      sw_irq              - Software interrupt (msip[0])
-/
def generateCLINT : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "bus_addr" (.bitVector 16)
  addInput "bus_wdata" (.bitVector 32)
  addInput "bus_we" .bit
  addInput "bus_re" .bit
  addOutput "bus_rdata" (.bitVector 32)
  addOutput "timer_irq" .bit
  addOutput "sw_irq" .bit

  let addr := Expr.ref "bus_addr"
  let wdata := Expr.ref "bus_wdata"
  let we := Expr.ref "bus_we"

  -- =========================================================================
  -- MSIP Register (1 bit, at offset 0x0000)
  -- =========================================================================
  let msipAddrMatch ← makeWire "msip_addr_match" .bit
  emitAssign msipAddrMatch (.op .eq [addr, .const clintMSIP 16])

  let msipWE ← makeWire "msip_we" .bit
  emitAssign msipWE (.op .and [we, .ref msipAddrMatch])

  let msipNext ← makeWire "msip_next" (.bitVector 32)
  let msipReg ← emitRegister "msip" "clk" "rst" (.ref msipNext) 0 (.bitVector 32)
  emitAssign msipNext (Expr.mux (.ref msipWE) wdata (.ref msipReg))

  -- Software interrupt = msip[0]
  emitAssign "sw_irq" (.slice (.ref msipReg) 0 0)

  -- =========================================================================
  -- MTIME Counter (64-bit, two 32-bit registers, increments every cycle)
  -- =========================================================================

  -- Address matching for MTIME writes
  let mtimeLoAddrMatch ← makeWire "mtime_lo_addr" .bit
  emitAssign mtimeLoAddrMatch (.op .eq [addr, .const clintMTIME_LO 16])
  let mtimeHiAddrMatch ← makeWire "mtime_hi_addr" .bit
  emitAssign mtimeHiAddrMatch (.op .eq [addr, .const clintMTIME_HI 16])

  let mtimeLoWE ← makeWire "mtime_lo_we" .bit
  emitAssign mtimeLoWE (.op .and [we, .ref mtimeLoAddrMatch])
  let mtimeHiWE ← makeWire "mtime_hi_we" .bit
  emitAssign mtimeHiWE (.op .and [we, .ref mtimeHiAddrMatch])

  -- Increment logic: mtime_lo + 1, carry to mtime_hi
  let mtimeLoNext ← makeWire "mtime_lo_next" (.bitVector 32)
  let mtimeHiNext ← makeWire "mtime_hi_next" (.bitVector 32)

  let mtimeLoReg ← emitRegister "mtime_lo" "clk" "rst" (.ref mtimeLoNext) 0 (.bitVector 32)
  let mtimeHiReg ← emitRegister "mtime_hi" "clk" "rst" (.ref mtimeHiNext) 0 (.bitVector 32)

  -- Increment: lo + 1
  let mtimeLoInc ← makeWire "mtime_lo_inc" (.bitVector 32)
  emitAssign mtimeLoInc (Expr.add (.ref mtimeLoReg) (.const 1 32))

  -- Carry: lo_inc == 0 means overflow
  let mtimeCarry ← makeWire "mtime_carry" .bit
  emitAssign mtimeCarry (.op .eq [.ref mtimeLoInc, .const 0 32])

  -- Hi increment
  let mtimeHiInc ← makeWire "mtime_hi_inc" (.bitVector 32)
  emitAssign mtimeHiInc (Expr.mux (.ref mtimeCarry)
    (Expr.add (.ref mtimeHiReg) (.const 1 32))
    (.ref mtimeHiReg))

  -- Mux: write takes priority over increment
  emitAssign mtimeLoNext (Expr.mux (.ref mtimeLoWE) wdata (.ref mtimeLoInc))
  emitAssign mtimeHiNext (Expr.mux (.ref mtimeHiWE) wdata (.ref mtimeHiInc))

  -- =========================================================================
  -- MTIMECMP Register (64-bit, two 32-bit registers)
  -- =========================================================================
  let mtimecmpLoAddrMatch ← makeWire "mtimecmp_lo_addr" .bit
  emitAssign mtimecmpLoAddrMatch (.op .eq [addr, .const clintMTIMECMP_LO 16])
  let mtimecmpHiAddrMatch ← makeWire "mtimecmp_hi_addr" .bit
  emitAssign mtimecmpHiAddrMatch (.op .eq [addr, .const clintMTIMECMP_HI 16])

  let mtimecmpLoWE ← makeWire "mtimecmp_lo_we" .bit
  emitAssign mtimecmpLoWE (.op .and [we, .ref mtimecmpLoAddrMatch])
  let mtimecmpHiWE ← makeWire "mtimecmp_hi_we" .bit
  emitAssign mtimecmpHiWE (.op .and [we, .ref mtimecmpHiAddrMatch])

  let mtimecmpLoNext ← makeWire "mtimecmp_lo_next" (.bitVector 32)
  let mtimecmpHiNext ← makeWire "mtimecmp_hi_next" (.bitVector 32)

  let mtimecmpLoReg ← emitRegister "mtimecmp_lo" "clk" "rst" (.ref mtimecmpLoNext) 0xFFFFFFFF (.bitVector 32)
  let mtimecmpHiReg ← emitRegister "mtimecmp_hi" "clk" "rst" (.ref mtimecmpHiNext) 0xFFFFFFFF (.bitVector 32)

  emitAssign mtimecmpLoNext (Expr.mux (.ref mtimecmpLoWE) wdata (.ref mtimecmpLoReg))
  emitAssign mtimecmpHiNext (Expr.mux (.ref mtimecmpHiWE) wdata (.ref mtimecmpHiReg))

  -- =========================================================================
  -- Timer Interrupt: mtime >= mtimecmp (unsigned 64-bit comparison)
  -- =========================================================================
  -- Compare high words first, then low words
  let hiGt ← makeWire "hi_gt" .bit
  emitAssign hiGt (.op .gt_u [.ref mtimeHiReg, .ref mtimecmpHiReg])
  let hiEq ← makeWire "hi_eq" .bit
  emitAssign hiEq (.op .eq [.ref mtimeHiReg, .ref mtimecmpHiReg])
  let loGe ← makeWire "lo_ge" .bit
  emitAssign loGe (.op .ge_u [.ref mtimeLoReg, .ref mtimecmpLoReg])

  -- timer_irq = hi_gt || (hi_eq && lo_ge)
  let hiEqLoGe ← makeWire "hi_eq_lo_ge" .bit
  emitAssign hiEqLoGe (.op .and [.ref hiEq, .ref loGe])
  emitAssign "timer_irq" (.op .or [.ref hiGt, .ref hiEqLoGe])

  -- =========================================================================
  -- Bus Read Mux
  -- =========================================================================
  let rdMsip ← makeWire "rd_msip" (.bitVector 32)
  emitAssign rdMsip (.ref msipReg)

  -- Read mux: select based on address
  emitAssign "bus_rdata"
    (Expr.mux (.ref msipAddrMatch) (.ref rdMsip)
    (Expr.mux (.ref mtimecmpLoAddrMatch) (.ref mtimecmpLoReg)
    (Expr.mux (.ref mtimecmpHiAddrMatch) (.ref mtimecmpHiReg)
    (Expr.mux (.ref mtimeLoAddrMatch) (.ref mtimeLoReg)
    (Expr.mux (.ref mtimeHiAddrMatch) (.ref mtimeHiReg)
      (.const 0 32))))))

/-- Build the CLINT module -/
def buildCLINT : Module :=
  CircuitM.runModule "RV32I_CLINT" do
    generateCLINT

end Sparkle.Examples.RV32.CLINT
