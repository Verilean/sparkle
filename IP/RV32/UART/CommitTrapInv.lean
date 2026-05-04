/-
  RV32 UART commit trap invariant — multi-cycle composite

  Proves "trap at cycle t → UART register at t+1 = old.val t"
  for all 6 UART 8250 registers (LCR/IER/MCR/SCR/DLL/DLM).

  The chain (same shape as CLINT/CommitTrapInv but at 8-bit width):

    1. trap at t → validEX at t = false       (validEX_trap)
    2. validEX=false → uartWE at t = false    (peripheralWESignal_false_when_validEX_false)
    3. uartWE=false → register-WE at t = false
                                              (each uartWriteXSignal starts with `uartWE &&&`)
    4. register-WE=false → reg at t+1 = old.val t
                                              (csrPlainReg8_hold_when_we_false)

  Note: each UART register's WE has the form `uartWE &&& <other-conditions>`,
  so when `uartWE` is false, ALL six register WEs are false. We prove
  this once for the pattern and instantiate at each register.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit
import IP.RV32.UART.Decode
import IP.RV32.Bus.PeripheralWE
import IP.RV32.Pipeline.SuppressEXWB

namespace Sparkle.IP.RV32.UART

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Bus
open Sparkle.IP.RV32.CSR
open Sparkle.IP.RV32.Pipeline

/-! ## Per-WE-type sub-lemmas

  Each `uartWriteXSignal` has the shape `uartWE &&& <cond>`.
  When uartWE is false, the whole WE is false. -/

/-- LCR-WE is false when uartWE is false. -/
theorem uartWriteLCR_false_when_uartWE_false {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3)) (t : Nat)
    (h : uartWE.val t = false) :
    (uartWriteLCRSignal uartWE offset).val t = false := by
  unfold uartWriteLCRSignal
  show (uartWE &&& uartOffSignal offset 3#3).val t = false
  show (Signal.ap (Signal.map (· && ·) uartWE) (uartOffSignal offset 3#3)).val t = false
  show (uartWE.val t && (uartOffSignal offset 3#3).val t) = false
  rw [h]
  rfl

/-- IER-WE is false when uartWE is false. -/
theorem uartWriteIER_false_when_uartWE_false {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool) (t : Nat)
    (h : uartWE.val t = false) :
    (uartWriteIERSignal uartWE offset uartDLAB).val t = false := by
  unfold uartWriteIERSignal
  show (uartWE &&& (uartOffSignal offset 1#3 &&& (~~~uartDLAB))).val t = false
  show (Signal.ap (Signal.map (· && ·) uartWE) _).val t = false
  show (uartWE.val t && _) = false
  rw [h]
  rfl

/-- MCR-WE is false when uartWE is false. -/
theorem uartWriteMCR_false_when_uartWE_false {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3)) (t : Nat)
    (h : uartWE.val t = false) :
    (uartWriteMCRSignal uartWE offset).val t = false := by
  unfold uartWriteMCRSignal
  show (Signal.ap (Signal.map (· && ·) uartWE) _).val t = false
  show (uartWE.val t && _) = false
  rw [h]
  rfl

/-- SCR-WE is false when uartWE is false. -/
theorem uartWriteSCR_false_when_uartWE_false {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3)) (t : Nat)
    (h : uartWE.val t = false) :
    (uartWriteSCRSignal uartWE offset).val t = false := by
  unfold uartWriteSCRSignal
  show (Signal.ap (Signal.map (· && ·) uartWE) _).val t = false
  show (uartWE.val t && _) = false
  rw [h]
  rfl

/-- DLL-WE is false when uartWE is false. -/
theorem uartWriteDLL_false_when_uartWE_false {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool) (t : Nat)
    (h : uartWE.val t = false) :
    (uartWriteDLLSignal uartWE offset uartDLAB).val t = false := by
  unfold uartWriteDLLSignal
  show (Signal.ap (Signal.map (· && ·) uartWE) _).val t = false
  show (uartWE.val t && _) = false
  rw [h]
  rfl

/-- DLM-WE is false when uartWE is false. -/
theorem uartWriteDLM_false_when_uartWE_false {dom : DomainConfig}
    (uartWE : Signal dom Bool) (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool) (t : Nat)
    (h : uartWE.val t = false) :
    (uartWriteDLMSignal uartWE offset uartDLAB).val t = false := by
  unfold uartWriteDLMSignal
  show (Signal.ap (Signal.map (· && ·) uartWE) _).val t = false
  show (uartWE.val t && _) = false
  rw [h]
  rfl

/-! ## Multi-cycle composites — one per UART register

  Each follows the chain "trap → validEX=false → uartWE=false →
  per-register-WE=false → register holds at t+1".
-/

/-- **trap at cycle t → uartLCRReg at t+1 = old.val t.** -/
theorem trap_holds_uart_LCR_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let uartWE :=
      peripheralWESignal idex_memWrite isUART_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let we := uartWriteLCRSignal uartWE offset
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  -- trap → validEX=false → uartWE=false → LCR-WE=false → reg holds.
  have h_validEX :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).val t = false := by
    rw [validEXSignal_eq_pure]
    rw [show trap_taken.val t = true from h_trap]
    exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
      (mmuBusy.val t) (dMMURedirect.val t)
  have h_uartWE :
    (peripheralWESignal idex_memWrite isUART_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    peripheralWESignal_false_when_validEX_false _ _ _ t h_validEX
  have h_we_false :
    (uartWriteLCRSignal _ offset).val t = false :=
    uartWriteLCR_false_when_uartWE_false _ offset t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

/-- **trap at cycle t → uartIERReg at t+1 = old.val t.** -/
theorem trap_holds_uart_IER_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool)
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let uartWE :=
      peripheralWESignal idex_memWrite isUART_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let we := uartWriteIERSignal uartWE offset uartDLAB
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  have h_validEX :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).val t = false := by
    rw [validEXSignal_eq_pure]
    rw [show trap_taken.val t = true from h_trap]
    exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
      (mmuBusy.val t) (dMMURedirect.val t)
  have h_uartWE :
    (peripheralWESignal idex_memWrite isUART_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    peripheralWESignal_false_when_validEX_false _ _ _ t h_validEX
  have h_we_false :
    (uartWriteIERSignal _ offset uartDLAB).val t = false :=
    uartWriteIER_false_when_uartWE_false _ offset uartDLAB t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

end Sparkle.IP.RV32.UART
