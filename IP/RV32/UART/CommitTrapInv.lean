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
import IP.RV32.Pipeline.FlushSquash

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

/-! ## Helper: trap → uartWE = false at t

  Common chain extracted for reuse across the remaining four
  composites. -/

private theorem trap_clears_uartWE {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (peripheralWESignal idex_memWrite isUART_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false := by
  apply peripheralWESignal_false_when_validEX_false
  rw [validEXSignal_eq_pure]
  rw [show trap_taken.val t = true from h_trap]
  exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
    (mmuBusy.val t) (dMMURedirect.val t)

/-- **trap at cycle t → uartMCRReg at t+1 = old.val t.** -/
theorem trap_holds_uart_MCR_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let uartWE :=
      peripheralWESignal idex_memWrite isUART_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let we := uartWriteMCRSignal uartWE offset
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  have h_uartWE := trap_clears_uartWE trap_taken dTLBMiss pendingWriteEn
    mmuBusy dMMURedirect idex_memWrite isUART_ex t h_trap
  have h_we_false :
    (uartWriteMCRSignal _ offset).val t = false :=
    uartWriteMCR_false_when_uartWE_false _ offset t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

/-- **trap at cycle t → uartSCRReg at t+1 = old.val t.** -/
theorem trap_holds_uart_SCR_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let uartWE :=
      peripheralWESignal idex_memWrite isUART_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let we := uartWriteSCRSignal uartWE offset
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  have h_uartWE := trap_clears_uartWE trap_taken dTLBMiss pendingWriteEn
    mmuBusy dMMURedirect idex_memWrite isUART_ex t h_trap
  have h_we_false :
    (uartWriteSCRSignal _ offset).val t = false :=
    uartWriteSCR_false_when_uartWE_false _ offset t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

/-- **trap at cycle t → uartDLLReg at t+1 = old.val t.** -/
theorem trap_holds_uart_DLL_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool)
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let uartWE :=
      peripheralWESignal idex_memWrite isUART_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let we := uartWriteDLLSignal uartWE offset uartDLAB
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  have h_uartWE := trap_clears_uartWE trap_taken dTLBMiss pendingWriteEn
    mmuBusy dMMURedirect idex_memWrite isUART_ex t h_trap
  have h_we_false :
    (uartWriteDLLSignal _ offset uartDLAB).val t = false :=
    uartWriteDLL_false_when_uartWE_false _ offset uartDLAB t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

/-- **trap at cycle t → uartDLMReg at t+1 = old.val t.** -/
theorem trap_holds_uart_DLM_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isUART_ex : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (uartDLAB : Signal dom Bool)
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let uartWE :=
      peripheralWESignal idex_memWrite isUART_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let we := uartWriteDLMSignal uartWE offset uartDLAB
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  have h_uartWE := trap_clears_uartWE trap_taken dTLBMiss pendingWriteEn
    mmuBusy dMMURedirect idex_memWrite isUART_ex t h_trap
  have h_we_false :
    (uartWriteDLMSignal _ offset uartDLAB).val t = false :=
    uartWriteDLM_false_when_uartWE_false _ offset uartDLAB t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

/-! ## Cycle-N+2 UART hold composite

  When idex_memWrite is false at cycle t (e.g., from an IDEX
  squash), uartWE is false at t (regardless of validEX), so any
  per-register UART WE is false, so the UART register at t+1 holds.
  Combined with `trap_squashes_idex_next_cycle`, this gives
  cycle-N+2 hold for all 6 UART registers.

  We provide the LCR variant fully and leave the others to
  follow the same template via `trap_clears_uartWE_via_idex_squash`
  (a private helper). -/

/-- **idex_memWrite at t = false → uartWE at t = false.** (Helper.) -/
private theorem uartWE_false_when_idex_memWrite_false {dom : DomainConfig}
    (idex_memWrite isUART_ex validEX : Signal dom Bool) (t : Nat)
    (h_no_memWrite : idex_memWrite.val t = false) :
    (peripheralWESignal idex_memWrite isUART_ex validEX).val t = false := by
  unfold peripheralWESignal
  show (Signal.ap (Signal.map (· && ·) idex_memWrite)
    (isUART_ex &&& validEX)).val t = false
  show (idex_memWrite.val t && _) = false
  rw [h_no_memWrite]
  rfl

/-- **idex_memWrite at t = false → uartLCRReg at t+1 = old at t.** -/
theorem uart_LCR_hold_when_idex_memWrite_false {dom : DomainConfig}
    (idex_memWrite isUART_ex validEX : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (t : Nat)
    (h_no_memWrite : idex_memWrite.val t = false) :
    let uartWE := peripheralWESignal idex_memWrite isUART_ex validEX
    let we := uartWriteLCRSignal uartWE offset
    (csrPlainRegSignal8 init we newVal old).val (t + 1) = old.val t := by
  have h_uartWE :=
    uartWE_false_when_idex_memWrite_false idex_memWrite isUART_ex validEX t h_no_memWrite
  have h_we_false :
    (uartWriteLCRSignal _ offset).val t = false :=
    uartWriteLCR_false_when_uartWE_false _ offset t h_uartWE
  exact csrPlainReg8_hold_when_we_false init _ newVal old t h_we_false

/-- **trap at N + ¬freeze at N → uartLCRReg at N+2 = old at N+1
    (when wired through idexLatchSignal).** -/
theorem trap_holds_uart_LCR_reg_at_N_plus_2 {dom : DomainConfig}
    (trap_taken freeze squash : Signal dom Bool)
    (idex_memWrite_old idex_memWrite_new : Signal dom Bool)
    (isUART_ex validEX : Signal dom Bool)
    (offset : Signal dom (BitVec 3))
    (init : BitVec 8) (newVal old : Signal dom (BitVec 8)) (n : Nat)
    (h_trap_n : trap_taken.atTime n = true)
    (h_no_freeze_n : freeze.atTime n = false)
    (h_squash_includes_trap :
      trap_taken.atTime n = true → squash.atTime n = true)
    (h_idex_memWrite_at_N1 :
      idex_memWrite_new.atTime (n + 1) =
        (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_memWrite_old
          idex_memWrite_new (false : Bool)).atTime (n + 1)) :
    let uartWE := peripheralWESignal idex_memWrite_new isUART_ex validEX
    let we := uartWriteLCRSignal uartWE offset
    (csrPlainRegSignal8 init we newVal old).val (n + 2) = old.val (n + 1) := by
  -- Step 1: IDEX latch at N+1 = false.
  have h_idex_n1_init :
    (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_memWrite_old
      idex_memWrite_new (false : Bool)).atTime (n + 1) = false := by
    apply Sparkle.IP.RV32.Pipeline.trap_squashes_idex_next_cycle freeze squash trap_taken
      idex_memWrite_old idex_memWrite_new false n
    · exact h_squash_includes_trap
    · exact h_trap_n
    · exact h_no_freeze_n
  -- Step 2: idex_memWrite at N+1 = false (by wire-def).
  have h_no_memWrite_n1 : idex_memWrite_new.atTime (n + 1) = false := by
    rw [h_idex_memWrite_at_N1]
    exact h_idex_n1_init
  -- Step 3: UART-LCR holds (downstream).
  exact uart_LCR_hold_when_idex_memWrite_false idex_memWrite_new isUART_ex validEX
    offset init newVal old (n + 1) h_no_memWrite_n1

end Sparkle.IP.RV32.UART
