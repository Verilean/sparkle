/-
  RV32 BitNet MMIO commit trap invariant — multi-cycle composite

  Proves "trap at cycle t → BitNet MMIO register at t+1 = old.val t"
  for the two BitNet MMIO registers (aiStatusReg, aiInputReg).

  The chain mirrors the CLINT/UART pattern:

    1. trap at t → validEX at t = false
    2. validEX=false → mmioWE at t = false
    3. mmioWE=false → register-WE (= mmioWE ∧ regMatch) at t = false
    4. register-WE=false → reg at t+1 = old.val t

  The aiStatus/aiInput next-state shape is
  `Signal.mux (mmioWE &&& mmioIsX) newVal aiReg`, which is
  semantically the same as `csrPlainNextSignal (mmioWE &&& mmioIsX)
  newVal aiReg`. We use that equivalence to apply
  `csrPlainReg_hold_when_we_false`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit
import IP.RV32.MMIO.BitNet
import IP.RV32.Bus.PeripheralWE
import IP.RV32.Pipeline.SuppressEXWB

namespace Sparkle.IP.RV32.MMIO

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Bus
open Sparkle.IP.RV32.CSR
open Sparkle.IP.RV32.Pipeline

/-! ## aiStatusNextSignal / aiInputNextSignal = csrPlainNextSignal

  Both BitNet MMIO next-state functions are definitionally
  `csrPlainNextSignal (mmioWE ∧ mmioIsX)`. We prove the
  equivalence to apply downstream sequential lemmas. -/

theorem aiStatusNextSignal_eq_csrPlain {dom : DomainConfig}
    (mmioWE mmioIsStatus : Signal dom Bool)
    (newVal aiStatusReg : Signal dom (BitVec 32)) :
    aiStatusNextSignal mmioWE mmioIsStatus newVal aiStatusReg =
      csrPlainNextSignal (mmioWE &&& mmioIsStatus) newVal aiStatusReg := by
  unfold aiStatusNextSignal csrPlainNextSignal
  rfl

theorem aiInputNextSignal_eq_csrPlain {dom : DomainConfig}
    (mmioWE mmioIsInput : Signal dom Bool)
    (newVal aiInputReg : Signal dom (BitVec 32)) :
    aiInputNextSignal mmioWE mmioIsInput newVal aiInputReg =
      csrPlainNextSignal (mmioWE &&& mmioIsInput) newVal aiInputReg := by
  unfold aiInputNextSignal csrPlainNextSignal
  rfl

/-! ## Multi-cycle composites -/

/-- **trap at cycle t → aiStatusReg at t+1 = old.val t.** -/
theorem trap_holds_aiStatus_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite is_mmio_ex mmioIsStatus : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let mmioWE :=
      peripheralWESignal idex_memWrite is_mmio_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    (Signal.register init (aiStatusNextSignal mmioWE mmioIsStatus newVal old)).val (t + 1)
      = old.val t := by
  -- Step 1: validEX=false on trap.
  have h_validEX :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).val t = false := by
    rw [validEXSignal_eq_pure]
    rw [show trap_taken.val t = true from h_trap]
    exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
      (mmuBusy.val t) (dMMURedirect.val t)
  -- Step 2: mmioWE=false.
  have h_mmioWE :
    (peripheralWESignal idex_memWrite is_mmio_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    peripheralWESignal_false_when_validEX_false _ _ _ t h_validEX
  -- Step 3: regWE = mmioWE ∧ mmioIsStatus is false.
  have h_regWE :
    ((peripheralWESignal idex_memWrite is_mmio_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
      &&& mmioIsStatus).val t = false := by
    show (Signal.ap (Signal.map (· && ·) _) mmioIsStatus).val t = false
    show ((peripheralWESignal _ _ _).val t && mmioIsStatus.val t) = false
    rw [h_mmioWE]
    rfl
  -- Step 4: aiStatusNextSignal definitionally = csrPlainNextSignal at the
  -- chosen WE.
  show (Signal.register init (csrPlainNextSignal _ newVal old)).val (t + 1) = old.val t
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

/-- **trap at cycle t → aiInputReg at t+1 = old.val t.** -/
theorem trap_holds_aiInput_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite is_mmio_ex mmioIsInput : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let mmioWE :=
      peripheralWESignal idex_memWrite is_mmio_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    (Signal.register init (aiInputNextSignal mmioWE mmioIsInput newVal old)).val (t + 1)
      = old.val t := by
  have h_validEX :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).val t = false := by
    rw [validEXSignal_eq_pure]
    rw [show trap_taken.val t = true from h_trap]
    exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
      (mmuBusy.val t) (dMMURedirect.val t)
  have h_mmioWE :
    (peripheralWESignal idex_memWrite is_mmio_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    peripheralWESignal_false_when_validEX_false _ _ _ t h_validEX
  have h_regWE :
    ((peripheralWESignal idex_memWrite is_mmio_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
      &&& mmioIsInput).val t = false := by
    show (Signal.ap (Signal.map (· && ·) _) mmioIsInput).val t = false
    show ((peripheralWESignal _ _ _).val t && mmioIsInput.val t) = false
    rw [h_mmioWE]
    rfl
  show (Signal.register init (csrPlainNextSignal _ newVal old)).val (t + 1) = old.val t
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

end Sparkle.IP.RV32.MMIO
