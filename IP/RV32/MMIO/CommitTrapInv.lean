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
import IP.RV32.Pipeline.FlushSquash

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

/-! ## Cycle-N+2 BitNet MMIO hold composites

  Same chain as CLINT (commit d361a48): when idex_memWrite is
  false at cycle t (e.g., from IDEX squash), mmioWE is false at
  t, so the BitNet MMIO register at t+1 holds. Combined with
  `trap_squashes_idex_next_cycle`, gives cycle-N+2 hold for
  aiStatusReg and aiInputReg. -/

/-- **idex_memWrite at t = false → mmioWE at t = false.** (Helper.) -/
private theorem mmioWE_false_when_idex_memWrite_false {dom : DomainConfig}
    (idex_memWrite is_mmio_ex validEX : Signal dom Bool) (t : Nat)
    (h_no_memWrite : idex_memWrite.val t = false) :
    (peripheralWESignal idex_memWrite is_mmio_ex validEX).val t = false := by
  unfold peripheralWESignal
  show (Signal.ap (Signal.map (· && ·) idex_memWrite)
    (is_mmio_ex &&& validEX)).val t = false
  show (idex_memWrite.val t && _) = false
  rw [h_no_memWrite]
  rfl

/-- **idex_memWrite at t = false → aiStatusReg at t+1 = old at t.** -/
theorem aiStatus_hold_when_idex_memWrite_false {dom : DomainConfig}
    (idex_memWrite is_mmio_ex mmioIsStatus validEX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_no_memWrite : idex_memWrite.val t = false) :
    let mmioWE := peripheralWESignal idex_memWrite is_mmio_ex validEX
    (Signal.register init (aiStatusNextSignal mmioWE mmioIsStatus newVal old)).val (t + 1)
      = old.val t := by
  have h_mmioWE :=
    mmioWE_false_when_idex_memWrite_false idex_memWrite is_mmio_ex validEX t h_no_memWrite
  -- regWE = mmioWE ∧ mmioIsStatus is false.
  have h_regWE :
    ((peripheralWESignal idex_memWrite is_mmio_ex validEX) &&& mmioIsStatus).val t = false := by
    show (Signal.ap (Signal.map (· && ·) _) mmioIsStatus).val t = false
    show ((peripheralWESignal idex_memWrite is_mmio_ex validEX).val t
      && mmioIsStatus.val t) = false
    rw [h_mmioWE]
    rfl
  -- aiStatusNext is definitionally csrPlainNextSignal at the WE.
  show (Signal.register init (csrPlainNextSignal _ newVal old)).val (t + 1) = old.val t
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

/-- **idex_memWrite at t = false → aiInputReg at t+1 = old at t.** -/
theorem aiInput_hold_when_idex_memWrite_false {dom : DomainConfig}
    (idex_memWrite is_mmio_ex mmioIsInput validEX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_no_memWrite : idex_memWrite.val t = false) :
    let mmioWE := peripheralWESignal idex_memWrite is_mmio_ex validEX
    (Signal.register init (aiInputNextSignal mmioWE mmioIsInput newVal old)).val (t + 1)
      = old.val t := by
  have h_mmioWE :=
    mmioWE_false_when_idex_memWrite_false idex_memWrite is_mmio_ex validEX t h_no_memWrite
  have h_regWE :
    ((peripheralWESignal idex_memWrite is_mmio_ex validEX) &&& mmioIsInput).val t = false := by
    show (Signal.ap (Signal.map (· && ·) _) mmioIsInput).val t = false
    show ((peripheralWESignal idex_memWrite is_mmio_ex validEX).val t
      && mmioIsInput.val t) = false
    rw [h_mmioWE]
    rfl
  show (Signal.register init (csrPlainNextSignal _ newVal old)).val (t + 1) = old.val t
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

/-- **trap at N + ¬freeze at N → aiStatusReg at N+2 = old at N+1.** -/
theorem trap_holds_aiStatus_reg_at_N_plus_2 {dom : DomainConfig}
    (trap_taken freeze squash : Signal dom Bool)
    (idex_memWrite_old idex_memWrite_new : Signal dom Bool)
    (is_mmio_ex mmioIsStatus validEX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (n : Nat)
    (h_trap_n : trap_taken.atTime n = true)
    (h_no_freeze_n : freeze.atTime n = false)
    (h_squash_includes_trap :
      trap_taken.atTime n = true → squash.atTime n = true)
    (h_idex_memWrite_at_N1 :
      idex_memWrite_new.atTime (n + 1) =
        (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_memWrite_old
          idex_memWrite_new (false : Bool)).atTime (n + 1)) :
    let mmioWE := peripheralWESignal idex_memWrite_new is_mmio_ex validEX
    (Signal.register init
      (aiStatusNextSignal mmioWE mmioIsStatus newVal old)).val (n + 2) =
      old.val (n + 1) := by
  have h_idex_n1_init :
    (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_memWrite_old
      idex_memWrite_new (false : Bool)).atTime (n + 1) = false := by
    apply Sparkle.IP.RV32.Pipeline.trap_squashes_idex_next_cycle freeze squash trap_taken
      idex_memWrite_old idex_memWrite_new false n
    · exact h_squash_includes_trap
    · exact h_trap_n
    · exact h_no_freeze_n
  have h_no_memWrite_n1 : idex_memWrite_new.atTime (n + 1) = false := by
    rw [h_idex_memWrite_at_N1]
    exact h_idex_n1_init
  exact aiStatus_hold_when_idex_memWrite_false idex_memWrite_new is_mmio_ex
    mmioIsStatus validEX init newVal old (n + 1) h_no_memWrite_n1

end Sparkle.IP.RV32.MMIO
