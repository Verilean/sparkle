/-
  RV32 CLINT commit trap invariant — multi-cycle composite

  Combines two prior building blocks into the multi-cycle
  theorem "trap at cycle t → CLINT register unchanged at
  cycle t+1":

    1. `Pipeline/SuppressEXWB.lean::validEX_trap` (combinational):
         trap → validEX at t = false.

    2. `Bus/PeripheralWE.lean::peripheralWESignal_false_when_validEX_false`
       (combinational):
         validEX=false at t → peripheralWE at t = false.

    3. `CLINT/Decode.lean::clintRegWeSignal` (def):
         clintRegWe = clintWE ∧ regMatch.

    4. `CSR/Commit.lean::csrPlainReg_hold_when_we_false`
       (sequential):
         WE=false at t → CSR-reg at t+1 = old.val t.

  Together: trap at cycle t → CLINT-WE at t = false → CLINT
  register at t+1 = old.val t.

  Applies to all 5 CLINT registers in SoC.lean:
  msip/mtimecmpLo/mtimecmpHi/mtimeLo/mtimeHi.

  The mtimeLo/Hi case is interesting: their `old` is actually the
  incremented value `mtimeLoInc`/`mtimeHiInc`, so under "no CSR
  write" the time advances every cycle. The trap-suppression
  guarantee here is that the CSR *write* doesn't fire — the
  mtime increment continues normally.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit
import IP.RV32.CLINT.Decode
import IP.RV32.Bus.PeripheralWE
import IP.RV32.Pipeline.SuppressEXWB
import IP.RV32.Pipeline.FlushSquash

namespace Sparkle.IP.RV32.CLINT

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Bus
open Sparkle.IP.RV32.CSR
open Sparkle.IP.RV32.Pipeline

/-! ## Multi-cycle composite -/

/-- **trap at cycle t → CLINT register at t+1 = old.val t.**

    The CLINT-WE is `clintWE ∧ regMatch`, where `clintWE =
    peripheralWESignal idex_memWrite isCLINT_ex validEX`. A trap
    clears validEX same-cycle, so peripheralWE is false, so the
    register WE is false, so the register holds. -/
theorem trap_holds_clintReg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isCLINT_ex regMatch : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    -- Wire the WE the same way SoC.lean does:
    let clintWE :=
      peripheralWESignal idex_memWrite isCLINT_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    let regWE := clintRegWeSignal clintWE regMatch
    (csrPlainRegSignal init regWE newVal old).val (t + 1) = old.val t := by
  -- Step 1: validEX at t = false on trap.
  have h_validEX :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).val t = false := by
    rw [validEXSignal_eq_pure]
    rw [show trap_taken.val t = true from h_trap]
    exact validEX_trap (dTLBMiss.val t) (pendingWriteEn.val t)
      (mmuBusy.val t) (dMMURedirect.val t)
  -- Step 2: clintWE = peripheralWE is false (validEX=false).
  have h_clintWE :
    (peripheralWESignal idex_memWrite isCLINT_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    peripheralWESignal_false_when_validEX_false _ _ _ t h_validEX
  -- Step 3: clintRegWe = clintWE ∧ regMatch is false (clintWE=false).
  have h_regWE :
    (clintRegWeSignal
      (peripheralWESignal idex_memWrite isCLINT_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
      regMatch).val t = false := by
    -- clintRegWeSignal is `&&&` over Signal Bool; reduce to Bool-and.
    show (Signal.ap (Signal.map (· && ·)
      (peripheralWESignal idex_memWrite isCLINT_ex
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)))
      regMatch).val t = false
    show ((peripheralWESignal idex_memWrite isCLINT_ex
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t
      && regMatch.val t) = false
    rw [h_clintWE]
    rfl
  -- Step 4: register holds when WE=false.
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

/-! ## Downstream cycle-N+2 CLINT hold

  When idex_memWrite is false at cycle t (e.g., from an IDEX
  squash), peripheralWE is false at t (regardless of validEX),
  so the CLINT register at t+1 holds. Cycle-N+2 form: idex_memWrite
  at N+1 = false → CLINT at N+2 = old at N+1. -/

/-- **idex_memWrite at t = false → CLINT-reg at t+1 = old at t.** -/
theorem clintReg_hold_when_idex_memWrite_false {dom : DomainConfig}
    (idex_memWrite isCLINT_ex regMatch validEX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_no_memWrite : idex_memWrite.val t = false) :
    let clintWE := peripheralWESignal idex_memWrite isCLINT_ex validEX
    let regWE := clintRegWeSignal clintWE regMatch
    (csrPlainRegSignal init regWE newVal old).val (t + 1) = old.val t := by
  -- peripheralWE = idex_memWrite ∧ (targetMatch ∧ validEX); when memWrite is false,
  -- the whole thing is false.
  have h_clintWE :
    (peripheralWESignal idex_memWrite isCLINT_ex validEX).val t = false := by
    unfold peripheralWESignal
    show (Signal.ap (Signal.map (· && ·) idex_memWrite)
      (isCLINT_ex &&& validEX)).val t = false
    show (idex_memWrite.val t && _) = false
    rw [h_no_memWrite]
    rfl
  -- regWE = clintWE ∧ regMatch is false.
  have h_regWE :
    (clintRegWeSignal (peripheralWESignal idex_memWrite isCLINT_ex validEX)
      regMatch).val t = false := by
    show (Signal.ap (Signal.map (· && ·)
      (peripheralWESignal idex_memWrite isCLINT_ex validEX)) regMatch).val t = false
    show ((peripheralWESignal idex_memWrite isCLINT_ex validEX).val t
      && regMatch.val t) = false
    rw [h_clintWE]
    rfl
  -- CLINT-reg holds when WE=false.
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_regWE

/-! ## Multi-cycle: trap at N → CLINT-reg at N+2 = old at N+1

  Chains the IDEX squash (idex_memWrite=false at N+1) with the
  downstream `clintReg_hold_when_idex_memWrite_false`. -/

/-- **trap at N + ¬freeze at N → CLINT-reg at N+2 = old at N+1
    (when wired through idexLatchSignal).** -/
theorem trap_holds_clintReg_at_N_plus_2 {dom : DomainConfig}
    (trap_taken freeze squash : Signal dom Bool)
    (idex_memWrite_old idex_memWrite_new : Signal dom Bool)
    (isCLINT_ex regMatch validEX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (n : Nat)
    (h_trap_n : trap_taken.atTime n = true)
    (h_no_freeze_n : freeze.atTime n = false)
    (h_squash_includes_trap :
      trap_taken.atTime n = true → squash.atTime n = true)
    (h_idex_memWrite_at_N1 :
      idex_memWrite_new.atTime (n + 1) =
        (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_memWrite_old
          idex_memWrite_new (false : Bool)).atTime (n + 1)) :
    let clintWE := peripheralWESignal idex_memWrite_new isCLINT_ex validEX
    let regWE := clintRegWeSignal clintWE regMatch
    (csrPlainRegSignal init regWE newVal old).val (n + 2) = old.val (n + 1) := by
  -- Step 1: IDEX latch at N+1 = false (init=false on squash).
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
  -- Step 3: CLINT-reg holds (downstream).
  exact clintReg_hold_when_idex_memWrite_false idex_memWrite_new isCLINT_ex
    regMatch validEX init newVal old (n + 1) h_no_memWrite_n1

/-! ## LTL forms -/

/-- **LTL form of `trap_holds_clintReg`.** -/
theorem trap_holds_clintReg_LTL {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_memWrite isCLINT_ex regMatch : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) :
    ∀ t, trap_taken.atTime t = true →
         let clintWE := peripheralWESignal idex_memWrite isCLINT_ex
           (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
         let regWE := clintRegWeSignal clintWE regMatch
         (csrPlainRegSignal init regWE newVal old).val (t + 1) = old.val t :=
  fun t => trap_holds_clintReg trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
    idex_memWrite isCLINT_ex regMatch init newVal old t

/-- **LTL form of `clintReg_hold_when_idex_memWrite_false`.** -/
theorem clintReg_hold_when_idex_memWrite_false_LTL {dom : DomainConfig}
    (idex_memWrite isCLINT_ex regMatch validEX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) :
    ∀ t, idex_memWrite.val t = false →
         let clintWE := peripheralWESignal idex_memWrite isCLINT_ex validEX
         let regWE := clintRegWeSignal clintWE regMatch
         (csrPlainRegSignal init regWE newVal old).val (t + 1) = old.val t :=
  fun t => clintReg_hold_when_idex_memWrite_false idex_memWrite isCLINT_ex regMatch
    validEX init newVal old t

end Sparkle.IP.RV32.CLINT
