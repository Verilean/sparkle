/-
  RV32 CSR commit trap invariant — multi-cycle composite

  Combines two prior building blocks into the multi-cycle
  theorem "trap at cycle t → plain-CSR register unchanged at
  cycle t+1":

    1. `Pipeline/SuppressEXWB.lean::trap_clears_idex_isCsr_valid`
       (combinational, commit cb217a8):
         trap at t → idex_isCsr_valid at t = false.

    2. `CSR/Commit.lean::csrPlainReg_hold_when_we_false`
       (sequential, commit 8991046):
         WE=false at t → CSR-reg at t+1 = old.val t.

  The composite says: when trap fires at cycle t, the next-cycle
  value of any plain-commit CSR register (mie, mtvec, mscratch,
  satp, sie, stvec, sscratch, ...) equals its current-cycle
  value, i.e., the register is unchanged across the trap entry.

  This is the hardware-side guarantee for invariant A
  (regfile preservation) extended to CSR registers — the trap
  handler sees the pre-trap CSR state, not a partially-committed
  CSR write that was in flight when the trap fired.

  Applies to 16 CSRs in SoC.lean: mie/mtvec/mscratch/satp/sie/
  stvec/sscratch/medeleg/mideleg/mcounteren/scounteren plus the
  5 trap-overridable ones (mepc/mcause/mtval/sepc/scause/stval)
  in their non-trap-firing-arm.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.CSR.Commit
import IP.RV32.CSR.AddrDecoder
import IP.RV32.Pipeline.SuppressEXWB
import IP.RV32.Pipeline.FlushSquash

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.Pipeline

/-! ## Multi-cycle composite -/

/-- **trap at cycle t → plain-commit CSR-reg at t+1 = old.val t.**

    The CSR-WE is gated by `idex_isCsr_valid` (= idex_isCsr ∧
    validEX); a trap clears validEX same-cycle (combinational),
    so the WE is false, and the register holds. -/
theorem trap_holds_csrPlain_reg {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_isCsr csrIsX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    -- Build the WE as csrRegWeSignal (= idex_isCsr_valid &&& csrIsX), the
    -- shape SoC.lean uses at all 21 CSR-write call sites (commit 4a5fa69).
    let we :=
      csrRegWeSignal
        (idexIsCsrValidSignal idex_isCsr
          (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
        csrIsX
    (csrPlainRegSignal init we newVal old).val (t + 1) = old.val t := by
  -- Step 1: trap → idex_isCsr_valid at t = false.
  have h_isCsrValid :
    (idexIsCsrValidSignal idex_isCsr
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t = false :=
    trap_clears_idex_isCsr_valid trap_taken dTLBMiss pendingWriteEn
      mmuBusy dMMURedirect idex_isCsr t h_trap
  -- Step 2: csrRegWeSignal (= isCsrValid ∧ csrIsX) is false when isCsrValid is false.
  have h_we_false :
    (Sparkle.IP.RV32.CSR.csrRegWeSignal
      (idexIsCsrValidSignal idex_isCsr
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
      csrIsX).val t = false := by
    -- csrRegWeSignal is `&&&` over Signal Bool; reduce to Bool-and at cycle t.
    show ((idexIsCsrValidSignal idex_isCsr
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect))
      &&& csrIsX).val t = false
    show (Signal.ap (Signal.map (· && ·)
      (idexIsCsrValidSignal idex_isCsr
        (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)))
      csrIsX).val t = false
    show ((idexIsCsrValidSignal idex_isCsr
      (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)).val t
      && csrIsX.val t) = false
    rw [h_isCsrValid]
    rfl
  -- Step 3: register holds when WE is false.
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_we_false

/-! ## Trap-override register on trap entry

  For trap-overridable CSRs (mepc/mcause/mtval), the trap-firing
  path latches `trapPayload` regardless of the CSR write. The
  pure version `csrTrapOverrideNext_trap_priority` already proves
  this combinationally; the sequential
  `csrTrapOverrideReg_latch_on_trap` lifts it across the
  Signal.register delay.

  Composite: when trap_taken (which implies trapTo for either
  M-mode or S-mode, depending on delegation) fires at cycle t,
  the trap-override register at cycle t+1 latches the payload.
  The composite below provides a clean entry point for invariant
  E reasoning: even if the CSR write would have fired, the trap
  takes priority.
-/

/-- **trapTo at t → trap-override CSR-reg at t+1 = trapPayload.val t.**

    This is essentially a re-export of
    `csrTrapOverrideReg_latch_on_trap` packaged with the
    same shape as `trap_holds_csrPlain_reg`. Provided for
    symmetry; downstream proofs may use either form. -/
theorem trapTo_latches_csrTrapOverride_reg {dom : DomainConfig}
    (init : BitVec 32) (trapTo : Signal dom Bool)
    (trapPayload : Signal dom (BitVec 32))
    (idex_isCsr csrIsX : Signal dom Bool)
    (validEX : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_trapTo : trapTo.val t = true) :
    let we := csrRegWeSignal (idexIsCsrValidSignal idex_isCsr validEX) csrIsX
    (csrTrapOverrideRegSignal init trapTo trapPayload we newVal old).val (t + 1) =
      trapPayload.val t :=
  csrTrapOverrideReg_latch_on_trap init trapTo trapPayload _ newVal old t h_trapTo

/-! ## Cycle-N+2 plain-CSR hold composite

  Same chain as the regfile cycle-N+2 composite
  (`trap_suppresses_wb_en_at_N_plus_2`), but for plain-commit
  CSR registers:

    trap at N → IDEX squash at N+1 (idex_isCsr at N+1 = false)
              → idex_isCsr_valid at N+1 = false
              → csrRegWe at N+1 = false
              → csrPlainReg at N+2 = old at N+1.

  The cycle-N+1 composite `trap_holds_csrPlain_reg` already
  proves "CSR at N+1 = old at N". Combined with this lemma,
  we get "CSR at N+2 = old at N+1" which by transitivity
  may equal old at N (when nothing else writes between).
  But the cleanest statement is just the cycle-by-cycle
  hold across N+1 → N+2.
-/

/-- **idex_isCsr at N+1 = false → csrPlainReg at N+2 = old at N+1.**

    Downstream half of the cycle-N+2 CSR-suppression chain.
    Combines `csrPlainReg_hold_when_we_false` with the
    `csrRegWeSignal` definition (= idex_isCsr_valid &&& csrIsX,
    which is false when idex_isCsr is false). -/
theorem csrPlainReg_hold_when_idex_isCsr_false {dom : DomainConfig}
    (init : BitVec 32) (idex_isCsr csrIsX : Signal dom Bool)
    (validEX : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) (t : Nat)
    (h_no_isCsr : idex_isCsr.val t = false) :
    let we := csrRegWeSignal (idexIsCsrValidSignal idex_isCsr validEX) csrIsX
    (csrPlainRegSignal init we newVal old).val (t + 1) = old.val t := by
  -- Step 1: idex_isCsr_valid = idex_isCsr ∧ validEX, so when idex_isCsr is false,
  -- the result is false.
  have h_no_isCsrValid :
    (idexIsCsrValidSignal idex_isCsr validEX).val t = false := by
    unfold idexIsCsrValidSignal
    show (Signal.ap (Signal.map (· && ·) idex_isCsr) validEX).val t = false
    show (idex_isCsr.val t && validEX.val t) = false
    rw [h_no_isCsr]
    rfl
  -- Step 2: csrRegWeSignal = idex_isCsr_valid ∧ csrIsX, false when isCsrValid is false.
  have h_no_we :
    (csrRegWeSignal (idexIsCsrValidSignal idex_isCsr validEX) csrIsX).val t = false := by
    show ((idexIsCsrValidSignal idex_isCsr validEX) &&& csrIsX).val t = false
    show (Signal.ap (Signal.map (· && ·)
      (idexIsCsrValidSignal idex_isCsr validEX)) csrIsX).val t = false
    show ((idexIsCsrValidSignal idex_isCsr validEX).val t && csrIsX.val t) = false
    rw [h_no_isCsrValid]
    rfl
  -- Step 3: register holds when WE is false.
  exact csrPlainReg_hold_when_we_false init _ newVal old t h_no_we

/-! ## Multi-cycle: trap at N → plain CSR-reg at N+2 = old at N+1

  Chains:
    1. IDEX squash at N+1 (idex_isCsr at N+1 = false), via
       `trap_squashes_idex_next_cycle` from FlushSquash (Bool init = false).
    2. csrPlainReg hold (cycle N+1 → N+2), via
       `csrPlainReg_hold_when_idex_isCsr_false`.

  Combined with the cycle-N+1 lemma `trap_holds_csrPlain_reg`,
  this gives a 2-cycle hold guarantee for plain-commit CSRs
  after a trap. -/

/-- **trap at N + freeze=false at N → plain CSR-reg at N+2 = old at N+1
    (when wired through idexLatchSignal).**

    Hypotheses on the structural shape:
    - `h_squash_includes_trap`: trap at N → squash at N (caller
      discharges via `squash_contains_trap_taken`).
    - `idex_isCsr_at_N1_is_idex_latch`: at N+1, idex_isCsr equals
      the IDEX latch's output. -/
theorem trap_holds_csrPlain_reg_at_N_plus_2 {dom : DomainConfig}
    (trap_taken freeze squash : Signal dom Bool)
    (idex_isCsr_old idex_isCsr_new : Signal dom Bool)
    (validEX : Signal dom Bool) (csrIsX : Signal dom Bool)
    (init : BitVec 32) (newVal old : Signal dom (BitVec 32)) (n : Nat)
    (h_trap_n : trap_taken.atTime n = true)
    (h_no_freeze_n : freeze.atTime n = false)
    (h_squash_includes_trap :
      trap_taken.atTime n = true → squash.atTime n = true)
    (h_idex_isCsr_at_N1 :
      idex_isCsr_new.atTime (n + 1) =
        (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_isCsr_old idex_isCsr_new
          (false : Bool)).atTime (n + 1)) :
    let we := csrRegWeSignal (idexIsCsrValidSignal idex_isCsr_new validEX) csrIsX
    (csrPlainRegSignal init we newVal old).val (n + 2) = old.val (n + 1) := by
  -- Step 1: IDEX-Bool latch at N+1 = false (init=false on squash).
  have h_idex_n1_init :
    (Sparkle.IP.RV32.Pipeline.idexLatchSignal freeze squash idex_isCsr_old idex_isCsr_new
      (false : Bool)).atTime (n + 1) = false := by
    apply Sparkle.IP.RV32.Pipeline.trap_squashes_idex_next_cycle freeze squash trap_taken
      idex_isCsr_old idex_isCsr_new false n
    · exact h_squash_includes_trap
    · exact h_trap_n
    · exact h_no_freeze_n
  -- Step 2: idex_isCsr at N+1 = false (by wire-def).
  have h_idex_isCsr_n1_false : idex_isCsr_new.atTime (n + 1) = false := by
    rw [h_idex_isCsr_at_N1]
    exact h_idex_n1_init
  -- Step 3: csrPlainReg holds (downstream).
  exact csrPlainReg_hold_when_idex_isCsr_false init idex_isCsr_new csrIsX validEX
    newVal old (n + 1) h_idex_isCsr_n1_false

end Sparkle.IP.RV32.CSR
