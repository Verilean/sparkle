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

end Sparkle.IP.RV32.CSR
