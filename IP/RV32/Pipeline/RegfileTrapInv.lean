/-
  RV32 regfile-write suppression on trap — partial invariant A

  Builds toward invariant A from `docs/RV32_Architecture_Status.md`
  §2.2:

      "If kernel at PC P has r[i] = v and runs into a trap+ISR
       sequence that saves r[i] to m[a] and later restores
       r[i] := m[a], then after sret r[i] = v."

  The full statement depends on the kernel ABI (save/restore
  correctness). What we can prove at the **hardware level**:
  during the trap-entry cycle itself, the regfile is NOT
  written by the in-flight IDEX instruction (because the
  trap suppresses `exwb_regW`).

  Spec:

    suppressEXWB = trap_taken ∨ dTLBMiss ∨ holdEX ∨ dMMURedirect

  When `trap_taken = true` at cycle N, the EXWB control bits
  (regWrite, memWrite, isCsr, etc.) are all forced to `false`
  at cycle N+1 via `mux suppressEXWB false ctrlBit` (proven
  in `Pipeline/AbortGuarantee.lean`'s `suppressEXWB_aborts_*`).

  In particular, `exwb_regW` at cycle N+1 = false. Combined
  with the WB-stage logic:

    wb_en = exwb_regW ∧ (exwb_rd ≠ 0)

  → `wb_en = false` at cycle N+1, so no regfile write fires.

  This is the **hardware prerequisite** for invariant A: the
  in-flight instruction's register write is dropped on trap
  entry, so the kernel save/restore sequence sees the
  pre-trap regfile state intact (modulo what the kernel
  itself reads/writes during the ISR).

  Companion to:
    * Pipeline/AbortGuarantee.lean — single-cycle abort guarantee
    * Pipeline/SuppressEXWB.lean   — suppression composition
    * Pipeline/Regfile.lean        — wb_en + WB→ID forwarding
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Pipeline.AbortGuarantee
import IP.RV32.Pipeline.SuppressEXWB

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## trap_taken at cycle N → exwb_regW = false at cycle N+1

  This combines:
    * `suppressEXWB_trap` (SuppressEXWB.lean): trap_taken
      forces suppressEXWB = true (combinational).
    * `suppressEXWB_aborts_regW_next_cycle` (AbortGuarantee.lean):
      suppressEXWB at cycle t → exwb_regW latch at t+1 = false.
-/

/-- **Trap suppresses register-write at next cycle.**

    When `trap_taken` fires at cycle t (and other suppressors are
    arbitrary), the in-flight IDEX instruction's `exwb_regW` is
    forced to `false` at cycle t+1 — so any subsequent regfile
    write port driver gates correctly. -/
theorem trap_suppresses_exwb_regW {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_regWrite : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    let suppressEXWB := suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
    (exwbRegWSignal suppressEXWB idex_regWrite).atTime (t + 1) = false := by
  -- Step 1: suppressEXWB.val t = true (since trap_taken.val t = true)
  have h_supp : (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect).atTime t = true := by
    unfold Signal.atTime
    rw [suppressEXWBSignal_eq_pure]
    show suppressEXWBPure (trap_taken.val t) (dTLBMiss.val t)
        (pendingWriteEn.val t) (mmuBusy.val t) (dMMURedirect.val t) = true
    rw [show trap_taken.val t = true from h_trap]
    exact suppressEXWB_trap (dTLBMiss.val t) (pendingWriteEn.val t) (mmuBusy.val t) (dMMURedirect.val t)
  -- Step 2: apply the abort guarantee
  exact suppressEXWB_aborts_regW_next_cycle _ idex_regWrite t h_supp

/-! ## Hardware-level regfile-preservation

  A sufficient condition for "regfile is not modified by the
  in-flight instruction during trap entry": the WB-stage
  enable (`wb_en = exwb_regW ∧ exwb_rd ≠ 0`) is false because
  the regW component is false. -/

/-- Pure wb_en computation for spec purposes. -/
@[inline] def wbEnPure (exwb_regW : Bool) (exwb_rd_nonzero : Bool) : Bool :=
  exwb_regW && exwb_rd_nonzero

/-- exwb_regW = false → wb_en = false. -/
@[simp] theorem wbEn_off_when_regW_off (rd_nz : Bool) :
    wbEnPure false rd_nz = false := by rfl

/-- The combined sequential statement: trap at cycle t →
    wb_en at t+1 = false. -/
theorem trap_suppresses_wb_en {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_regWrite : Signal dom Bool) (rd_nz_at_t1 : Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    wbEnPure
      ((exwbRegWSignal
          (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
          idex_regWrite).atTime (t + 1))
      rd_nz_at_t1 = false := by
  have h_regW := trap_suppresses_exwb_regW trap_taken dTLBMiss pendingWriteEn
    mmuBusy dMMURedirect idex_regWrite t h_trap
  rw [h_regW]
  rfl

/-! ## Connection to invariant A

  Invariant A requires "regfile preservation across trap":

    1. **In-flight instruction does not write to regfile during
       trap entry** (proven here): the EXWB-stage `regW` bit
       is forced to false on the trap cycle, so no regfile
       write fires.

    2. **Kernel save/restore correctness** (kernel ABI): the
       trap handler saves all registers it modifies and
       restores them before sret. This is the kernel's
       responsibility, not the hardware's.

  With (1) proven, the hardware delivers the right precondition
  for the kernel's save/restore to work. (1) is what we control;
  (2) is a software contract.

  Combined with the previous sequential invariants:

    - B (IDEX squash, FlushSquash.lean):
        trap → IDEX latches NOP-init at cycle t+1
    - this commit:
        trap → exwb_regW=false at cycle t+1, hence wb_en=false

  Together: at cycle t+1, both the in-flight EXWB instruction
  AND the new IDEX (= NOP) have all side-effect-bearing bits
  cleared. The regfile is untouched.
-/

end Sparkle.IP.RV32.Pipeline
