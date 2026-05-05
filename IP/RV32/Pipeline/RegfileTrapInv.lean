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
import IP.RV32.Pipeline.FlushSquash

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

/-- Pure rd-nonzero predicate. -/
@[inline] def wbRdNzPure (exwb_rd : BitVec 5) : Bool :=
  !(exwb_rd == 0#5)

/-- Signal-level rd-nonzero predicate. -/
def wbRdNzSignal {dom : DomainConfig}
    (exwb_rd : Signal dom (BitVec 5)) : Signal dom Bool :=
  ~~~(exwb_rd === 0#5)

/-- Signal-level wb_en. -/
def wbEnSignal {dom : DomainConfig}
    (exwb_regW wbRdNz : Signal dom Bool) : Signal dom Bool :=
  exwb_regW &&& wbRdNz

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

/-! ## Signal-level wb_en form

  Restated using `wbEnSignal` (matches SoC.lean's call site):
  trap at cycle t → wbEnSignal at cycle t+1 = false. -/

/-- `(a &&& b).val t = a.val t && b.val t` for Signal Bool. -/
private theorem wb_signal_and_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := by
  show (Signal.ap (Signal.map (· && ·) a) b).val t = _
  rfl

theorem trap_suppresses_wb_en_sig {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_regWrite : Signal dom Bool) (wbRdNz : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    (wbEnSignal
      (exwbRegWSignal
        (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
        idex_regWrite)
      wbRdNz).atTime (t + 1) = false := by
  have h_regW := trap_suppresses_exwb_regW trap_taken dTLBMiss pendingWriteEn
    mmuBusy dMMURedirect idex_regWrite t h_trap
  unfold wbEnSignal Signal.atTime
  rw [wb_signal_and_val]
  rw [show (exwbRegWSignal
    (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)
    idex_regWrite).val (t + 1) = false from h_regW]
  rfl

/-! ## Cycle-N+2 wb_en suppression after trap

  Combines the downstream lemma `exwbRegW_false_when_idex_regW_false`
  (which only needs idex_regWrite at N+1 to be false) with the
  hypothesis that IDEX has been squashed at N+1, to conclude that
  wb_en is false at N+2.

  The hypothesis "idex_regWrite at N+1 = false" can be discharged
  by `trap_squashes_idex_next_cycle` plus the structural
  `squash_contains_trap_taken` bridge — but both live in
  Pipeline/FlushSquash.lean and would need importing here. We
  expose this lemma in the form that lets callers thread the
  IDEX-squash hypothesis directly. -/

/-- **idex_regWrite at N+1 = false → wb_en at N+2 = false.**

    Downstream half of the cycle-N+2 regfile-suppression chain.
    Combines `exwbRegW_false_when_idex_regW_false` with
    `wbEn_off_when_regW_off`. -/
theorem wbEn_false_when_idex_regW_false_next_cycle {dom : DomainConfig}
    (suppressEXWB idex_regWrite : Signal dom Bool)
    (wbRdNz : Signal dom Bool) (t : Nat)
    (h_no_idex_regW : idex_regWrite.atTime t = false) :
    (wbEnSignal (exwbRegWSignal suppressEXWB idex_regWrite) wbRdNz).atTime (t + 1) =
      false := by
  have h_regW := exwbRegW_false_when_idex_regW_false suppressEXWB idex_regWrite t
    h_no_idex_regW
  unfold wbEnSignal Signal.atTime
  rw [wb_signal_and_val]
  rw [show (exwbRegWSignal suppressEXWB idex_regWrite).val (t + 1) = false from h_regW]
  rfl

/-! ## Multi-cycle: trap at N → wb_en at N+2 = false

  Chains through three layers:

    1. `idexLatchSignal` (IDEX register-input):
       trap at N → squash at N → IDEX-Bool latch at N+1 = false.
       (Discharged via `trap_squashes_idex_next_cycle` from
       FlushSquash, with init = false.)

    2. `exwbRegWSignal`: idex_regWrite at N+1 = false → exwb_regW
       at N+2 = false. (`exwbRegW_false_when_idex_regW_false`.)

    3. `wbEnSignal`: exwb_regW at N+2 = false → wb_en at N+2 = false.
       (`wbEn_off_when_regW_off`.)

  This is the cycle-N+2 complement to `trap_suppresses_wb_en_sig`
  (cycle N+1). Together they extend regfile-write suppression
  through 2 cycles.
-/

/-- **trap at N + freeze=false at N → wb_en at N+2 = false (when wired
    through idexLatchSignal then exwbRegWSignal then wbEnSignal).**

    Hypotheses on the structural shape:
    - `h_squash_includes_trap`: trap_taken.atTime N = true →
      squash.atTime N = true. (Discharged in callers via
      `squash_contains_trap_taken` from FlushSquash.)
    - `idex_regWrite_at_N1_is_idex_latch`: at N+1, idex_regWrite
      equals the idex latch's output. (Wired in callers; here we
      take it as a hypothesis.) -/
theorem trap_suppresses_wb_en_at_N_plus_2 {dom : DomainConfig}
    (trap_taken freeze squash : Signal dom Bool)
    (suppressEXWB : Signal dom Bool)
    (idex_regWrite_old idex_regWrite_new : Signal dom Bool)
    (wbRdNz : Signal dom Bool) (n : Nat)
    (h_trap_n : trap_taken.atTime n = true)
    (h_no_freeze_n : freeze.atTime n = false)
    (h_squash_includes_trap :
      trap_taken.atTime n = true → squash.atTime n = true)
    -- Wire idex_regWrite := idexLatchSignal freeze squash old new false.
    (h_idex_regWrite_at_N1 :
      idex_regWrite_new.atTime (n + 1) =
        (idexLatchSignal freeze squash idex_regWrite_old idex_regWrite_new
          (false : Bool)).atTime (n + 1)) :
    (wbEnSignal (exwbRegWSignal suppressEXWB idex_regWrite_new) wbRdNz).atTime
      (n + 2) = false := by
  -- Step 1: IDEX-Bool latch at N+1 = false (squash with init=false).
  have h_idex_n1_init :
    (idexLatchSignal freeze squash idex_regWrite_old idex_regWrite_new
      (false : Bool)).atTime (n + 1) = false := by
    apply trap_squashes_idex_next_cycle freeze squash trap_taken
      idex_regWrite_old idex_regWrite_new false n
    · exact h_squash_includes_trap
    · exact h_trap_n
    · exact h_no_freeze_n
  -- Step 2: idex_regWrite at N+1 = false (by wire-def).
  have h_idex_regWrite_n1_false : idex_regWrite_new.atTime (n + 1) = false := by
    rw [h_idex_regWrite_at_N1]
    exact h_idex_n1_init
  -- Step 3: wbEn at N+2 = false (via downstream lemma).
  exact wbEn_false_when_idex_regW_false_next_cycle suppressEXWB idex_regWrite_new
    wbRdNz (n + 1) h_idex_regWrite_n1_false

/-! ## LTL form -/

/-- **LTL form of `wbEn_false_when_idex_regW_false_next_cycle`.** -/
theorem wbEn_false_when_idex_regW_false_next_cycle_LTL {dom : DomainConfig}
    (suppressEXWB idex_regWrite : Signal dom Bool)
    (wbRdNz : Signal dom Bool) :
    ∀ t, idex_regWrite.atTime t = false →
         (wbEnSignal (exwbRegWSignal suppressEXWB idex_regWrite) wbRdNz).atTime (t + 1) =
           false :=
  fun t => wbEn_false_when_idex_regW_false_next_cycle suppressEXWB idex_regWrite wbRdNz t

/-- **∀N form of `trap_suppresses_wb_en_at_N_plus_2`.** -/
theorem trap_suppresses_wb_en_at_N_plus_2_LTL {dom : DomainConfig}
    (trap_taken freeze squash : Signal dom Bool)
    (suppressEXWB : Signal dom Bool)
    (idex_regWrite_old idex_regWrite_new : Signal dom Bool)
    (wbRdNz : Signal dom Bool)
    (h_squash_includes_trap :
      ∀ n, trap_taken.atTime n = true → squash.atTime n = true)
    (h_idex_regWrite_at_N1 :
      ∀ n, idex_regWrite_new.atTime (n + 1) =
        (idexLatchSignal freeze squash idex_regWrite_old idex_regWrite_new
          (false : Bool)).atTime (n + 1)) :
    ∀ n, trap_taken.atTime n = true → freeze.atTime n = false →
         (wbEnSignal (exwbRegWSignal suppressEXWB idex_regWrite_new) wbRdNz).atTime
           (n + 2) = false :=
  fun n h_trap_n h_no_freeze_n =>
    trap_suppresses_wb_en_at_N_plus_2 trap_taken freeze squash suppressEXWB
      idex_regWrite_old idex_regWrite_new wbRdNz n h_trap_n h_no_freeze_n
      (h_squash_includes_trap n) (h_idex_regWrite_at_N1 n)

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
