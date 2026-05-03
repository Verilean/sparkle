/-
  RV32 EX/WB suppression — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`. The `suppressEXWB` signal gates
  every side-effect-bearing latch on the EX→WB pipeline edge: when
  asserted, the in-flight IDEX instruction does NOT advance into EXWB
  (its register write, store, CSR write, etc. are all dropped).

  This is the single most consequential signal in the trap path: if
  `suppressEXWB` is wrong, an aborted instruction may commit anyway
  (or vice versa), breaking trap semantics. The recent IDEX-validity
  fix (commit 01c7177) and the dMMURedirect fix (commit 0e14494) both
  hinge on this signal's spec.

  Spec (from current SoC.lean):

      suppressEXWB =
        trap_taken              -- async or sync trap fires this cycle
      ∨ dTLBMiss                -- d-side TLB miss this cycle
      ∨ holdEX                  -- pendingWrite or MMU PTW busy
      ∨ dMMURedirect            -- MMU FSM transitions to DONE this cycle

      where holdEX = pendingWriteEn ∨ mmuBusy

  This module captures that boolean expression as a pure function and
  proves the obvious invariants. The interesting *negative* spec
  question — "does suppressEXWB also gate dmem_we?" — is asked but
  not yet answered here; see the comment block at the bottom.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure boolean expressions -/

/-- `holdEX = pendingWriteEn ∨ mmuBusy`. -/
@[inline] def holdEXPure (pendingWriteEn mmuBusy : Bool) : Bool :=
  pendingWriteEn || mmuBusy

/-- `suppressEXWB = trap_taken ∨ dTLBMiss ∨ holdEX ∨ dMMURedirect`. -/
@[inline] def suppressEXWBPure
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Bool)
    : Bool :=
  trap_taken || (dTLBMiss || holdEXPure pendingWriteEn mmuBusy)
    || dMMURedirect

/-- `validEX = ¬suppressEXWB`. -/
@[inline] def validEXPure
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Bool)
    : Bool :=
  !suppressEXWBPure trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect

/-! ## Spec invariants — closed by `decide` over Bool⁵ (32 cases) -/

/-- A trap suppresses EX→WB. -/
@[simp] theorem suppressEXWB_trap
    (dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Bool) :
    suppressEXWBPure true dTLBMiss pendingWriteEn mmuBusy dMMURedirect = true := by
  revert dTLBMiss pendingWriteEn mmuBusy dMMURedirect; decide

/-- A d-side TLB miss suppresses EX→WB. -/
@[simp] theorem suppressEXWB_dTLBMiss
    (trap_taken pendingWriteEn mmuBusy dMMURedirect : Bool) :
    suppressEXWBPure trap_taken true pendingWriteEn mmuBusy dMMURedirect = true := by
  revert trap_taken pendingWriteEn mmuBusy dMMURedirect; decide

/-- A pending DRAM write (AMO writeback in flight) suppresses EX→WB. -/
@[simp] theorem suppressEXWB_pendingWrite
    (trap_taken dTLBMiss mmuBusy dMMURedirect : Bool) :
    suppressEXWBPure trap_taken dTLBMiss true mmuBusy dMMURedirect = true := by
  revert trap_taken dTLBMiss mmuBusy dMMURedirect; decide

/-- An MMU PTW in flight suppresses EX→WB. -/
@[simp] theorem suppressEXWB_mmuBusy
    (trap_taken dTLBMiss pendingWriteEn dMMURedirect : Bool) :
    suppressEXWBPure trap_taken dTLBMiss pendingWriteEn true dMMURedirect = true := by
  revert trap_taken dTLBMiss pendingWriteEn dMMURedirect; decide

/-- The MMU-redirect cycle suppresses EX→WB so the instruction that
    was in IDEX during PTW does not commit (the redirect re-fetches
    the faulting load, which will re-execute next cycle). -/
@[simp] theorem suppressEXWB_dMMURedirect
    (trap_taken dTLBMiss pendingWriteEn mmuBusy : Bool) :
    suppressEXWBPure trap_taken dTLBMiss pendingWriteEn mmuBusy true = true := by
  revert trap_taken dTLBMiss pendingWriteEn mmuBusy; decide

/-- When all five suppressors are clear, `validEX` is `true`. -/
@[simp] theorem validEX_normal_cycle :
    validEXPure false false false false false = true := by
  decide

/-- `validEX` is `false` if any suppressor fires. (Useful as a contrapositive
    of the five lemmas above.) -/
@[simp] theorem validEX_false_iff_any_suppressor
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Bool) :
    validEXPure trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect = false ↔
      (trap_taken || dTLBMiss || pendingWriteEn || mmuBusy || dMMURedirect) = true := by
  revert trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect; decide

/-! ## Composite spec -/

/--
  Exhaustive truth table for `suppressEXWBPure`. Closed by `decide`
  over 2⁵ = 32 input combinations. -/
theorem suppressEXWBPure_spec :
    ∀ (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Bool),
      suppressEXWBPure trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
        = (trap_taken || dTLBMiss || pendingWriteEn || mmuBusy || dMMURedirect) := by
  decide

/-! ## Signal-level wrappers -/

/-- Signal-level `holdEX`. -/
def holdEXSignal {dom : DomainConfig}
    (pendingWriteEn mmuBusy : Signal dom Bool) : Signal dom Bool :=
  pendingWriteEn ||| mmuBusy

/-- Signal-level `suppressEXWB`. -/
def suppressEXWBSignal {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
      : Signal dom Bool) : Signal dom Bool :=
  trap_taken |||
    (dTLBMiss ||| holdEXSignal pendingWriteEn mmuBusy)
      ||| dMMURedirect

/-- Signal-level `validEX`. -/
def validEXSignal {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
      : Signal dom Bool) : Signal dom Bool :=
  ~~~(suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect)

/-- Helper used in equivalence proofs: `(a ||| b).val t = a.val t || b.val t`. -/
private theorem signal_or_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a ||| b).val t = (a.val t || b.val t) := by
  show (Signal.ap (Signal.map (· || ·) a) b).val t = _
  rfl

/-- Helper: `(~~~a).val t = !(a.val t)`. -/
private theorem signal_not_val {dom : DomainConfig}
    (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := by
  show (Signal.map (fun x => !x) a).val t = _
  rfl

/-- Cycle-wise equivalence: Signal version equals pure version. -/
theorem suppressEXWBSignal_eq_pure {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
      : Signal dom Bool) (t : Nat) :
    (suppressEXWBSignal trap_taken dTLBMiss pendingWriteEn mmuBusy
       dMMURedirect).val t =
      suppressEXWBPure (trap_taken.val t) (dTLBMiss.val t)
        (pendingWriteEn.val t) (mmuBusy.val t) (dMMURedirect.val t) := by
  unfold suppressEXWBSignal holdEXSignal suppressEXWBPure holdEXPure
  simp [signal_or_val]

/-- Cycle-wise equivalence for `validEX`. -/
theorem validEXSignal_eq_pure {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
      : Signal dom Bool) (t : Nat) :
    (validEXSignal trap_taken dTLBMiss pendingWriteEn mmuBusy
       dMMURedirect).val t =
      validEXPure (trap_taken.val t) (dTLBMiss.val t)
        (pendingWriteEn.val t) (mmuBusy.val t) (dMMURedirect.val t) := by
  unfold validEXSignal validEXPure
  rw [signal_not_val]
  rw [suppressEXWBSignal_eq_pure]

/-! ## Open question — DRAM write asymmetry

  Throughout `SoC.lean`, all peripheral writes are gated on `validEX`:

      clintWE = idex_memWrite ∧ isCLINT_ex ∧ validEX
      mmioWE  = idex_memWrite ∧ is_mmio_ex ∧ validEX
      uartWE  = idex_memWrite ∧ isUART_ex ∧ validEX

  But the DRAM write is NOT:

      dmem_we = idex_memWrite ∧ isDMEM_ex ∧ ¬dTLBMiss ∧ ¬scExFails

  Note that `dmem_we` does include `¬dTLBMiss`, but does NOT mention
  `trap_taken`, `pendingWriteEn`, `mmuBusy`, or `dMMURedirect`.

  Is this a bug? Three sub-questions:

  1. **trap_taken**: a store in IDEX during a trap fires
     `dmem_we = 1` and writes to DRAM. After the trap returns via sret,
     the kernel re-executes from `mepc` (= the suppressed instruction's
     PC under fix 01c7177), which re-runs the store. If the inputs
     (sp, store value) are stable across the trap save/restore, this
     is idempotent. But: with our pipeline, are they?

  2. **pendingWriteEn / mmuBusy**: while an AMO writeback or PTW is in
     flight, IDEX is supposed to be frozen (`freezeIDEX`). But the
     register-file-edit gating uses `suppressEXWB`, not `freezeIDEX`.
     Confirm by hand: when `pendingWriteEn = 1`, `freezeIDEX = 1`, so
     IDEX inst doesn't change cycle-to-cycle; but `dmem_we` is
     evaluated on the still-resident IDEX inst, and would re-fire
     every cycle. This is likely the intent (the AMO state machine
     parks the same store in IDEX until done), but worth verifying.

  3. **dMMURedirect**: at the redirect cycle, IDEX holds the post-load
     instruction; it should not commit. Like (1), `dmem_we` would
     fire if that post-load happened to be a store; the redirect
     re-runs the original load, which doesn't re-issue the store.
     So the post-load store would be committed exactly once — at
     the redirect cycle — when arguably the kernel/compiler would
     not have generated such a sequence anyway. Borderline.

  These are sequential invariants over the pipeline, not pure
  combinational. They belong in the next phase of the proof effort
  (see `docs/RV32_Architecture_Status.md` §2.2 invariant E).
-/

end Sparkle.IP.RV32.Pipeline
