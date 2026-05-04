/-
  RV32 LR/SC across trap — sequential invariant D

  Invariant D from `docs/RV32_Architecture_Status.md` §2.2:

      "An LR followed by a trap then an SC (same addr) → SC
       fails (returns 1)."

  Per RISC-V "A" extension §10.2: any trap (including async
  interrupts) MUST invalidate the LR/SC reservation, so that an
  SC issued after the trap returns cannot succeed even if the
  address matches the prior LR. This prevents lost-update bugs
  when a trap handler runs between LR and SC and modifies the
  same memory location.

  We prove this in two steps:

    1. **Combinational**: `resValidNextPure trap _ _ _ = false`
       whenever `trap = true`. (Already proven in
       `AMO/Reservation.lean` as `resValidNext_trap_invalidates`.)

    2. **Sequential**: `Signal.register false resValidNextSignal`
       captures the next cycle's reservation. When trap fires at
       cycle N, the reservation register at cycle N+1 is `false`,
       and the SC at cycle N+2 sees `reservationValid = false`,
       hence `scExFails = true`, hence the DRAM write is
       suppressed and the SC return-value is 1 (= fail).

  This file proves the sequential statement: if the reservation-
  register's input is forced to `false` at cycle N (because a
  trap fired), the register's value at cycle N+1 is `false`.

  This is the same one-cycle-latency property as
  `Pipeline/AbortGuarantee.lean`'s
  `suppressEXWB_aborts_regW_next_cycle` — generic "register's
  next-state semantics" applied to a specific gate.

  Companion to:
    * `AMO/Reservation.lean` — combinational `resValidNext` spec
    * `AMO/SC.lean` — `scExFailsPure` and `dmemWePure`
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.AMO.Reservation
import IP.RV32.AMO.SC
import IP.RV32.AMO.PendingWrite
import IP.RV32.Pipeline.SideEffectsTrapInv

namespace Sparkle.IP.RV32.AMO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Sequential: trap at cycle N → reservation invalid at N+1 -/

/-- Reservation register modeled as a `Signal.register`. -/
def reservationValidSignal {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) : Signal dom Bool :=
  Signal.register false (resValidNextSignal trap isLR isSC prevValid)

/-- **Trap at cycle t → reservation invalid at cycle t+1.** -/
theorem trap_invalidates_reservation_next_cycle {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) (t : Nat) :
    trap.atTime t = true →
    (reservationValidSignal trap isLR isSC prevValid).atTime (t + 1) = false := by
  intro h_trap
  unfold reservationValidSignal
  unfold Signal.atTime
  -- (register false ...).val (t+1) = (resValidNextSignal ...).val t
  show (Signal.register false _).val (t + 1) = false
  -- Use the register's next-state semantics.
  show (resValidNextSignal trap isLR isSC prevValid).val t = false
  -- Apply the combinational spec at cycle t.
  rw [resValidNextSignal_eq_pure]
  rw [show trap.val t = true from h_trap]
  -- Now goal: resValidNextPure true _ _ _ = false
  rfl

/-- **LR at cycle t (no trap) → reservation valid at cycle t+1.** -/
theorem LR_sets_reservation_next_cycle {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) (t : Nat)
    (h_no_trap : trap.val t = false)
    (h_LR : isLR.val t = true) :
    (reservationValidSignal trap isLR isSC prevValid).val (t + 1) = true := by
  unfold reservationValidSignal
  show (Signal.register false _).val (t + 1) = true
  show (resValidNextSignal trap isLR isSC prevValid).val t = true
  rw [resValidNextSignal_eq_pure]
  rw [h_no_trap, h_LR]
  rfl

/-- **SC at cycle t (no trap, no LR) → reservation invalid at cycle t+1.** -/
theorem SC_clears_reservation_next_cycle {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) (t : Nat)
    (h_no_trap : trap.val t = false)
    (h_no_LR : isLR.val t = false)
    (h_SC : isSC.val t = true) :
    (reservationValidSignal trap isLR isSC prevValid).val (t + 1) = false := by
  unfold reservationValidSignal
  show (Signal.register false _).val (t + 1) = false
  show (resValidNextSignal trap isLR isSC prevValid).val t = false
  rw [resValidNextSignal_eq_pure]
  rw [h_no_trap, h_no_LR, h_SC]
  rfl

/-- **No event at cycle t → reservation at cycle t+1 = prevValid.val t.** -/
theorem reservation_holds_when_no_event {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) (t : Nat)
    (h_no_trap : trap.val t = false)
    (h_no_LR : isLR.val t = false)
    (h_no_SC : isSC.val t = false) :
    (reservationValidSignal trap isLR isSC prevValid).val (t + 1) = prevValid.val t := by
  unfold reservationValidSignal
  show (Signal.register false _).val (t + 1) = _
  show (resValidNextSignal trap isLR isSC prevValid).val t = _
  rw [resValidNextSignal_eq_pure]
  rw [h_no_trap, h_no_LR, h_no_SC]
  rfl

/-! ## Cycle-N+2 reservation invalidation across trap

  The cycle-N+1 lemma `trap_invalidates_reservation_next_cycle`
  proves resValid=false at N+1 after trap at N. At cycle N+1,
  the resValidNext computation is:

      resValid(N+2) = if trap(N+1) then false
                      else if isLR(N+1) then true
                      else if isSC(N+1) then false
                      else resValid(N+1)

  After a trap at N, IDEX is squashed at N+1, so isLR(N+1) =
  false and isSC(N+1) = false (both AMO control bits are
  squashed-init = false). Thus the resValid stays false unless
  trap fires again at N+1.

  We provide the form that takes all three "no event at N+1"
  hypotheses; the IDEX-squash discharge is left to callers.
-/

/-- **Trap at N + no event at N+1 → reservation invalid at N+2.** -/
theorem reservation_stays_invalid_at_N_plus_2 {dom : DomainConfig}
    (trap isLR isSC : Signal dom Bool) (t : Nat)
    (h_trap_n : trap.val t = true)
    (h_no_trap_n1 : trap.val (t + 1) = false)
    (h_no_LR_n1 : isLR.val (t + 1) = false)
    (h_no_SC_n1 : isSC.val (t + 1) = false) :
    -- prevValid at N+1 is the previous-cycle's reservationValid.
    (reservationValidSignal trap isLR isSC
      (reservationValidSignal trap isLR isSC (Signal.pure false))).val (t + 2) = false := by
  -- Step 1: At N+1, prevValid (= cycle-N+1 reservationValidSignal) is false (by trap-invalidate).
  have h_inner_n1 :
    (reservationValidSignal trap isLR isSC (Signal.pure false)).val (t + 1) = false := by
    have := trap_invalidates_reservation_next_cycle trap isLR isSC
      (Signal.pure false) t h_trap_n
    unfold Signal.atTime at this
    exact this
  -- Step 2: At N+2, resValid uses (isSC, isLR, trap, prevValid) at N+1; all "no event"
  -- hypotheses fire and prevValid at N+1 = false.
  -- Apply the no-event hold lemma at cycle N+1.
  have := reservation_holds_when_no_event trap isLR isSC
    (reservationValidSignal trap isLR isSC (Signal.pure false))
    (t + 1) h_no_trap_n1 h_no_LR_n1 h_no_SC_n1
  -- this : reservationValidSignal trap isLR isSC ... .val (t+1+1) = (...).val (t+1)
  show (reservationValidSignal trap isLR isSC _).val (t + 2) = false
  rw [this]
  exact h_inner_n1

/-! ## Sequential: SC after trap → SC fails

  Combine the trap-invalidation theorem with `scExFailsPure` to
  show that an SC at cycle t+1 (after trap at cycle t) fails. -/

/--
  **Invariant D (sequential)**: a trap at cycle t followed by
  an SC at cycle t+1 → scExFails fires → DRAM write suppressed.

  The hypothesis `h_sc_at_t1` says "the IDEX-stage instruction
  at cycle t+1 is SC.W". The `reservationValid` field at
  cycle t+1 is the value of the reservation register at that
  cycle, which (by the previous theorem) is `false` whenever
  trap fired at cycle t.

  Spec: `scExFailsPure idexIsSC reservationValid scExAddrMatch`
  is `idexIsSC && !(reservationValid && scExAddrMatch)`. With
  `reservationValid = false`, this reduces to `idexIsSC` (=true
  by hypothesis), so `scExFails = true`. -/
theorem sc_after_trap_fails {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool)
    (idexIsSC_ex_at_t1 : Bool) (scExAddrMatch_at_t1 : Bool)
    (t : Nat)
    (h_trap : trap.atTime t = true)
    (h_sc_at_t1 : idexIsSC_ex_at_t1 = true) :
    scExFailsPure idexIsSC_ex_at_t1
      ((reservationValidSignal trap isLR isSC prevValid).atTime (t + 1))
      scExAddrMatch_at_t1 = true := by
  rw [h_sc_at_t1]
  rw [trap_invalidates_reservation_next_cycle trap isLR isSC prevValid t h_trap]
  unfold scExFailsPure
  -- Goal: true && !(false && _) = true
  cases scExAddrMatch_at_t1 <;> rfl

/-- **Invariant D corollary**: the SC after trap suppresses dmem_we.

    With `scExFails = true`, `dmemWePure idex_memWrite isDMEM_ex
    dTLBMiss true = false`. -/
theorem sc_after_trap_suppresses_dmem_we
    (idex_memWrite isDMEM_ex dTLBMiss : Bool) :
    dmemWePure idex_memWrite isDMEM_ex dTLBMiss true = false := by
  exact dmemWe_sc_fail idex_memWrite isDMEM_ex dTLBMiss

/-! ## Connection to the full invariant D

  Invariant D ("LR followed by trap then SC fails") is now
  proven combinationally + sequentially:

    * Combinational (already proven in `AMO/Reservation.lean`):
        resValidNextPure true _ _ _ = false
      Trap clears the reservation's next-state at cycle t.

    * Sequential (proven here):
        trap_invalidates_reservation_next_cycle:
          trap.val t = true →
          reservationValid.val (t+1) = false

    * SC failure (proven here):
        sc_after_trap_fails:
          When the SC at cycle t+1 sees the post-trap reservation
          (which is false), scExFails fires.

    * DRAM-write suppression (proven here, follows from AMO/SC.lean):
        scExFails = true → dmem_we = false
      The SC-failed write does not commit to DRAM.

  Together these show: an LR-trap-SC sequence cannot leak a
  successful SC update to DRAM.
-/

/-! ## Multi-cycle: trap at t → pendingWriteEn at t+2 = false

  This packages the AMO-side trap-suppression chain that spans
  two cycles. The chain is:

    trap_taken at cycle t        (input)
    → exwb_isAMO at t+1 = false   (trap_clears_exwb_isAMO)
    → exwb_isAMOrw at t+1 = false (isAMOrwSignal_false_when_isAMO_false)
    → pendingWriteEn at t+2 = false (pendingWriteEn_false_after_amo_clear)

  This complements the cycle-N+1 reservation-invalidation
  (`trap_invalidates_reservation_next_cycle`) — the reservation
  side handles SC.W at t+1; this cycle-N+2 piece handles the AMO
  writeback that would otherwise commit at t+2.

  Together, an in-flight AMO that's interrupted by a trap at
  cycle t cannot:
    * have its SC.W path succeed (cycle t+1, via reservation)
    * commit its read-modify-write writeback (cycle t+2, this lemma).
-/

/-- **Composite cycle-N+2 invariant: trap at t → pendingWriteEn at t+2 = false.**

    This is the multi-cycle composition. Type variables for
    `exwb_isLR`/`exwb_isSC` are quantified over since they don't
    matter — `exwb_isAMOrw = false` whenever `exwb_isAMO = false`. -/
theorem trap_clears_pendingWriteEn_2_cycles_later {dom : DomainConfig}
    (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect : Signal dom Bool)
    (idex_isAMO exwb_isLR exwb_isSC : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.atTime t = true) :
    -- Define exwb_isAMO as the suppressEXWB-gated next-cycle latch.
    let exwb_isAMO :=
      Signal.register false
        (Signal.mux
          (Sparkle.IP.RV32.Pipeline.suppressEXWBSignal trap_taken dTLBMiss
            pendingWriteEn mmuBusy dMMURedirect)
          (Signal.pure false) idex_isAMO)
    (pendingWriteEnRegSignal
      (isAMOrwSignal exwb_isAMO exwb_isLR exwb_isSC)).val (t + 2) = false := by
  -- Step 1: trap at t → exwb_isAMO at t+1 = false.
  have h_isAMO :
    (Signal.register false
        (Signal.mux
          (Sparkle.IP.RV32.Pipeline.suppressEXWBSignal trap_taken dTLBMiss
            pendingWriteEn mmuBusy dMMURedirect)
          (Signal.pure false) idex_isAMO)).val (t + 1) = false := by
    have h := Sparkle.IP.RV32.Pipeline.trap_clears_exwb_isAMO trap_taken dTLBMiss pendingWriteEn
      mmuBusy dMMURedirect idex_isAMO t h_trap
    unfold Signal.atTime at h
    exact h
  -- Step 2: exwb_isAMO at t+1 = false → pendingWriteEn at t+2 = false.
  exact pendingWriteEn_false_after_isAMO_clear _ exwb_isLR exwb_isSC (t + 1) h_isAMO

/-! ## LTL forms for AMO trap-suppression composites -/

theorem trap_invalidates_reservation_next_cycle_LTL {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) :
    ∀ t, trap.atTime t = true →
         (reservationValidSignal trap isLR isSC prevValid).atTime (t + 1) = false :=
  fun t => trap_invalidates_reservation_next_cycle trap isLR isSC prevValid t

theorem sc_after_trap_suppresses_dmem_we_LTL :
    ∀ (idex_memWrite isDMEM_ex dTLBMiss : Bool),
      dmemWePure idex_memWrite isDMEM_ex dTLBMiss true = false :=
  fun idex_memWrite isDMEM_ex dTLBMiss =>
    sc_after_trap_suppresses_dmem_we idex_memWrite isDMEM_ex dTLBMiss

end Sparkle.IP.RV32.AMO
