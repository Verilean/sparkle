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

end Sparkle.IP.RV32.AMO
