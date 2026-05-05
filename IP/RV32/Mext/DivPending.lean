/-
  RV32 divider-pending state tracking — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1104..1114, 1722..1725).
  The multi-cycle DIV/REM circuit is gated by a `divPending`
  state bit:

    divWanted    = idex_isMext ∧ isDivOp
    divStart     = divWanted ∧ ¬divPending           (rising edge)
    divStall     = divWanted ∧ ¬(divPending ∧ divDone) (un-stall on done)

    divPendingNext = if flushOrDelay then false      (abort on flush)
                     else if divStart then true       (latch start)
                     else if divDone  then false      (clear on done)
                     else divPending                  (hold)

  This file proves:
    * Per-source priority of `divPendingNext`.
    * `divStart` fires exactly when the divider is being kicked off
      (divWanted but not already pending).
    * `divStall` correctly accounts for the one-cycle "done" pulse:
      stalls cleared on the cycle the result is valid.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Mext

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure decoders -/

/-- divWanted: the IDEX-stage instruction is a DIV/REM. -/
@[inline] def divWantedPure (isMext isDivOp : Bool) : Bool :=
  isMext && isDivOp

/-- divStart: kick the divider on the first cycle of a DIV/REM. -/
@[inline] def divStartPure (divWanted divPending : Bool) : Bool :=
  divWanted && !divPending

/-- divStall: hold the pipeline until the divider's done pulse. -/
@[inline] def divStallPure (divWanted divPending divDone : Bool) : Bool :=
  divWanted && !(divPending && divDone)

/-- 4-way priority next-state for divPending. -/
@[inline] def divPendingNextPure
    (flushOrDelay divStart divDone divPending : Bool) : Bool :=
  if flushOrDelay then false
  else if divStart then true
  else if divDone then false
  else divPending

/-! ## Spec invariants — closed by `decide` -/

/-- Flush always clears divPending (abort on flush). -/
@[simp] theorem divPending_flush_clears
    (divStart divDone divPending : Bool) :
    divPendingNextPure true divStart divDone divPending = false := by rfl

/-- Start (no flush) sets divPending. -/
@[simp] theorem divPending_start_sets
    (divDone divPending : Bool) :
    divPendingNextPure false true divDone divPending = true := by rfl

/-- Done (no flush, no start) clears divPending. -/
@[simp] theorem divPending_done_clears (divPending : Bool) :
    divPendingNextPure false false true divPending = false := by rfl

/-- No event → hold. -/
@[simp] theorem divPending_hold (divPending : Bool) :
    divPendingNextPure false false false divPending = divPending := by rfl

/-! ### divStart spec -/

/-- divStart only fires when divWanted is true. -/
theorem divStart_requires_wanted (divPending : Bool) :
    divStartPure false divPending = false := by rfl

/-- divStart only fires when divPending is false. -/
theorem divStart_requires_not_pending (divWanted : Bool) :
    divStartPure divWanted true = false := by
  unfold divStartPure
  cases divWanted <;> rfl

/-- divStart fires when wanted ∧ !pending. -/
theorem divStart_fires : divStartPure true false = true := by rfl

/-! ### divStall spec -/

/-- divStall only fires when divWanted is true. -/
theorem divStall_requires_wanted (divPending divDone : Bool) :
    divStallPure false divPending divDone = false := by rfl

/-- divStall is cleared on the done pulse (when divPending ∧ divDone). -/
theorem divStall_done_unstalls (divWanted : Bool) :
    divStallPure divWanted true true = false := by
  unfold divStallPure
  cases divWanted <;> rfl

/-- divStall fires while a DIV is in flight (pending, not yet done). -/
theorem divStall_in_flight :
    divStallPure true true false = true := by rfl

/-- divStall fires on the start cycle (wanted, no pending yet). -/
theorem divStall_start_cycle (divDone : Bool) :
    divStallPure true false divDone = true := by
  unfold divStallPure
  cases divDone <;> rfl

/-! ## Composite specs -/

theorem divPendingNextPure_spec
    (flushOrDelay divStart divDone divPending : Bool) :
    divPendingNextPure flushOrDelay divStart divDone divPending =
      (if flushOrDelay then false
       else if divStart then true
       else if divDone then false
       else divPending) := by rfl

/-! ## Signal-level wrappers -/

def divWantedSignal {dom : DomainConfig}
    (isMext isDivOp : Signal dom Bool) : Signal dom Bool :=
  isMext &&& isDivOp

def divStartSignal {dom : DomainConfig}
    (divWanted divPending : Signal dom Bool) : Signal dom Bool :=
  divWanted &&& (~~~divPending)

def divStallSignal {dom : DomainConfig}
    (divWanted divPending divDone : Signal dom Bool) : Signal dom Bool :=
  divWanted &&& (~~~(divPending &&& divDone))

def divPendingNextSignal {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool)
    : Signal dom Bool :=
  Signal.mux flushOrDelay (Signal.pure false)
    (Signal.mux divStart (Signal.pure true)
      (Signal.mux divDone (Signal.pure false) divPending))

/-! ## Sequential divPendingReg

  divPendingReg is held in a `Signal.register false
  divPendingNextSignal`. This module adds the cycle-wise
  sequential statements.

  Key fact for invariant E: when `flushOrDelay` (which includes
  trap_taken via flush ⊆ flushOrDelay) fires at cycle t,
  divPendingReg at t+1 is forced to false — so a trap-aborted
  divide doesn't leave a stale "pending" flag that would gate
  the next instruction.
-/

/-- divPendingReg signal wrapper. -/
def divPendingRegSignal {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) : Signal dom Bool :=
  Signal.register false (divPendingNextSignal flushOrDelay divStart divDone divPending)

/-- **flushOrDelay at t → divPendingReg at t+1 = false.** -/
theorem divPendingReg_clears_on_flush {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) (t : Nat)
    (h_flush : flushOrDelay.val t = true) :
    (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) = false := by
  unfold divPendingRegSignal
  show (Signal.register false _).val (t + 1) = false
  show (divPendingNextSignal flushOrDelay divStart divDone divPending).val t = false
  unfold divPendingNextSignal Signal.mux
  show (if flushOrDelay.val t then _ else _) = false
  rw [h_flush]
  rfl

/-- **divStart at t (no flush) → divPendingReg at t+1 = true.** -/
theorem divPendingReg_set_on_start {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) (t : Nat)
    (h_no_flush : flushOrDelay.val t = false)
    (h_start : divStart.val t = true) :
    (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) = true := by
  unfold divPendingRegSignal
  show (Signal.register false _).val (t + 1) = true
  show (divPendingNextSignal flushOrDelay divStart divDone divPending).val t = true
  unfold divPendingNextSignal Signal.mux
  show (if flushOrDelay.val t then _ else
    (if divStart.val t then _ else _)) = true
  rw [h_no_flush, h_start]
  rfl

/-- **divDone at t (no flush, no start) → divPendingReg at t+1 = false.** -/
theorem divPendingReg_clears_on_done {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) (t : Nat)
    (h_no_flush : flushOrDelay.val t = false)
    (h_no_start : divStart.val t = false)
    (h_done : divDone.val t = true) :
    (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) = false := by
  unfold divPendingRegSignal
  show (Signal.register false _).val (t + 1) = false
  show (divPendingNextSignal flushOrDelay divStart divDone divPending).val t = false
  unfold divPendingNextSignal Signal.mux
  show (if flushOrDelay.val t then _ else
    (if divStart.val t then _ else
      (if divDone.val t then _ else _))) = false
  rw [h_no_flush, h_no_start, h_done]
  rfl

/-- **No event at t → divPendingReg at t+1 = divPending.val t.** -/
theorem divPendingReg_hold_when_no_event {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) (t : Nat)
    (h_no_flush : flushOrDelay.val t = false)
    (h_no_start : divStart.val t = false)
    (h_no_done : divDone.val t = false) :
    (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) =
      divPending.val t := by
  unfold divPendingRegSignal
  show (Signal.register false _).val (t + 1) = _
  show (divPendingNextSignal flushOrDelay divStart divDone divPending).val t = _
  unfold divPendingNextSignal Signal.mux
  show (if flushOrDelay.val t then _ else
    (if divStart.val t then _ else
      (if divDone.val t then _ else divPending.val t))) = divPending.val t
  rw [h_no_flush, h_no_start, h_no_done]
  rfl

/-! ## Cycle-N+2 divPending stays false across trap

  After a trap at N (or any flushOrDelay event), divPending=false
  at N+1 (via `divPendingReg_clears_on_flush`). At cycle N+1
  with no flush/start/done events, the hold-arm preserves false.

  This certifies that a trap-aborted divide doesn't leave a
  stale "pending" flag through cycle N+2 either. -/

/-- **flushOrDelay at N + no events at N+1 → divPending at N+2 = false.** -/
theorem divPendingReg_stays_false_at_N_plus_2 {dom : DomainConfig}
    (flushOrDelay divStart divDone : Signal dom Bool) (t : Nat)
    (h_flush_n : flushOrDelay.val t = true)
    (h_no_flush_n1 : flushOrDelay.val (t + 1) = false)
    (h_no_start_n1 : divStart.val (t + 1) = false)
    (h_no_done_n1 : divDone.val (t + 1) = false) :
    -- Build the recursive register signal, mirroring the SoC's
    -- divPending = register false (divPendingNextSignal flushOrDelay
    -- divStart divDone divPending).
    (divPendingRegSignal flushOrDelay divStart divDone
      (divPendingRegSignal flushOrDelay divStart divDone (Signal.pure false))).val
        (t + 2) = false := by
  -- Step 1: At cycle N, flush fires → inner reg at N+1 = false.
  have h_inner_n1 :
    (divPendingRegSignal flushOrDelay divStart divDone (Signal.pure false)).val (t + 1) =
      false :=
    divPendingReg_clears_on_flush flushOrDelay divStart divDone _ t h_flush_n
  -- Step 2: At cycle N+1, no events → outer reg at N+2 = inner reg at N+1.
  have h_outer := divPendingReg_hold_when_no_event flushOrDelay divStart divDone
    (divPendingRegSignal flushOrDelay divStart divDone (Signal.pure false))
    (t + 1) h_no_flush_n1 h_no_start_n1 h_no_done_n1
  show (divPendingRegSignal _ _ _ _).val (t + 2) = _
  rw [h_outer]
  exact h_inner_n1

/-! ## LTL forms for divPendingReg cycle-N+1 lemmas -/

/-- **LTL form of `divPendingReg_clears_on_flush`.** -/
theorem divPendingReg_clears_on_flush_LTL {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) :
    ∀ t, flushOrDelay.val t = true →
         (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) = false :=
  fun t => divPendingReg_clears_on_flush flushOrDelay divStart divDone divPending t

/-- **LTL form of `divPendingReg_set_on_start`.** -/
theorem divPendingReg_set_on_start_LTL {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) :
    ∀ t, flushOrDelay.val t = false → divStart.val t = true →
         (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) = true :=
  fun t => divPendingReg_set_on_start flushOrDelay divStart divDone divPending t

/-- **LTL form of `divPendingReg_clears_on_done`.** -/
theorem divPendingReg_clears_on_done_LTL {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) :
    ∀ t, flushOrDelay.val t = false → divStart.val t = false → divDone.val t = true →
         (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) = false :=
  fun t => divPendingReg_clears_on_done flushOrDelay divStart divDone divPending t

/-- **LTL form of `divPendingReg_hold_when_no_event`.** -/
theorem divPendingReg_hold_when_no_event_LTL {dom : DomainConfig}
    (flushOrDelay divStart divDone divPending : Signal dom Bool) :
    ∀ t, flushOrDelay.val t = false → divStart.val t = false → divDone.val t = false →
         (divPendingRegSignal flushOrDelay divStart divDone divPending).val (t + 1) =
           divPending.val t :=
  fun t => divPendingReg_hold_when_no_event flushOrDelay divStart divDone divPending t

/-- **∀N form of `divPendingReg_stays_false_at_N_plus_2`.** -/
theorem divPendingReg_stays_false_at_N_plus_2_LTL {dom : DomainConfig}
    (flushOrDelay divStart divDone : Signal dom Bool) :
    ∀ n, flushOrDelay.val n = true →
         flushOrDelay.val (n + 1) = false →
         divStart.val (n + 1) = false →
         divDone.val (n + 1) = false →
         (divPendingRegSignal flushOrDelay divStart divDone
           (divPendingRegSignal flushOrDelay divStart divDone (Signal.pure false))).val
             (n + 2) = false :=
  fun n => divPendingReg_stays_false_at_N_plus_2 flushOrDelay divStart divDone n

end Sparkle.IP.RV32.Mext
