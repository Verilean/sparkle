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

end Sparkle.IP.RV32.Mext
