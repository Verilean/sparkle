/-
  RV32 MMU FSM next-state — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1718..1725). The MMU
  driver's state machine encodes whether translation is in
  progress, completed, or faulted.

  States:
    0 IDLE     no translation in flight
    2 PTW_WALK PTW has the bus
    3 DONE     translation completed; D-side will redirect
    4 FAULT    page fault

  Transitions (D-side only — I-side is handled separately):

    From IDLE:
      dTLBMiss → PTW_WALK (state 2)
      else    → IDLE      (hold)

    From PTW_WALK:
      ptwIsDone  → DONE   (state 3)
      ptwIsFault → FAULT  (state 4)
      else       → PTW_WALK (hold while PTW progresses)

    From any other state (DONE/FAULT/2-cycle pulse):
      → IDLE  (one-cycle pulse, then back to IDLE)

  This is the structure that makes `dMMURedirect` and the trap
  signals fire for exactly one cycle, after which the MMU is
  ready for the next translation.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.MMU.State

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure FSM transitions -/

/-- Next state when in IDLE. -/
@[inline] def mmuNextFromIdlePure (dTLBMiss : Bool) : BitVec 3 :=
  if dTLBMiss then 2#3 else 0#3

/-- Next state when in PTW_WALK. -/
@[inline] def mmuNextFromWalkPure (ptwIsDone ptwIsFault : Bool) : BitVec 3 :=
  if ptwIsDone then 3#3
  else if ptwIsFault then 4#3
  else 2#3

/-- Top-level MMU state next: dispatch by current state.
    DONE/FAULT/other → IDLE (one-cycle pulse). -/
@[inline] def mmuStateNextPure
    (mmuState : BitVec 3) (dTLBMiss ptwIsDone ptwIsFault : Bool) : BitVec 3 :=
  if isMMUIdlePure mmuState then mmuNextFromIdlePure dTLBMiss
  else if isPTWWalkPure mmuState then mmuNextFromWalkPure ptwIsDone ptwIsFault
  else 0#3

/-! ## Spec invariants — closed by `decide` / `bv_decide` -/

/-- IDLE + no miss → IDLE. -/
@[simp] theorem mmu_idle_no_miss_holds (ptwIsDone ptwIsFault : Bool) :
    mmuStateNextPure 0#3 false ptwIsDone ptwIsFault = 0#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure mmuNextFromIdlePure
  rfl

/-- IDLE + miss → WALK (state 2). -/
@[simp] theorem mmu_idle_miss_starts_walk (ptwIsDone ptwIsFault : Bool) :
    mmuStateNextPure 0#3 true ptwIsDone ptwIsFault = 2#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure mmuNextFromIdlePure
  rfl

/-- WALK + ptwDone → DONE (state 3). -/
@[simp] theorem mmu_walk_ptw_done (dTLBMiss ptwIsFault : Bool) :
    mmuStateNextPure 2#3 dTLBMiss true ptwIsFault = 3#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure mmuNextFromWalkPure
  rfl

/-- WALK + ptwFault → FAULT (state 4). -/
@[simp] theorem mmu_walk_ptw_fault (dTLBMiss : Bool) :
    mmuStateNextPure 2#3 dTLBMiss false true = 4#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure mmuNextFromWalkPure
  rfl

/-- WALK + ptw busy (neither done nor fault) → WALK (hold). -/
@[simp] theorem mmu_walk_ptw_busy (dTLBMiss : Bool) :
    mmuStateNextPure 2#3 dTLBMiss false false = 2#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure mmuNextFromWalkPure
  rfl

/-- DONE → IDLE (one-cycle pulse). -/
@[simp] theorem mmu_done_to_idle (dTLBMiss ptwIsDone ptwIsFault : Bool) :
    mmuStateNextPure 3#3 dTLBMiss ptwIsDone ptwIsFault = 0#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure
  rfl

/-- FAULT → IDLE (one-cycle pulse). -/
@[simp] theorem mmu_fault_to_idle (dTLBMiss ptwIsDone ptwIsFault : Bool) :
    mmuStateNextPure 4#3 dTLBMiss ptwIsDone ptwIsFault = 0#3 := by
  unfold mmuStateNextPure isMMUIdlePure isPTWWalkPure
  rfl

/-! ## Reachability invariants

  These prove that legitimate MMU states are stable under one
  next-state step (with the right inputs). -/

/-- DONE always transitions to IDLE (regardless of inputs). -/
theorem mmu_done_always_idle :
    ∀ (dTLBMiss ptwIsDone ptwIsFault : Bool),
      mmuStateNextPure 3#3 dTLBMiss ptwIsDone ptwIsFault = 0#3 := by
  intros; rfl

/-- FAULT always transitions to IDLE. -/
theorem mmu_fault_always_idle :
    ∀ (dTLBMiss ptwIsDone ptwIsFault : Bool),
      mmuStateNextPure 4#3 dTLBMiss ptwIsDone ptwIsFault = 0#3 := by
  intros; rfl

/-- DONE/FAULT pulse: dMMURedirect (= DONE) ⇒ next state is IDLE.

    This is the "one-cycle pulse" property — after the redirect
    cycle, the MMU is ready for the next translation. -/
theorem mmu_dMMURedirect_pulses (dTLBMiss ptwIsDone ptwIsFault bypassMMU : Bool) :
    dMMURedirectPure 3#3 bypassMMU = !bypassMMU →
    mmuStateNextPure 3#3 dTLBMiss ptwIsDone ptwIsFault = 0#3 := by
  intros _; rfl

/-! ## Composite spec -/

theorem mmuStateNextPure_spec
    (mmuState : BitVec 3) (dTLBMiss ptwIsDone ptwIsFault : Bool) :
    mmuStateNextPure mmuState dTLBMiss ptwIsDone ptwIsFault =
      (if isMMUIdlePure mmuState then mmuNextFromIdlePure dTLBMiss
       else if isPTWWalkPure mmuState then mmuNextFromWalkPure ptwIsDone ptwIsFault
       else 0#3) := by
  rfl

/-! ## Signal-level wrappers -/

def mmuNextFromIdleSignal {dom : DomainConfig}
    (dTLBMiss : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.mux dTLBMiss (Signal.pure 2#3) (Signal.pure 0#3)

def mmuNextFromWalkSignal {dom : DomainConfig}
    (ptwIsDone ptwIsFault : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.mux ptwIsDone (Signal.pure 3#3)
    (Signal.mux ptwIsFault (Signal.pure 4#3) (Signal.pure 2#3))

def mmuStateNextSignal {dom : DomainConfig}
    (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool)
    : Signal dom (BitVec 3) :=
  Signal.mux isMMUIdle (mmuNextFromIdleSignal dTLBMiss)
    (Signal.mux isPTWWalk (mmuNextFromWalkSignal ptwIsDone ptwIsFault)
      (Signal.pure 0#3))

end Sparkle.IP.RV32.MMU
