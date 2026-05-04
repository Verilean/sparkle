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

/-! ## Sequential mmuStateReg

  Cycle-wise register lemmas for the MMU FSM state. The register
  next-state is the priority dispatch above; this section proves
  the per-arm sequential statements. -/

/-- mmuStateReg signal wrapper. -/
def mmuStateRegSignal {dom : DomainConfig}
    (init : BitVec 3) (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.register init
    (mmuStateNextSignal isMMUIdle isPTWWalk dTLBMiss ptwIsDone ptwIsFault)

/-- **IDLE + dTLBMiss at t → state at t+1 = WALK (= 2#3).** -/
theorem mmuStateReg_idle_to_walk_on_miss {dom : DomainConfig}
    (init : BitVec 3) (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool) (t : Nat)
    (h_idle : isMMUIdle.val t = true)
    (h_miss : dTLBMiss.val t = true) :
    (mmuStateRegSignal init isMMUIdle isPTWWalk
      dTLBMiss ptwIsDone ptwIsFault).val (t + 1) = 2#3 := by
  unfold mmuStateRegSignal mmuStateNextSignal mmuNextFromIdleSignal
  show (Signal.register init _).val (t + 1) = _
  -- (register init next).val (t+1) = next.val t.
  unfold Signal.mux
  show (if isMMUIdle.val t then _ else _) = _
  rw [h_idle]
  show (if dTLBMiss.val t then _ else _) = _
  rw [h_miss]
  rfl

/-- **IDLE + no miss at t → state at t+1 = IDLE (= 0#3).** -/
theorem mmuStateReg_idle_holds_no_miss {dom : DomainConfig}
    (init : BitVec 3) (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool) (t : Nat)
    (h_idle : isMMUIdle.val t = true)
    (h_no_miss : dTLBMiss.val t = false) :
    (mmuStateRegSignal init isMMUIdle isPTWWalk
      dTLBMiss ptwIsDone ptwIsFault).val (t + 1) = 0#3 := by
  unfold mmuStateRegSignal mmuStateNextSignal mmuNextFromIdleSignal
  show (Signal.register init _).val (t + 1) = _
  unfold Signal.mux
  show (if isMMUIdle.val t then _ else _) = _
  rw [h_idle]
  show (if dTLBMiss.val t then _ else _) = _
  rw [h_no_miss]
  rfl

/-- **WALK + ptwIsDone at t (no idle) → state at t+1 = DONE (= 3#3).** -/
theorem mmuStateReg_walk_to_done {dom : DomainConfig}
    (init : BitVec 3) (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool) (t : Nat)
    (h_no_idle : isMMUIdle.val t = false)
    (h_walk : isPTWWalk.val t = true)
    (h_done : ptwIsDone.val t = true) :
    (mmuStateRegSignal init isMMUIdle isPTWWalk
      dTLBMiss ptwIsDone ptwIsFault).val (t + 1) = 3#3 := by
  unfold mmuStateRegSignal mmuStateNextSignal mmuNextFromWalkSignal
  show (Signal.register init _).val (t + 1) = _
  unfold Signal.mux
  show (if isMMUIdle.val t then _ else _) = _
  rw [h_no_idle]
  show (if isPTWWalk.val t then _ else _) = _
  rw [h_walk]
  show (if ptwIsDone.val t then _ else _) = _
  rw [h_done]
  rfl

/-- **WALK + ptwIsFault at t (no idle, no done) → state at t+1 = FAULT (= 4#3).** -/
theorem mmuStateReg_walk_to_fault {dom : DomainConfig}
    (init : BitVec 3) (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool) (t : Nat)
    (h_no_idle : isMMUIdle.val t = false)
    (h_walk : isPTWWalk.val t = true)
    (h_no_done : ptwIsDone.val t = false)
    (h_fault : ptwIsFault.val t = true) :
    (mmuStateRegSignal init isMMUIdle isPTWWalk
      dTLBMiss ptwIsDone ptwIsFault).val (t + 1) = 4#3 := by
  unfold mmuStateRegSignal mmuStateNextSignal mmuNextFromWalkSignal
  show (Signal.register init _).val (t + 1) = _
  unfold Signal.mux
  show (if isMMUIdle.val t then _ else _) = _
  rw [h_no_idle]
  show (if isPTWWalk.val t then _ else _) = _
  rw [h_walk]
  show (if ptwIsDone.val t then _ else _) = _
  rw [h_no_done]
  show (if ptwIsFault.val t then _ else _) = _
  rw [h_fault]
  rfl

/-- **DONE/FAULT (¬idle, ¬walk) at t → state at t+1 = IDLE.** -/
theorem mmuStateReg_done_or_fault_to_idle {dom : DomainConfig}
    (init : BitVec 3) (isMMUIdle isPTWWalk : Signal dom Bool)
    (dTLBMiss ptwIsDone ptwIsFault : Signal dom Bool) (t : Nat)
    (h_no_idle : isMMUIdle.val t = false)
    (h_no_walk : isPTWWalk.val t = false) :
    (mmuStateRegSignal init isMMUIdle isPTWWalk
      dTLBMiss ptwIsDone ptwIsFault).val (t + 1) = 0#3 := by
  unfold mmuStateRegSignal mmuStateNextSignal
  show (Signal.register init _).val (t + 1) = _
  unfold Signal.mux
  show (if isMMUIdle.val t then _ else _) = _
  rw [h_no_idle]
  show (if isPTWWalk.val t then _ else _) = _
  rw [h_no_walk]
  rfl

end Sparkle.IP.RV32.MMU
