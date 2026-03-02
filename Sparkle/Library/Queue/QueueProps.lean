/-
  Queue Formal Properties — Pure State Machine Model

  This file contains a pure model of a synchronous FIFO queue,
  together with formal proofs of safety properties:

  - No overflow (count never exceeds depth)
  - No underflow (count never goes negative — trivial for Nat)
  - Full blocks enqueue
  - Empty blocks dequeue
  - Idle preserves count
  - Simultaneous enqueue+dequeue preserves count
  - Inductive invariant (count stays bounded)

  Pattern follows ArbiterProps.lean: self-contained definitions + proofs,
  no cross-library dependencies.
-/

namespace Sparkle.Library.Queue.QueueProps

/-- Can enqueue: count has room -/
def canEnqueue (count depth : Nat) : Prop := count < depth

/-- Can dequeue: count is non-zero -/
def canDequeue (count : Nat) : Prop := 0 < count

instance (count depth : Nat) : Decidable (canEnqueue count depth) :=
  inferInstanceAs (Decidable (count < depth))

instance (count : Nat) : Decidable (canDequeue count) :=
  inferInstanceAs (Decidable (0 < count))

/-- Next count after one cycle.
    Enqueue if enqValid and not full; dequeue if deqReady and not empty. -/
def nextCount (count depth : Nat) (enqValid deqReady : Bool) : Nat :=
  let doEnq := enqValid ∧ canEnqueue count depth
  let doDeq := deqReady ∧ canDequeue count
  if doEnq ∧ doDeq then count         -- simultaneous enq+deq
  else if doEnq then count + 1         -- enqueue only
  else if doDeq then count - 1         -- dequeue only
  else count                           -- idle

/-! ## Safety Properties -/

/--
  No overflow: if count is within bounds, the next count cannot exceed depth.
-/
theorem no_overflow (count depth : Nat) (enqValid deqReady : Bool) :
    count ≤ depth → nextCount count depth enqValid deqReady ≤ depth := by
  intro h
  simp only [nextCount, canEnqueue, canDequeue]
  cases enqValid <;> cases deqReady <;> simp <;>
    first | omega | assumption
          | (split <;> first | omega
                              | (split <;> first | omega | (split <;> omega)))

/--
  No underflow: the next count is always non-negative (trivial for Nat).
-/
theorem no_underflow (count depth : Nat) (enqValid deqReady : Bool) :
    0 ≤ nextCount count depth enqValid deqReady := by
  exact Nat.zero_le _

/--
  Full blocks enqueue: when count equals depth, canEnqueue is false.
-/
theorem full_blocks_enqueue (depth : Nat) :
    ¬ canEnqueue depth depth := by
  simp [canEnqueue]

/--
  Empty blocks dequeue: when count is zero, canDequeue is false.
-/
theorem empty_blocks_dequeue :
    ¬ canDequeue 0 := by
  simp [canDequeue]

/--
  Idle preserves count: with no enqueue and no dequeue, count is unchanged.
-/
theorem idle_preserves (count depth : Nat) :
    nextCount count depth false false = count := by
  simp [nextCount, canEnqueue, canDequeue]

/--
  Simultaneous enqueue and dequeue preserves count when both are possible.
-/
theorem simultaneous_preserves (count depth : Nat) :
    canEnqueue count depth → canDequeue count →
    nextCount count depth true true = count := by
  intro he hd
  simp [nextCount, he, hd]

/--
  Inductive invariant: count stays bounded across all transitions.
  (Same as no_overflow, stated as the inductive step of the invariant.)
-/
theorem count_bounded_inductive (count depth : Nat) (enqValid deqReady : Bool) :
    count ≤ depth → nextCount count depth enqValid deqReady ≤ depth := by
  exact no_overflow count depth enqValid deqReady

end Sparkle.Library.Queue.QueueProps
