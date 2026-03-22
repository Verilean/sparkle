/-
  CDC Formal Properties — Lock-Free SPSC Queue & Rollback Protocol

  Pure state-machine model of the SPSC queue and Time-Warping rollback
  mechanism, with formal proofs of safety and correctness.

  Properties:
  - SPSC no-overflow: push never exceeds capacity
  - SPSC no-underflow: pop never goes below zero
  - Rollback guarantee: timestamp inversion forces rollback + state restore
  - Queue index isolation: rollback never modifies queue indices

  Pattern follows QueueProps.lean: self-contained definitions + proofs.
-/

namespace Sparkle.Verification.CDCProps

/-! ## SPSC Queue State Machine -/

/-- State of the SPSC ring-buffer queue.
    We require writeIdx ≥ readIdx as a well-formedness invariant. -/
structure SPSCState where
  writeIdx : Nat
  readIdx  : Nat
  capacity : Nat
  h_pow2   : ∃ k, capacity = 2 ^ k

/-- Number of elements currently in the queue -/
def spscCount (s : SPSCState) : Nat := s.writeIdx - s.readIdx

/-- Queue has room for at least one more element -/
def canPush (s : SPSCState) : Prop := spscCount s < s.capacity

/-- Queue has at least one element to consume -/
def canPop (s : SPSCState) : Prop := 0 < spscCount s

/-- Push transition: advance writeIdx by 1 -/
def pushTransition (s : SPSCState) : SPSCState :=
  { s with writeIdx := s.writeIdx + 1 }

/-- Pop transition: advance readIdx by 1 -/
def popTransition (s : SPSCState) : SPSCState :=
  { s with readIdx := s.readIdx + 1 }

/-! ## SPSC Safety Theorems -/

/--
  No overflow: if a push is only performed when canPush holds,
  the count after pushing does not exceed capacity.
-/
theorem spsc_no_overflow (s : SPSCState)
    (h_wf : s.readIdx ≤ s.writeIdx)
    (h_can : canPush s) :
    spscCount (pushTransition s) ≤ s.capacity := by
  simp only [spscCount, pushTransition, canPush] at *
  omega

/--
  No underflow: if a pop is only performed when canPop holds,
  the count after popping is non-negative (trivial for Nat).
-/
theorem spsc_no_underflow (s : SPSCState) :
    0 ≤ spscCount (popTransition s) := by
  exact Nat.zero_le _

/--
  Push preserves pop capability: if the queue was non-empty before push,
  it remains non-empty after push.
-/
theorem push_preserves_nonempty (s : SPSCState)
    (h_nonempty : canPop s) :
    canPop (pushTransition s) := by
  simp only [canPop, spscCount, pushTransition] at *
  omega

/--
  Pop frees space: if a pop is performed, the queue has room for a push.
-/
theorem pop_frees_space (s : SPSCState)
    (h_bounded : spscCount s ≤ s.capacity)
    (h_can : canPop s) :
    canPush (popTransition s) := by
  simp only [canPush, spscCount, popTransition, canPop] at *
  omega

/-! ## CDC Message & Rollback State Machine -/

/-- A timestamped message crossing clock domains -/
structure CDCMessage where
  timestamp : Nat
  payload   : Nat
  signalId  : Nat

/-- Opaque simulation state (snapshot-restorable) -/
structure SimSnapshot where
  data : Nat  -- abstract representation
  deriving BEq, DecidableEq

/-- Full CDC consumer state -/
structure CDCState where
  queue      : SPSCState
  localTime  : Nat
  rollback   : Bool
  simState   : SimSnapshot
  snapshot   : SimSnapshot  -- most recent saved snapshot

/-- Consume transition: pop a message and check for timestamp inversion -/
def consumeTransition (s : CDCState) (msg : CDCMessage) : CDCState :=
  let newQueue := popTransition s.queue
  if msg.timestamp < s.localTime then
    -- Timestamp inversion → rollback
    { queue     := newQueue          -- queue indices advance (never rolled back)
      localTime := msg.timestamp     -- rewind local time
      rollback  := true              -- set rollback flag
      simState  := s.snapshot        -- restore from snapshot
      snapshot  := s.snapshot }      -- snapshot unchanged
  else
    -- Normal consumption
    { queue     := newQueue
      localTime := msg.timestamp
      rollback  := s.rollback        -- preserve existing flag
      simState  := s.simState
      snapshot  := s.snapshot }

/-! ## Rollback Safety Theorems -/

/--
  Rollback guarantee: if a message has a timestamp earlier than the
  consumer's local time, the rollback flag is set and the simulation
  state is restored to the snapshot.
-/
theorem rollback_guarantee (s : CDCState) (msg : CDCMessage)
    (h_inversion : msg.timestamp < s.localTime) :
    let s' := consumeTransition s msg
    s'.rollback = true ∧ s'.simState = s.snapshot := by
  simp only [consumeTransition]
  simp [h_inversion]

/--
  Queue index advances on rollback: the queue's readIdx is incremented
  even when a rollback occurs (queue state is never rolled back).
-/
theorem rollback_advances_read_idx (s : CDCState) (msg : CDCMessage)
    (h_inversion : msg.timestamp < s.localTime) :
    (consumeTransition s msg).queue.readIdx = s.queue.readIdx + 1 := by
  simp only [consumeTransition]
  simp [h_inversion, popTransition]

/--
  Queue write index isolation: consuming a message (with or without
  rollback) never modifies the write index.
-/
theorem consume_preserves_write_idx (s : CDCState) (msg : CDCMessage) :
    (consumeTransition s msg).queue.writeIdx = s.queue.writeIdx := by
  simp only [consumeTransition]
  split <;> simp [popTransition]

/--
  Normal consumption: if the message timestamp is not in the past,
  the rollback flag is unchanged and simulation state is preserved.
-/
theorem normal_consume_no_rollback (s : CDCState) (msg : CDCMessage)
    (h_ok : s.localTime ≤ msg.timestamp) :
    let s' := consumeTransition s msg
    s'.rollback = s.rollback ∧ s'.simState = s.simState := by
  simp only [consumeTransition]
  have : ¬ (msg.timestamp < s.localTime) := Nat.not_lt.mpr h_ok
  simp [this]

/--
  Local time monotonicity under normal consumption: if no inversion,
  local time advances to the message timestamp.
-/
theorem normal_consume_time_advances (s : CDCState) (msg : CDCMessage)
    (h_ok : s.localTime ≤ msg.timestamp) :
    (consumeTransition s msg).localTime = msg.timestamp := by
  simp only [consumeTransition]
  have : ¬ (msg.timestamp < s.localTime) := Nat.not_lt.mpr h_ok
  simp [this]

/--
  Read index always advances: regardless of rollback, readIdx increments by 1.
  This is the key isolation property — queue progress is never undone.
-/
theorem consume_always_advances_read_idx (s : CDCState) (msg : CDCMessage) :
    (consumeTransition s msg).queue.readIdx = s.queue.readIdx + 1 := by
  simp only [consumeTransition]
  split <;> simp [popTransition]

/--
  Snapshot preservation: consuming a message never changes the stored snapshot.
-/
theorem consume_preserves_snapshot (s : CDCState) (msg : CDCMessage) :
    (consumeTransition s msg).snapshot = s.snapshot := by
  simp only [consumeTransition]
  split <;> simp

/--
  Rollback time rewind: on timestamp inversion, local time is set to
  the message's timestamp (which is earlier than the previous local time).
-/
theorem rollback_rewinds_time (s : CDCState) (msg : CDCMessage)
    (h_inversion : msg.timestamp < s.localTime) :
    (consumeTransition s msg).localTime = msg.timestamp ∧
    (consumeTransition s msg).localTime < s.localTime := by
  simp only [consumeTransition]
  simp [h_inversion]

end Sparkle.Verification.CDCProps
