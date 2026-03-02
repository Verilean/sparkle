/-
  Round-Robin Arbiter Formal Properties

  This file contains a pure state-machine model of a 2-client
  round-robin arbiter, together with formal proofs of:

  Safety  — mutual exclusion, no spurious grants
  Liveness — progress and starvation-freedom
  Fairness — round-robin alternation on contention

  Pattern follows ISAProps.lean: self-contained definitions + proofs,
  no cross-library dependencies.
-/

namespace Sparkle.Verification.ArbiterProps

/-- Arbiter FSM state -/
inductive ArbiterState where
  | Idle
  | GrantA
  | GrantB
  deriving DecidableEq, Repr, BEq, Inhabited

open ArbiterState

/--
  Next-state function (12-entry truth table).

  Tie-break from Idle: A wins.
  Round-robin on contention: alternate A ↔ B.
-/
def nextState (s : ArbiterState) (reqA reqB : Bool) : ArbiterState :=
  match s, reqA, reqB with
  | Idle,   true,  true  => GrantA   -- tie-break: A first from Idle
  | Idle,   true,  false => GrantA
  | Idle,   false, true  => GrantB
  | Idle,   false, false => Idle
  | GrantA, true,  true  => GrantB   -- round-robin: alternate
  | GrantA, true,  false => GrantA
  | GrantA, false, true  => GrantB
  | GrantA, false, false => Idle
  | GrantB, true,  true  => GrantA   -- round-robin: alternate
  | GrantB, true,  false => GrantA
  | GrantB, false, true  => GrantB
  | GrantB, false, false => Idle

/-- Output: client A is granted -/
def grantA : ArbiterState → Bool
  | GrantA => true
  | _      => false

/-- Output: client B is granted -/
def grantB : ArbiterState → Bool
  | GrantB => true
  | _      => false

/-! ## Safety Properties -/

/--
  Mutual exclusion on next-state output.
  The arbiter never grants both clients simultaneously.
-/
theorem mutual_exclusion (s : ArbiterState) (reqA reqB : Bool) :
    ¬(grantA (nextState s reqA reqB) ∧ grantB (nextState s reqA reqB)) := by
  cases s <;> cases reqA <;> cases reqB <;> simp [nextState, grantA, grantB]

/--
  Mutual exclusion on any reachable state.
-/
theorem mutual_exclusion_current (s : ArbiterState) :
    ¬(grantA s ∧ grantB s) := by
  cases s <;> simp [grantA, grantB]

/--
  No spurious grants: when neither client requests, no grant is issued.
-/
theorem no_spurious_grant (s : ArbiterState) :
    grantA (nextState s false false) = false ∧
    grantB (nextState s false false) = false := by
  cases s <;> simp [nextState, grantA, grantB]

/-! ## Liveness Properties -/

/--
  Progress for client A: if A requests, it is either granted immediately
  or the other client holds (ensuring A will be next via round-robin).
-/
theorem progress_A (s : ArbiterState) (reqB : Bool) :
    grantA (nextState s true reqB) ∨ nextState s true reqB = GrantB := by
  cases s <;> cases reqB <;> simp [nextState, grantA]

/--
  Progress for client B: symmetric to progress_A.
-/
theorem progress_B (s : ArbiterState) (reqA : Bool) :
    grantB (nextState s reqA true) ∨ nextState s reqA true = GrantA := by
  cases s <;> cases reqA <;> simp [nextState, grantB]

/--
  Starvation-freedom for client A: if A keeps requesting, it is granted
  within at most 2 cycles.
-/
theorem starvation_free_A (s : ArbiterState) (reqB : Bool) :
    grantA (nextState s true reqB) ∨
    grantA (nextState (nextState s true reqB) true reqB) := by
  cases s <;> cases reqB <;> simp [nextState, grantA]

/--
  Starvation-freedom for client B (symmetric).
-/
theorem starvation_free_B (s : ArbiterState) (reqA : Bool) :
    grantB (nextState s reqA true) ∨
    grantB (nextState (nextState s reqA true) reqA true) := by
  cases s <;> cases reqA <;> simp [nextState, grantB]

/-! ## Fairness Properties -/

/--
  Round-robin: from GrantA with both requesting, next state is GrantB.
-/
theorem round_robin_A_to_B :
    nextState GrantA true true = GrantB := by
  rfl

/--
  Round-robin: from GrantB with both requesting, next state is GrantA.
-/
theorem round_robin_B_to_A :
    nextState GrantB true true = GrantA := by
  rfl

/--
  Tie-break: from Idle with both requesting, A wins.
-/
theorem idle_tiebreak :
    nextState Idle true true = GrantA := by
  rfl

/-! ## Efficiency Properties -/

/--
  Work-conserving: if at least one client requests, at least one client is granted.
  The arbiter never wastes a cycle when work is pending.
-/
theorem work_conserving (s : ArbiterState) (reqA reqB : Bool) :
    (reqA ∨ reqB) →
    (grantA (nextState s reqA reqB) ∨ grantB (nextState s reqA reqB)) := by
  cases s <;> cases reqA <;> cases reqB <;> simp [nextState, grantA, grantB]

/--
  Bounded wait for client A: if A requests but is not granted this cycle,
  then A is guaranteed to be granted next cycle (regardless of B's request).
  Maximum wait = exactly 1 cycle.
-/
theorem bounded_wait_A (s : ArbiterState) (reqB reqB' : Bool) :
    ¬grantA (nextState s true reqB) →
    grantA (nextState (nextState s true reqB) true reqB') := by
  cases s <;> cases reqB <;> cases reqB' <;> simp [nextState, grantA]

/--
  Bounded wait for client B (symmetric): if B requests but is not granted
  this cycle, B is guaranteed to be granted next cycle.
-/
theorem bounded_wait_B (s : ArbiterState) (reqA reqA' : Bool) :
    ¬grantB (nextState s reqA true) →
    grantB (nextState (nextState s reqA true) reqA' true) := by
  cases s <;> cases reqA <;> cases reqA' <;> simp [nextState, grantB]

end Sparkle.Verification.ArbiterProps
