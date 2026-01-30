/-
  Linear Temporal Logic (LTL) for Hardware Verification

  Provides temporal operators for expressing and proving properties about
  hardware behavior over time. Designed for verification-first, with
  optional optimization via cycle skipping for proven stable properties.

  See Examples/TemporalLogicExample.md for usage examples and design rationale.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.Verification.Temporal

open Sparkle.Core.Signal
open Sparkle.Core.Domain

/-!
## Core Linear Temporal Logic Operators

These operators form the foundation of LTL for hardware verification.
All operators work on `Signal d Bool` predicates.
-/

/--
  `always P` - Property P holds at ALL future time steps.

  Semantics: ∀ t, P.atTime t = true

  Example:
  ```lean
  theorem counter_never_exceeds_max :
    always (counter.map (· < 256))
  ```
-/
def always {d : DomainConfig} (P : Signal d Bool) : Prop :=
  ∀ (t : Nat), P.atTime t = true

/--
  `eventually P` - Property P holds at SOME future time step.

  Semantics: ∃ t, P.atTime t = true

  Example:
  ```lean
  theorem done_flag_set :
    eventually (done.map (· == true))
  ```
-/
def eventually {d : DomainConfig} (P : Signal d Bool) : Prop :=
  ∃ (t : Nat), P.atTime t = true

/--
  `next n P` - Property P holds exactly n cycles in the future.

  Semantics: ∀ t, P.atTime (t + n) = true

  Example:
  ```lean
  theorem pipeline_latency :
    next 3 (output.map (· == expected))
  ```
-/
def next {d : DomainConfig} (n : Nat) (P : Signal d Bool) : Prop :=
  ∀ (t : Nat), P.atTime (t + n) = true

/--
  `Until P Q` - Property P holds until Q becomes true.

  Semantics: ∃ t, Q.atTime t = true ∧ (∀ t' < t, P.atTime t' = true)

  Example:
  ```lean
  theorem busy_until_done :
    Until (busy.map id) (done.map id)
  ```
-/
def Until {d : DomainConfig} (P Q : Signal d Bool) : Prop :=
  ∃ (t : Nat), Q.atTime t = true ∧ (∀ (t' : Nat), t' < t → P.atTime t' = true)

/-!
## Derived Temporal Operators

These are convenience operators defined in terms of the core LTL operators.
-/

/--
  `implies P Q` - Temporal implication: whenever P holds, Q also holds.

  Semantics: ∀ t, P.atTime t = true → Q.atTime t = true
-/
def implies {d : DomainConfig} (P Q : Signal d Bool) : Prop :=
  ∀ (t : Nat), P.atTime t = true → Q.atTime t = true

/--
  `release P Q` - Dual of `until`: Q holds until and including when P holds.

  Semantics: ∀ t, (Q.atTime t = true) ∨ (∃ t' ≤ t, P.atTime t' = true ∧ ∀ t'' < t', Q.atTime t'' = true)
-/
def release {d : DomainConfig} (P Q : Signal d Bool) : Prop :=
  ∀ (t : Nat), (Q.atTime t = true) ∨
    (∃ (t' : Nat), t' ≤ t ∧ P.atTime t' = true ∧
      ∀ (t'' : Nat), t'' < t' → Q.atTime t'' = true)

/--
  `WeakUntil P Q` - Like `Until`, but P can hold forever if Q never becomes true.

  Semantics: (∃ t, Q.atTime t ∧ ∀ t' < t, P.atTime t') ∨ (∀ t, P.atTime t)
-/
def WeakUntil {d : DomainConfig} (P Q : Signal d Bool) : Prop :=
  (∃ (t : Nat), Q.atTime t = true ∧ (∀ (t' : Nat), t' < t → P.atTime t' = true)) ∨
  (∀ (t : Nat), P.atTime t = true)

/-!
## Optimization-Enabling Operators

These operators specifically enable cycle-skipping optimizations when proven.
They express stability properties that allow the simulator to skip evaluations.
-/

/--
  `stableFor s v n` - Signal s maintains value v for exactly n cycles.

  This is the KEY property that enables cycle skipping optimization.
  When proven, the simulator can skip n-1 evaluation cycles.

  Example:
  ```lean
  theorem reset_stable :
    stableFor counter 0 10  -- Counter stays 0 for 10 cycles
  ```
-/
def stableFor {d : DomainConfig} {α : Type} [BEq α]
    (s : Signal d α) (v : α) (n : Nat) : Prop :=
  ∀ (t : Nat), t < n → s.atTime t == v

/--
  `stableWhile s cond` - Signal s remains constant while condition holds.

  Example:
  ```lean
  theorem idle_stable :
    stableWhile state (isIdle.map id)
  ```
-/
def stableWhile {d : DomainConfig} {α : Type} [BEq α]
    (s : Signal d α) (cond : Signal d Bool) : Prop :=
  ∀ (t : Nat), cond.atTime t = true →
    cond.atTime (t + 1) = true ∧ s.atTime (t + 1) == s.atTime t

/--
  `monotonic s` - Signal s is monotonically increasing.

  Useful for counters and timers. While not enabling cycle skipping,
  helps prove other temporal properties.
-/
def monotonic {d : DomainConfig} (s : Signal d Nat) : Prop :=
  ∀ (t : Nat), s.atTime t ≤ s.atTime (t + 1)

/-!
## Temporal Induction Principles

Helper lemmas and tactics for proving temporal properties.
-/

/--
  Induction principle for `always`:
  To prove ∀ t, P(t), prove P(0) and P(t) → P(t+1).
-/
theorem always_induction {d : DomainConfig} (P : Signal d Bool) :
  P.atTime 0 = true →
  (∀ (t : Nat), P.atTime t = true → P.atTime (t + 1) = true) →
  always P := by
  intro h_base h_step t
  induction t with
  | zero => exact h_base
  | succ t ih => exact h_step t ih

/--
  Induction principle for `stableFor`:
  To prove signal stays stable for n cycles, prove base case and preservation.

  Note: This is a placeholder theorem for future proof development.
-/
theorem stableFor_induction {d : DomainConfig} {α : Type} [BEq α]
    (s : Signal d α) (v : α) (n : Nat) :
  s.atTime 0 == v →
  (∀ (t : Nat), t < n → s.atTime t == v → s.atTime (t + 1) == v) →
  stableFor s v (n + 1) := by
  sorry

/--
  Composition lemma: If P always holds and P implies Q, then Q always holds.
-/
theorem always_implies {d : DomainConfig} (P Q : Signal d Bool) :
  always P → implies P Q → always Q := by
  intro h_always_p h_implies t
  exact h_implies t (h_always_p t)

/--
  Eventually is weaker than always: if P always holds, it eventually holds.
-/
theorem always_implies_eventually {d : DomainConfig} (P : Signal d Bool) :
  always P → eventually P := by
  intro h_always
  exists 0
  exact h_always 0

/-!
## Temporal Oracle Interface (Future Work)

This interface will be used by an optimized simulator to enable cycle skipping.
Currently a placeholder for future implementation.
-/

/--
  Temporal Oracle: Queries proven temporal properties to enable cycle skipping.

  The oracle checks if a signal has a proven stability property and returns
  how many cycles can be safely skipped.
-/
structure TemporalOracle (d : DomainConfig) where
  /-- Query if we can skip cycles for a given signal property -/
  canSkip : (α : Type) → [BEq α] → Signal d α → α → Option Nat

  /-- Proof that canSkip is sound: if it returns n, the signal is stable for n cycles -/
  soundness : ∀ {α : Type} [BEq α] (s : Signal d α) (v : α) (n : Nat),
    canSkip α s v = some n → stableFor s v n

/--
  Empty oracle: no optimizations available.
  This is the default for standard simulation.
-/
def emptyOracle {d : DomainConfig} : TemporalOracle d where
  canSkip := fun _ [_] _ _ => none
  soundness := fun _ _ _ h => by simp at h

/-!
## Notation and Helpers

Convenient notation for temporal formulas.
-/

-- Notation for temporal operators (optional, can be enabled by users)
scoped notation:50 "◯" P:51 => next 1 P          -- Next (circle)
scoped notation:40 "□" P:41 => always P           -- Always (box)
scoped notation:40 "◇" P:41 => eventually P       -- Eventually (diamond)
scoped infixr:35 "U" => Until                      -- Until
scoped infixr:35 "R" => release                    -- Release
scoped infixr:30 "⟹" => implies                   -- Temporal implies

/--
  Check if a signal satisfies a property at a specific time.
-/
def satisfiesAt {d : DomainConfig} (P : Signal d Bool) (t : Nat) : Bool :=
  P.atTime t

/--
  Check if a signal satisfies a property for a duration.
-/
def satisfiesFor {d : DomainConfig} (P : Signal d Bool) (n : Nat) : Prop :=
  ∀ (t : Nat), t < n → P.atTime t = true

/-!
## Examples and Documentation

See Examples/TemporalLogicExample.md for comprehensive usage examples.
-/

end Sparkle.Verification.Temporal
