# Temporal Logic for Hardware Verification

This document demonstrates Linear Temporal Logic (LTL) operators in Sparkle HDL for expressing and proving temporal properties of hardware designs.

## Core Concept

Temporal logic extends boolean logic with operators that reason about **time**:
- `always P`: Property P holds at all future time steps
- `eventually P`: Property P holds at some future time step
- `next P`: Property P holds at the next time step
- `until P Q`: P holds until Q becomes true

## Design Goals

### 1. Optimization Enablement

**Cycle Skipping via Temporal Oracle:**
```lean
-- If we prove this property:
theorem counter_stable : ∀ (c : Signal d (BitVec 8)),
    c == 0 → always (next 10) (c == 0)

-- The simulator can skip 10 cycles when counter is 0
-- instead of evaluating 10 individual time steps
```

**Property-Driven Simulation:**
- Proven temporal properties become "oracles" during simulation
- When a property's precondition is met, skip ahead by the proven duration
- Example: "After reset, system is idle for 100 cycles" → skip 100 evaluations

### 2. Constraints Imposed

**Type Safety:**
```lean
-- Temporal operators ONLY work on Signal Bool
always : (Signal d Bool) → Prop
eventually : (Signal d Bool) → Prop

-- NOT on arbitrary predicates
-- ❌ WRONG: always (λ t => counter.atTime t < 100)
-- ✓ RIGHT: always ((counter.map (· < 100)))
```

**Proof Obligations:**
```lean
-- To use cycle skipping, you MUST provide a proof
axiom skipCycles {P : Signal d Bool} (n : Nat) :
  (always (next n) P) → CanSkip n
```

**Soundness Requirements:**
- Temporal properties must be provable, not axioms
- Proofs must handle all edge cases (reset, overflow, etc.)
- Invalid proofs lead to incorrect simulation results

## Example 1: Reset Stability

### Hardware Design
```lean
-- A counter that resets to 0 and stays there for 10 cycles
def resetCounter : Signal defaultDomain (BitVec 8) := do
  let count ← Signal.register 0
  let resetActive ← Signal.register true
  let resetTimer ← Signal.register (10 : BitVec 8)

  -- Stay in reset for 10 cycles
  let nextResetActive := resetTimer > 0
  let nextTimer := if resetTimer > 0 then resetTimer - 1 else 0
  let nextCount := if resetActive then 0 else count + 1

  resetActive <~ nextResetActive
  resetTimer <~ nextTimer
  count <~ nextCount

  return count
```

### Temporal Property
```lean
-- Property: After reset, counter stays 0 for 10 cycles
theorem reset_stability :
  let counter := resetCounter
  let isZero := counter.map (· == 0)
  -- At time 0, counter is 0 and stays 0 for next 10 cycles
  (isZero.atTime 0) → always (next 10) isZero := by
  -- Proof by induction on time...
  sorry
```

### Optimization Enabled
```lean
-- Simulator uses the proof:
-- At t=0: Check isZero.atTime 0 == true
-- Oracle: Skip to t=10 (no evaluation needed for t=1..9)
-- Result: 10x speedup for reset sequence
```

## Example 2: State Machine Verification

### Hardware Design
```lean
inductive State where
  | Idle
  | Active
  | Done

def stateMachine : Signal d State := do
  let state ← Signal.register State.Idle
  let counter ← Signal.register (0 : BitVec 8)

  let nextState := match state with
    | State.Idle => if trigger then State.Active else State.Idle
    | State.Active => if counter == 99 then State.Done else State.Active
    | State.Done => State.Idle

  let nextCounter := match state with
    | State.Active => counter + 1
    | _ => 0

  state <~ nextState
  counter <~ nextCounter
  return state
```

### Temporal Properties
```lean
-- Property 1: Active state lasts exactly 100 cycles
theorem active_duration :
  let isActive := stateMachine.map (· == State.Active)
  let isDone := stateMachine.map (· == State.Done)
  -- When entering Active, it lasts 100 cycles until Done
  isActive → (always (next 100) isActive) ∧ (next 100) isDone := by
  sorry

-- Property 2: Done state lasts exactly 1 cycle
theorem done_transient :
  let isDone := stateMachine.map (· == State.Done)
  let isIdle := stateMachine.map (· == State.Idle)
  isDone → (next 1) isIdle := by
  sorry

-- Property 3: Idle is stable until trigger
theorem idle_stable :
  let isIdle := stateMachine.map (· == State.Idle)
  isIdle ∧ ¬trigger → (next 1) isIdle := by
  sorry
```

### Optimization Enabled
```lean
-- When in Active state:
-- - Skip 100 cycles to Done (proven by active_duration)
-- - Savings: 99 evaluation cycles

-- When in Done state:
-- - Skip 1 cycle to Idle (proven by done_transient)

-- When in Idle with no trigger:
-- - Skip ahead by batch size (e.g., 1000 cycles)
-- - Check trigger periodically
```

## Example 3: Pipeline Verification

### Hardware Design
```lean
-- 3-stage pipeline
def pipeline (input : Signal d (BitVec 16)) : Signal d (BitVec 16) := do
  let stage1 ← Signal.register 0
  let stage2 ← Signal.register 0
  let stage3 ← Signal.register 0

  stage1 <~ input
  stage2 <~ stage1.map (· * 2)
  stage3 <~ stage2.map (· + 1)

  return stage3
```

### Temporal Properties
```lean
-- Property: Output appears 3 cycles after input
theorem pipeline_latency (x : BitVec 16) :
  let out := pipeline (Signal.pure x)
  (next 3) (out.map (· == (x * 2 + 1))) := by
  -- Proof by register chain induction
  sorry

-- Property: Pipeline always produces correct result after 3 cycles
theorem pipeline_correctness :
  ∀ (input : Signal d (BitVec 16)),
    eventually (output == input.map (λ x => x * 2 + 1)) := by
  sorry
```

### Optimization: NOT Enabled
```lean
-- Note: Pipeline latency CANNOT be skipped
-- Reason: Each stage has computational dependencies
-- Temporal properties here are for VERIFICATION only, not optimization

-- This is the constraint: Not all temporal properties enable cycle skipping
-- Only properties about STABLE VALUES enable skipping
```

## Design Constraints Summary

### ✓ Properties That Enable Cycle Skipping

1. **Stability Properties**: Signal stays constant
   ```lean
   always (next N) (signal == value)
   ```

2. **State Invariants**: State doesn't change
   ```lean
   state == Idle → (next N) (state == Idle)
   ```

3. **Deterministic Delays**: Known duration
   ```lean
   reset → (next 100) idle
   ```

### ✗ Properties That DON'T Enable Cycle Skipping

1. **Eventually Properties**: Unknown timing
   ```lean
   eventually (done == true)  -- When? Can't skip
   ```

2. **Computational Dependencies**: Must evaluate
   ```lean
   output == f(input)  -- Must compute f
   ```

3. **Non-deterministic Timing**: External inputs
   ```lean
   trigger → eventually response  -- Can't predict when
   ```

## API Design Implications

### Core Operators (Proof-only)
```lean
-- These are for verification, not optimization
def always (P : Signal d Bool) : Prop
def eventually (P : Signal d Bool) : Prop
def next (n : Nat) (P : Signal d Bool) : Prop
def until (P Q : Signal d Bool) : Prop
```

### Optimization-Enabled Operators
```lean
-- These enable cycle skipping when proven
def stableFor (s : Signal d α) (v : α) (n : Nat) : Prop :=
  always (next n) (s.map (· == v))

def stableWhile (s : Signal d α) (cond : Signal d Bool) : Prop :=
  cond → (next 1) cond ∧ (next 1) (s.map (· == s))
```

### Simulation Oracle Interface
```lean
-- Internal simulator interface (not exposed to users)
structure TemporalOracle where
  canSkip : Nat → Signal d Bool → Option Nat
  proof : ∀ n P, canSkip n P = some m → stableFor P true m
```

## Proof Requirements

### Soundness Guarantee
```lean
-- Every temporal property must be PROVABLE, not axiomatic
-- Bad: axiom reset_stable : always (next 10) (counter == 0)
-- Good:
theorem reset_stable : always (next 10) (counter == 0) := by
  intro t
  induction t with
  | zero => -- Base case: prove for t=0
    simp [counter, Signal.register]
  | succ t ih => -- Inductive case
    have : counter.atTime (t + 1) = 0 := by
      -- Use IH and register semantics
      sorry
    exact this
```

### Edge Cases Must Be Handled
```lean
-- Property must account for:
-- 1. Initial state (t=0)
-- 2. Overflow/underflow
-- 3. Reset behavior
-- 4. Boundary conditions
```

## Implementation Architecture

```
Sparkle/Verification/Temporal.lean
├── Core LTL Operators (always, eventually, next, until)
├── Derived Operators (implies, release, stableFor)
├── Proof Helpers (temporal induction tactics)
└── Oracle Interface (for future simulator integration)

Future: Sparkle/Core/OptimizedSim.lean
├── Temporal Oracle Registry
├── Cycle Skipping Engine
└── Proof Validation
```

## Summary

**Optimizations Enabled:**
- Cycle skipping for proven stable periods
- 10-1000x speedup for designs with idle periods
- Batch evaluation for long stable states

**Constraints Imposed:**
- Properties must be provable (not axiomatic)
- Only works on `Signal Bool` predicates
- Only stability properties enable optimization
- Proofs must be sound and complete

**Design Principle:**
> Temporal logic is PRIMARILY for verification.
> Cycle skipping is a BONUS optimization when properties are proven stable.
> Never sacrifice soundness for performance.
