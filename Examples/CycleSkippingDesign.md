# Cycle-Skipping Simulation Design

## Overview

Cycle-skipping simulation uses proven temporal properties to optimize simulation by skipping evaluation of cycles where signal values are known to be stable.

## Motivation

Consider a reset sequence where a counter stays at 0 for 1000 cycles:

```lean
-- Traditional simulation: evaluate 1000 times
for t in [0:1000] do
  counter.atTime t  -- Always returns 0

-- Cycle-skipping: evaluate once, skip 999 cycles
if stableFor counter 0 1000 then
  skip_to_cycle 1000
```

**Speedup potential**: 10-1000x for designs with long idle periods.

## Architecture

### 1. Temporal Oracle

The oracle stores proven stability properties and answers queries:

```lean
structure TemporalOracle where
  -- Registry of proven properties
  properties : List StabilityProperty

  -- Query: Can we skip cycles for this signal?
  canSkip : Signal d α → Nat → Option (Nat × α)

  -- Returns: Some (n, value) if signal is stable at 'value' for next n cycles
```

### 2. Stability Property

```lean
structure StabilityProperty where
  signalName : String
  value : α
  startCycle : Nat
  duration : Nat
  proof : stableFor signal value duration
```

### 3. Optimized Simulator

```lean
def simulateOptimized (oracle : TemporalOracle) (signal : Signal d α) (maxCycles : Nat) : List α :=
  let rec sim (t : Nat) (acc : List α) : List α :=
    if t >= maxCycles then acc.reverse
    else
      -- Query oracle for skip opportunity
      match oracle.canSkip signal t with
      | some (n, value) =>
        -- Skip n cycles, fill with stable value
        let skipped := List.replicate n value
        sim (t + n) (skipped.reverse ++ acc)
      | none =>
        -- Normal evaluation
        let val := signal.atTime t
        sim (t + 1) (val :: acc)
  sim 0 []
```

## Implementation Approach

### Phase 1: Manual Oracle (Current)

Users manually register proven properties:

```lean
def myOracle : TemporalOracle := {
  properties := [
    { signalName := "counter"
      value := 0
      startCycle := 0
      duration := 1000
      proof := counter_stable_during_reset
    }
  ]
}
```

### Phase 2: Automatic Registration (Future)

Use tactics to automatically extract properties from proofs:

```lean
-- User writes proof
theorem counter_stable : stableFor counter 0 1000 := by
  intro t h_bound
  simp [counter]
  omega

-- Tactic automatically registers with oracle
register_temporal_property counter_stable
```

### Phase 3: Dynamic Property Discovery (Future)

Simulator discovers stability at runtime:

```lean
-- Monitor signal values during simulation
-- If stable for N cycles, cache the property
-- Use cached property for future simulations
```

## Example: Reset Sequence Optimization

```lean
-- Circuit with long reset
def circuitWithReset : Signal d (BitVec 8) := do
  let count ← Signal.register 0
  let resetActive ← Signal.register true
  let resetTimer ← Signal.register 1000

  let nextReset := resetTimer > 0
  let nextTimer := if resetTimer > 0 then resetTimer - 1 else resetTimer
  let nextCount := if nextReset then 0 else count + 1

  resetTimer <~ nextTimer
  count <~ nextCount
  return count

-- Proven property
theorem reset_stable : stableFor circuitWithReset 0 1000 := by
  sorry  -- Proof here

-- Create oracle with property
def resetOracle : TemporalOracle :=
  emptyOracle.addProperty reset_stable

-- Simulate with optimization
def testResetOptimization : IO Unit := do
  let standardTime := measureTime (simulate circuitWithReset 10000)
  let optimizedTime := measureTime (simulateOptimized resetOracle circuitWithReset 10000)

  IO.println s!"Standard: {standardTime}ms"
  IO.println s!"Optimized: {optimizedTime}ms"
  IO.println s!"Speedup: {standardTime / optimizedTime}x"
```

## Performance Model

For a signal stable for N cycles out of T total:

- **Standard simulation**: O(T) evaluations
- **Optimized simulation**: O(T - N + 1) evaluations
- **Speedup**: T / (T - N + 1) ≈ T / (T - N) for large T

Example scenarios:

| Total Cycles | Stable Cycles | Speedup |
|--------------|---------------|---------|
| 1,000 | 900 | 10x |
| 10,000 | 9,000 | 10x |
| 10,000 | 9,900 | 100x |
| 100,000 | 99,000 | 100x |

## Safety and Soundness

**Critical requirement**: Properties must be PROVEN, not assumed.

```lean
-- ✓ SAFE: Proven property
theorem counter_stable : stableFor counter 0 100 := by
  intro t h_bound
  simp [counter]
  omega

-- ✗ UNSAFE: Axiom without proof
axiom counter_stable : stableFor counter 0 100  -- DON'T DO THIS!
```

If a property is incorrectly proven, the simulator will produce wrong results. The type system ensures properties are `Prop` (must be proven), not `Bool` (can be arbitrary).

## Implementation Challenges

### 1. Signal Identity

Problem: How to match signal values to properties?

```lean
-- Same signal, different names
let sig1 := myCounter
let sig2 := myCounter
-- Are sig1 and sig2 the same for oracle purposes?
```

Solution: Use signal structure equality or unique IDs.

### 2. Conditional Stability

Problem: Stability may depend on other signals:

```lean
-- Counter stable only while enable = false
theorem counter_stable_when_disabled :
  enable = false → stableFor counter (counter.atTime 0) 1000
```

Solution: Oracle must check preconditions before skipping.

### 3. Nested Signals

Problem: Composed signals may not have direct properties:

```lean
let doubled := counter.map (* 2)
-- No direct property for 'doubled', but can infer from 'counter'
```

Solution: Property inference rules for signal combinators.

## Incremental Implementation Plan

### Step 1: Basic Oracle
- [x] Define TemporalOracle structure (already in Temporal.lean)
- [ ] Implement manual property registration
- [ ] Simple query interface

### Step 2: Optimized Simulator
- [ ] `simulateOptimized` function
- [ ] Skip detection and fast-forward logic
- [ ] Correctness verification (compare with standard simulator)

### Step 3: Example Properties
- [ ] Reset stable property
- [ ] State machine idle property
- [ ] Clock divider stable property

### Step 4: Performance Measurement
- [ ] Benchmark framework
- [ ] Compare standard vs optimized simulation
- [ ] Report speedup metrics

### Step 5: Advanced Features
- [ ] Automatic property extraction from proofs
- [ ] Property composition rules
- [ ] Dynamic property discovery

## Summary

Cycle-skipping simulation provides:
- **10-1000x speedup** for designs with idle/stable periods
- **Soundness guarantee** through theorem proving
- **Incremental adoption** - works alongside standard simulation
- **Type safety** - incorrect properties caught at compile time

The key insight: Formal verification enables performance optimization. Proofs about hardware behavior become executable optimization hints.
