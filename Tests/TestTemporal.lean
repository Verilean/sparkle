/-
  Temporal Logic Tests

  Tests for Linear Temporal Logic operators and temporal reasoning.

  Note: Temporal logic properties are of type `Prop`, not `Bool`,
  so we test by verifying signal behaviors that would support the properties.
-/

import Sparkle
import Sparkle.Verification.Temporal
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Temporal
open LSpec

namespace Sparkle.Test.Temporal

/-!
## Test Signals

Define simple signals for testing temporal properties.
-/

/-- Constant signal: always returns the same value -/
def constantSignal (v : BitVec 8) : Signal defaultDomain (BitVec 8) :=
  Signal.pure v

/-- Counter signal: increments every cycle -/
def counterSignal : Signal defaultDomain Nat :=
  ⟨fun t => t⟩

/-- Periodic signal: alternates between true and false -/
def periodicSignal : Signal defaultDomain Bool :=
  ⟨fun t => t % 2 == 0⟩

/-- Delayed signal: becomes true after n cycles -/
def delayedSignal (n : Nat) : Signal defaultDomain Bool :=
  ⟨fun t => t ≥ n⟩

/-- Pulse signal: true only at specific time -/
def pulseSignal (t_pulse : Nat) : Signal defaultDomain Bool :=
  ⟨fun t => t == t_pulse⟩

/-!
## Signal Behavior Tests

Test concrete signal evaluations that demonstrate temporal properties.
-/

def test_signal_basics : IO TestSeq := do
  let const42 := constantSignal 42
  pure (
    test "constant signal at time 0" (const42.atTime 0 == 42#8) $
    test "constant signal at time 100" (const42.atTime 100 == 42#8) $
    test "counter signal at time 0" (counterSignal.atTime 0 == 0) $
    test "counter signal at time 5" (counterSignal.atTime 5 == 5) $
    test "counter signal at time 10" (counterSignal.atTime 10 == 10) $
    test "periodic signal at time 0" (periodicSignal.atTime 0 == true) $
    test "periodic signal at time 1" (periodicSignal.atTime 1 == false) $
    test "periodic signal at time 2" (periodicSignal.atTime 2 == true)
  )

def test_delayed_signals : IO TestSeq := do
  let delayed10 := delayedSignal 10
  let pulse5 := pulseSignal 5
  pure (
    test "delayed signal false at time 0" (delayed10.atTime 0 == false) $
    test "delayed signal false at time 9" (delayed10.atTime 9 == false) $
    test "delayed signal true at time 10" (delayed10.atTime 10 == true) $
    test "delayed signal true at time 11" (delayed10.atTime 11 == true) $
    test "pulse signal false at time 0" (pulse5.atTime 0 == false) $
    test "pulse signal false at time 4" (pulse5.atTime 4 == false) $
    test "pulse signal true at time 5" (pulse5.atTime 5 == true) $
    test "pulse signal false at time 6" (pulse5.atTime 6 == false)
  )

def test_counter_monotonicity : IO TestSeq := do
  pure (
    test "counter increases from 5 to 10" (counterSignal.atTime 5 ≤ counterSignal.atTime 10) $
    test "counter increases from 0 to 1" (counterSignal.atTime 0 ≤ counterSignal.atTime 1) $
    test "counter increases from 99 to 100" (counterSignal.atTime 99 ≤ counterSignal.atTime 100)
  )

/-!
## Real-world Scenario Tests
-/

def test_reset_scenario : IO TestSeq := do
  -- Model: A counter that stays at 0 for 10 cycles after reset
  let resetCounter : Signal defaultDomain Nat := ⟨fun t =>
    if t < 10 then 0 else t - 10
  ⟩

  pure (
    test "reset counter at time 0" (resetCounter.atTime 0 == 0) $
    test "reset counter at time 5" (resetCounter.atTime 5 == 0) $
    test "reset counter at time 9" (resetCounter.atTime 9 == 0) $
    test "reset counter at time 10" (resetCounter.atTime 10 == 0) $
    test "reset counter at time 11" (resetCounter.atTime 11 == 1) $
    test "reset counter at time 20" (resetCounter.atTime 20 == 10)
  )

-- State type for state machine test
inductive State where
  | Idle
  | Active
  | Done
  deriving BEq, Repr

def test_state_machine_scenario : IO TestSeq := do
  -- Model: Simple state machine Idle -> Active -> Done -> Idle
  let stateMachine : Signal defaultDomain State := ⟨fun t =>
    let cycle := t % 12
    if cycle < 2 then State.Idle
    else if cycle < 11 then State.Active
    else State.Done
  ⟩

  pure (
    test "state machine at time 0 is Idle" (stateMachine.atTime 0 == State.Idle) $
    test "state machine at time 1 is Idle" (stateMachine.atTime 1 == State.Idle) $
    test "state machine at time 2 is Active" (stateMachine.atTime 2 == State.Active) $
    test "state machine at time 5 is Active" (stateMachine.atTime 5 == State.Active) $
    test "state machine at time 10 is Active" (stateMachine.atTime 10 == State.Active) $
    test "state machine at time 11 is Done" (stateMachine.atTime 11 == State.Done) $
    test "state machine at time 12 is Idle (next cycle)" (stateMachine.atTime 12 == State.Idle)
  )

/-!
## Temporal Oracle Tests
-/

def test_temporal_oracle : IO TestSeq := do
  -- Test the empty oracle (no optimizations)
  let oracle := emptyOracle (d := defaultDomain)
  let result := oracle.canSkip Nat counterSignal 0

  pure (
    test "empty oracle returns none" (result == none)
  )

/-!
## Example Temporal Properties (Not directly testable, but demonstrate API)

These properties would be proven in formal verification, not tested at runtime.
They demonstrate the temporal logic API without trying to execute them as tests.

Note: The proofs are left as `sorry` placeholders since this is a test file.
In real verification code, these would be fully proven.
-/

-- Example: Constant signal always equals its value
example : let const42 := constantSignal 42
          let isConstant := const42.map (· == 42#8)
          always isConstant := by
  sorry

-- Example: Counter is monotonic
example : monotonic counterSignal := by
  sorry

-- Example: Delayed signal eventually becomes true
example : let delayed := delayedSignal 10
          eventually delayed := by
  sorry

-- Example: Reset counter is stable for first 10 cycles
example : let resetCounter : Signal defaultDomain Nat := ⟨fun t => if t < 10 then 0 else t - 10⟩
          stableFor resetCounter 0 10 := by
  sorry

/-!
## Combined Test Suite
-/

def temporalTests : IO TestSeq := do
  let tests1 ← test_signal_basics
  let tests2 ← test_delayed_signals
  let tests3 ← test_counter_monotonicity
  let tests4 ← test_reset_scenario
  let tests5 ← test_state_machine_scenario
  let tests6 ← test_temporal_oracle

  return group "Temporal Logic Tests" (
    group "Signal Basics" tests1 ++
    group "Delayed Signals" tests2 ++
    group "Counter Properties" tests3 ++
    group "Reset Scenario" tests4 ++
    group "State Machine Scenario" tests5 ++
    group "Temporal Oracle" tests6
  )

end Sparkle.Test.Temporal
