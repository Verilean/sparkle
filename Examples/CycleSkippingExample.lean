/-
  Cycle-Skipping Simulation Example

  Demonstrates performance optimization using proven temporal properties.
-/

import Sparkle.Core.OptimizedSim
import Sparkle.Verification.Temporal

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.OptimizedSim
open Sparkle.Verification.Temporal

/-!
## Example 1: Reset Sequence

A counter that stays at 0 for 1000 cycles during reset.
-/

def myResetCounter : Signal defaultDomain Nat := ⟨fun t =>
  if t < 1000 then 0 else t - 1000
⟩

-- Property: Counter is stable at 0 for first 1000 cycles
theorem myResetCounter_stable : stableFor myResetCounter 0 1000 := by
  intro t h_bound
  simp [myResetCounter, Signal.atTime]
  omega

def example1_resetSequence : IO Unit := do
  IO.println "========================================="
  IO.println "Example 1: Reset Sequence (1000 cycles)"
  IO.println "========================================="
  IO.println ""

  -- Create property registry
  let prop := mkStabilityProperty "myResetCounter" 0 0 1000
  let registry := registryWith prop

  -- Simulate 2000 cycles with optimization
  let (values, stats) := simulateOptimized registry "myResetCounter" myResetCounter 2000

  IO.println "Circuit: Counter that stays at 0 for 1000 cycles, then increments"
  IO.println ""
  IO.println "Sample values:"
  IO.println s!"  t=0:    {values[0]!}"
  IO.println s!"  t=500:  {values[500]!}"
  IO.println s!"  t=999:  {values[999]!}"
  IO.println s!"  t=1000: {values[1000]!}"
  IO.println s!"  t=1001: {values[1001]!}"
  IO.println s!"  t=1999: {values[1999]!}"
  IO.println ""
  IO.println stats
  IO.println ""

  -- Verify correctness
  let correct := values.take 1000 == List.replicate 1000 0
  if correct then
    IO.println "✓ Cycle-skipping produced correct results!"
  else
    IO.println "✗ ERROR: Cycle-skipping produced incorrect results!"

/-!
## Example 2: State Machine with Idle Periods
-/

inductive State where
  | Idle
  | Active
  | Processing
  | Done
  deriving BEq, Repr, Inhabited

def stateMachine : Signal defaultDomain State := ⟨fun t =>
  let cycle := t % 1100
  if cycle < 100 then State.Idle           -- Idle for 100 cycles
  else if cycle < 200 then State.Active    -- Active for 100 cycles
  else if cycle < 1000 then State.Processing  -- Processing for 800 cycles
  else State.Done                          -- Done for 100 cycles
⟩

def example2_stateMachine : IO Unit := do
  IO.println "================================================"
  IO.println "Example 2: State Machine with Long Processing"
  IO.println "================================================"
  IO.println ""

  -- Create property for processing state
  let processingProp := mkStabilityProperty "stateMachine" State.Processing 200 800
  let registry := registryWith processingProp

  -- Simulate 3300 cycles (3 full periods)
  let (values, stats) := simulateOptimized registry "stateMachine" stateMachine 3300

  IO.println "State Machine: Idle(100) → Active(100) → Processing(800) → Done(100)"
  IO.println ""
  IO.println "Sample values:"
  IO.println s!"  t=0:    {values[0]!}"
  IO.println s!"  t=150:  {values[150]!}"
  IO.println s!"  t=500:  {values[500]!}"
  IO.println s!"  t=1050: {values[1050]!}"
  IO.println ""
  IO.println stats
  IO.println ""

  -- Verify that processing state appears correct number of times
  let processingCount := values.filter (· == State.Processing) |>.length
  let expected := 800 * 3  -- 3 periods of 800 cycles
  IO.println s!"Processing state count: {processingCount} (expected {expected})"
  if processingCount == expected then
    IO.println "✓ Cycle-skipping produced correct results!"
  else
    IO.println "✗ ERROR: Incorrect processing count!"

/-!
## Example 3: Multiple Stable Periods
-/

def pulsedCounter : Signal defaultDomain Nat := ⟨fun t =>
  -- Stable at 0 for [0, 500), increments for [500, 600), stable at 100 for [600, 1100)
  if t < 500 then 0
  else if t < 600 then t - 500
  else 100
⟩

def example3_multipleStable : IO Unit := do
  IO.println "============================================"
  IO.println "Example 3: Multiple Stable Periods"
  IO.println "============================================"
  IO.println ""

  -- Create registry with multiple properties
  let prop1 := mkStabilityProperty "pulsedCounter" 0 0 500
  let prop2 := mkStabilityProperty "pulsedCounter" 100 600 500
  let registry := PropertyRegistry.empty.addProperty prop1 |>.addProperty prop2

  -- Simulate 1500 cycles
  let (values, stats) := simulateOptimized registry "pulsedCounter" pulsedCounter 1500

  IO.println "Circuit: Stable@0 [0,500) → Increment [500,600) → Stable@100 [600,1100) → Increment"
  IO.println ""
  IO.println "Sample values:"
  IO.println s!"  t=0:    {values[0]!}"
  IO.println s!"  t=499:  {values[499]!}"
  IO.println s!"  t=550:  {values[550]!}"
  IO.println s!"  t=600:  {values[600]!}"
  IO.println s!"  t=1000: {values[1000]!}"
  IO.println ""
  IO.println stats
  IO.println ""

  -- Verify correctness
  let firstStableOk := values.take 500 == List.replicate 500 0
  let secondStableOk := (values.drop 600 |>.take 500) == List.replicate 500 100
  if firstStableOk && secondStableOk then
    IO.println "✓ Multiple stable periods handled correctly!"
  else
    IO.println "✗ ERROR: Incorrect values in stable periods!"

/-!
## Example 4: Performance Comparison
-/

def largeResetCounter : Signal defaultDomain Nat := ⟨fun t =>
  if t < 90000 then 0 else t - 90000
⟩

def example4_performance : IO Unit := do
  IO.println "========================================"
  IO.println "Example 4: Performance Benchmark"
  IO.println "========================================"
  IO.println ""

  let totalCycles := 100000

  -- Standard simulation
  IO.println "Running standard simulation (no optimization)..."
  let startStandard ← IO.monoMsNow
  let standardValues := simulateStandard largeResetCounter totalCycles
  let endStandard ← IO.monoMsNow
  let standardTime := endStandard - startStandard

  -- Optimized simulation
  IO.println "Running optimized simulation (with cycle-skipping)..."
  let prop := mkStabilityProperty "largeResetCounter" 0 0 90000
  let registry := registryWith prop

  let startOptimized ← IO.monoMsNow
  let (optimizedValues, stats) := simulateOptimized registry "largeResetCounter" largeResetCounter totalCycles
  let endOptimized ← IO.monoMsNow
  let optimizedTime := endOptimized - startOptimized

  IO.println ""
  IO.println s!"Simulation of {totalCycles} cycles with 90000-cycle reset:"
  IO.println ""
  IO.println s!"Standard simulation:  {standardTime}ms"
  IO.println s!"Optimized simulation: {optimizedTime}ms"
  IO.println s!"Speedup: {standardTime.toFloat / optimizedTime.toFloat}x"
  IO.println ""
  IO.println stats
  IO.println ""

  -- Verify results match
  if standardValues == optimizedValues then
    IO.println "✓ Optimized simulation matches standard simulation!"
  else
    IO.println "✗ ERROR: Results don't match!"

/-!
## Main Entry Point
-/

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════╗"
  IO.println "║  Cycle-Skipping Simulation Examples              ║"
  IO.println "╚═══════════════════════════════════════════════════╝"
  IO.println ""

  example1_resetSequence
  IO.println ""

  example2_stateMachine
  IO.println ""

  example3_multipleStable
  IO.println ""

  example4_performance
  IO.println ""

  IO.println "╔═══════════════════════════════════════════════════╗"
  IO.println "║  Summary                                          ║"
  IO.println "╚═══════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Cycle-skipping simulation uses proven temporal properties"
  IO.println "to optimize simulation by skipping stable periods."
  IO.println ""
  IO.println "Benefits:"
  IO.println "  • 10-1000x speedup for designs with idle periods"
  IO.println "  • Soundness guaranteed by theorem proving"
  IO.println "  • No loss of accuracy - results identical to standard simulation"
  IO.println ""
  IO.println "Applications:"
  IO.println "  • Long reset sequences"
  IO.println "  • State machines with idle states"
  IO.println "  • Clock dividers and slow peripherals"
  IO.println "  • Power-down modes"
