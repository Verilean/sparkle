/-
  Simple Cycle-Skipping Demonstration

  Shows how proven temporal properties enable simulation optimization.
-/

import Sparkle.Core.OptimizedSim

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.OptimizedSim

/-!
## Example: Reset Sequence Optimization
-/

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════╗"
  IO.println "║  Cycle-Skipping Simulation Demonstration         ║"
  IO.println "╚═══════════════════════════════════════════════════╝"
  IO.println ""

  -- Create a counter that stays at 0 for 1000 cycles (reset)
  let resetCounter : Signal defaultDomain Nat := ⟨fun t =>
    if t < 1000 then 0 else t - 1000
  ⟩

  -- Register the stability property
  let prop := mkStabilityProperty "resetCounter" 0 0 1000
  let registry := registryWith prop

  IO.println "Circuit: Counter with 1000-cycle reset"
  IO.println "  t ∈ [0, 1000): counter = 0 (stable)"
  IO.println "  t ≥ 1000:      counter increments"
  IO.println ""

  -- Simulate 2000 cycles with optimization
  IO.println "Running optimized simulation (2000 cycles)..."
  let (values, stats) := simulateOptimized registry "resetCounter" resetCounter 2000

  IO.println ""
  IO.println "Sample values:"
  IO.println s!"  t=0:     {values[0]!}"
  IO.println s!"  t=500:   {values[500]!}"
  IO.println s!"  t=999:   {values[999]!}"
  IO.println s!"  t=1000:  {values[1000]!}"
  IO.println s!"  t=1500:  {values[1500]!}"
  IO.println s!"  t=1999:  {values[1999]!}"
  IO.println ""
  IO.println stats
  IO.println ""

  -- Verify correctness
  let firstStable := values.take 1000 == List.replicate 1000 0
  let incrementing := values[1500]! == 500  -- Should be counting from 0

  if firstStable && incrementing then
    IO.println "✓ Cycle-skipping produced correct results!"
    IO.println ""
    IO.println "Key insight:"
    IO.println "  Instead of evaluating 1000 stable cycles individually,"
    IO.println "  we skipped forward in 1 evaluation using the proven property."
    IO.println s!"  Speedup: {stats.speedup}x"
  else
    IO.println "✗ ERROR: Results don't match expected values!"
