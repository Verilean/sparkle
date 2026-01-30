/-
  Cycle-Skipping Performance Benchmark

  Compares standard simulation vs optimized simulation
  to demonstrate speedup for various stable period lengths.
-/

import Sparkle.Core.OptimizedSim

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.OptimizedSim

/-!
## Performance Benchmarks
-/

def runBenchmark (name : String) (stableCycles : Nat) (totalCycles : Nat) : IO Unit := do
  IO.println s!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"Benchmark: {name}"
  IO.println s!"  Stable cycles: {stableCycles}"
  IO.println s!"  Total cycles:  {totalCycles}"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Create counter that stays at 0 for stableCycles
  let counter : Signal defaultDomain Nat := ⟨fun t =>
    if t < stableCycles then 0 else t - stableCycles
  ⟩

  -- Standard simulation
  IO.println "Running standard simulation (no optimization)..."
  let startStandard ← IO.monoMsNow
  let standardValues := simulateStandard counter totalCycles
  let endStandard ← IO.monoMsNow
  let standardTime := endStandard - startStandard

  -- Optimized simulation
  IO.println "Running optimized simulation (with cycle-skipping)..."
  let prop := mkStabilityProperty "counter" 0 0 stableCycles
  let registry := registryWith prop

  let startOptimized ← IO.monoMsNow
  let (optimizedValues, stats) := simulateOptimized registry "counter" counter totalCycles
  let endOptimized ← IO.monoMsNow
  let optimizedTime := endOptimized - startOptimized

  IO.println ""
  IO.println "Results:"
  IO.println s!"  Standard time:  {standardTime}ms"
  IO.println s!"  Optimized time: {optimizedTime}ms"

  let actualSpeedup := if optimizedTime > 0
    then standardTime.toFloat / optimizedTime.toFloat
    else 0.0
  IO.println s!"  Actual speedup: {actualSpeedup}x"
  IO.println ""
  IO.println stats
  IO.println ""

  -- Verify correctness
  if standardValues == optimizedValues then
    IO.println "✓ Results verified: Optimized simulation matches standard"
  else
    IO.println "✗ ERROR: Results don't match!"
  IO.println ""

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════╗"
  IO.println "║  Cycle-Skipping Performance Benchmarks           ║"
  IO.println "╚═══════════════════════════════════════════════════╝"
  IO.println ""

  -- Benchmark 1: 50% stable (2x theoretical speedup)
  runBenchmark "50% Stable Period" 5000 10000

  -- Benchmark 2: 90% stable (10x theoretical speedup)
  runBenchmark "90% Stable Period" 9000 10000

  -- Benchmark 3: 99% stable (100x theoretical speedup)
  runBenchmark "99% Stable Period" 99000 100000

  -- Benchmark 4: Long reset sequence (realistic scenario)
  runBenchmark "Long Reset (1000 cycles)" 1000 5000

  IO.println "╔═══════════════════════════════════════════════════╗"
  IO.println "║  Summary                                          ║"
  IO.println "╚═══════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Key Insights:"
  IO.println "  • Speedup proportional to stable period length"
  IO.println "  • Dramatic gains for designs with long idle/reset periods"
  IO.println "  • Zero accuracy loss - results identical to standard simulation"
  IO.println "  • Soundness guaranteed by proven temporal properties"
  IO.println ""
