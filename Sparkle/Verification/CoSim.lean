/-
  Co-simulation Infrastructure

  Enables bit-accurate verification and benchmarking between:
  - Lean simulation (Sparkle Signal semantics)
  - Verilator simulation (compiled Verilog)

  This module provides infrastructure to:
  1. Generate Verilog files from Sparkle modules
  2. Run both Lean and Verilator simulations with same inputs
  3. Compare outputs for bit-accuracy
  4. Measure and compare performance
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog

namespace Sparkle.Verification.CoSim

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog

/-!
## Test Vector Format

Test vectors contain input/output pairs for verification.
-/

structure TestVector (α : Type) where
  inputs : List α
  expectedOutputs : List α
  deriving Repr

/-!
## Simulation Results

Results from running simulations in Lean and Verilator.
-/

structure SimulationResult (α : Type) where
  leanOutputs : List α
  verilatorOutputs : Option (List α)  -- None if Verilator not available
  cyclesSimulated : Nat
  leanTimeNs : Nat  -- Simulation time in nanoseconds
  verilatorTimeNs : Option Nat
  deriving Repr

/-!
## Bit-Accurate Comparison

Compare outputs from Lean and Verilator simulations.
-/

def compareBitVec (lean : BitVec n) (verilator : BitVec n) : Bool :=
  lean == verilator

def compareOutputs {α : Type} [BEq α] (lean : List α) (verilator : List α) : Bool :=
  lean.length == verilator.length && (lean.zip verilator).all fun (l, v) => l == v

structure ComparisonResult where
  totalCycles : Nat
  matchingCycles : Nat
  mismatchCycles : List Nat
  bitAccurate : Bool
  deriving Repr

def verifyBitAccuracy {α : Type} [BEq α]
    (leanOutputs : List α) (verilatorOutputs : List α) : ComparisonResult :=
  let zipped : List (α × α) := leanOutputs.zip verilatorOutputs
  let indexed : List (Nat × (α × α)) := List.range zipped.length |>.zip zipped
  let matchList : List (Nat × (α × α)) := List.filter (fun (_, (l, v)) => l == v) indexed
  let mismatches : List (Nat × (α × α)) := List.filter (fun (_, (l, v)) => l != v) indexed
  { totalCycles := zipped.length
    matchingCycles := matchList.length
    mismatchCycles := List.map (fun (i, _) => i) mismatches
    bitAccurate := List.isEmpty mismatches }

/-!
## Verilator Integration

Functions to generate Verilog and prepare for Verilator compilation.
-/

/-- Generate Verilog file from a Sparkle module definition -/
def generateVerilogFile (declName : Lean.Name) (outputPath : String) : Lean.Meta.MetaM Unit := do
  let design ← synthesizeHierarchical declName
  let verilog := toVerilogDesign design
  IO.FS.writeFile outputPath verilog
  return ()

/-- Generate testbench inputs as hex values -/
def generateTestVectorFile {n : Nat} (inputs : List (BitVec n)) (outputPath : String) : IO Unit := do
  let hexValues : List String := List.map (fun bv =>
    let value := bv.toNat
    let hexStr := String.ofList (Nat.toDigits 16 value).reverse
    s!"{hexStr}\n"
  ) inputs
  let content := String.join hexValues
  IO.FS.writeFile outputPath content

/-!
## Benchmarking Infrastructure

Measure simulation performance.
-/

structure BenchmarkResult where
  moduleName : String
  cycles : Nat
  leanTimeNs : Nat
  verilatorTimeNs : Option Nat
  leanCyclesPerSecond : Float
  verilatorCyclesPerSecond : Option Float
  speedup : Option Float  -- Verilator speedup over Lean
  deriving Repr

def calculateCyclesPerSecond (cycles : Nat) (timeNs : Nat) : Float :=
  if timeNs == 0 then 0.0
  else (cycles.toFloat / timeNs.toFloat) * 1e9

def calculateSpeedup (leanTimeNs : Nat) (verilatorTimeNs : Nat) : Float :=
  if verilatorTimeNs == 0 then 0.0
  else leanTimeNs.toFloat / verilatorTimeNs.toFloat

def createBenchmarkResult (name : String) (result : SimulationResult α) : BenchmarkResult :=
  let leanCPS := calculateCyclesPerSecond result.cyclesSimulated result.leanTimeNs
  let verilatorCPS := result.verilatorTimeNs.map (calculateCyclesPerSecond result.cyclesSimulated)
  let speedup := match result.verilatorTimeNs with
    | none => none
    | some vTime => some (calculateSpeedup result.leanTimeNs vTime)
  { moduleName := name
    cycles := result.cyclesSimulated
    leanTimeNs := result.leanTimeNs
    verilatorTimeNs := result.verilatorTimeNs
    leanCyclesPerSecond := leanCPS
    verilatorCyclesPerSecond := verilatorCPS
    speedup := speedup }

/-!
## High-Level Co-Simulation API

Run both simulations and compare results.
-/

/-- Run Lean simulation and measure time -/
def runLeanSimulation {dom : DomainConfig} {α : Type}
    (circuit : Signal dom α) (cycles : Nat) : IO (List α × Nat) := do
  let startTime ← IO.monoNanosNow
  let outputs := List.range cycles |>.map circuit.atTime
  let endTime ← IO.monoNanosNow
  let elapsed := endTime - startTime
  return (outputs, elapsed)

/-- Check if Verilator is available -/
def verilatorAvailable : IO Bool := do
  try
    let output ← IO.Process.output { cmd := "which", args := #["verilator"] }
    return output.exitCode == 0
  catch _ =>
    return false

/-!
## Test Report Generation

Generate human-readable reports from co-simulation results.
-/

def formatComparisonReport (result : ComparisonResult) : String :=
  let status := if result.bitAccurate then "✓ PASS" else "✗ FAIL"
  let accuracy := (result.matchingCycles.toFloat / result.totalCycles.toFloat) * 100.0
  s!"Bit-Accuracy Verification: {status}\n" ++
  s!"  Total cycles: {result.totalCycles}\n" ++
  s!"  Matching: {result.matchingCycles} ({accuracy}%)\n" ++
  s!"  Mismatches: {result.mismatchCycles.length}\n" ++
  if result.mismatchCycles.isEmpty then ""
  else s!"  Mismatch cycles: {result.mismatchCycles}\n"

def formatBenchmarkReport (result : BenchmarkResult) : String :=
  let leanCPS := s!"{result.leanCyclesPerSecond}"
  s!"Benchmark: {result.moduleName}\n" ++
  s!"  Cycles: {result.cycles}\n" ++
  s!"  Lean simulation: {result.leanTimeNs}ns ({leanCPS} cycles/sec)\n" ++
  match result.verilatorTimeNs, result.verilatorCyclesPerSecond, result.speedup with
  | some vTime, some vCPS, some speedup =>
    let vCPSStr := s!"{vCPS}"
    let speedupStr := s!"{speedup}"
    s!"  Verilator simulation: {vTime}ns ({vCPSStr} cycles/sec)\n" ++
    s!"  Speedup: {speedupStr}x\n"
  | _, _, _ =>
    s!"  Verilator: Not available\n"

end Sparkle.Verification.CoSim
