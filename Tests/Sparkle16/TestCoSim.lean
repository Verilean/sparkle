/-
  Co-simulation and Benchmarking Tests for Sparkle16

  Tests bit-accurate verification and performance benchmarking between:
  - Lean simulation (Sparkle semantics)
  - Verilator simulation (compiled Verilog)

  Uses Sparkle16 ALU and datapath as test subjects.
-/

import Sparkle
import Sparkle.Verification.CoSim
import LSpec
import Tests.Sparkle16.TestALU
import Tests.Sparkle16.TestHierarchical

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.CoSim
open LSpec

namespace Sparkle16.Test

/-!
## Co-Simulation Tests

These tests verify:
1. Verilog generation for Sparkle16 modules
2. Lean simulation produces consistent results
3. Bit-accuracy when Verilator is available
4. Performance comparison
-/

/-- Test: Generate Verilog files for Sparkle16 ALU -/
def test_generate_alu_verilog : IO TestSeq := do
  -- Create temporary directory for generated files
  let tmpDir := "/tmp/sparkle_cosim"
  IO.FS.createDirAll tmpDir

  -- Generate Verilog for ALU
  let verilogPath := s!"{tmpDir}/sparkle16_alu.v"

  -- Set up Lean environment
  let mods : Array Lean.Import := #[
    { module := `Sparkle },
    { module := `Sparkle.Compiler.Elab },
    { module := `Tests.Sparkle16.TestALU }
  ]
  let env ← Lean.importModules mods {} (trustLevel := 1024)
  let coreCtx : Lean.Core.Context := { fileName := "<test>", fileMap := default }
  let coreState : Lean.Core.State := { env := env }

  -- Synthesize and generate Verilog
  let (design, _, _) ← Lean.Meta.MetaM.toIO
    (Sparkle.Compiler.Elab.synthesizeHierarchical ``Sparkle16.Test.alu)
    coreCtx coreState

  let verilog := Sparkle.Backend.Verilog.toVerilogDesign design
  IO.FS.writeFile verilogPath verilog

  -- Read file to verify generation
  let content ← IO.FS.readFile verilogPath

  return group "Verilog Generation for Co-Sim" (
    test "File contains module declaration" (content.contains "module Sparkle16_Test_alu") $
    test "File contains inputs" (content.contains "input") $
    test "File contains outputs" (content.contains "output") $
    test "File is non-empty" (content.length > 100)
  )

/-!
## Lean Simulation Benchmarking

Test pure Lean simulation performance.
-/

def test_lean_alu_benchmark : IO TestSeq := do
  -- Create test signals
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (10 + t)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (20 + t)⟩
  let sel := Signal.pure false  -- ADD operation
  let result := alu sel a b

  -- Benchmark small simulation (100 cycles)
  let cycles := 100
  let (outputs, timeNs) ← runLeanSimulation result cycles

  let benchmark : BenchmarkResult := {
    moduleName := "Sparkle16_ALU"
    cycles := cycles
    leanTimeNs := timeNs
    verilatorTimeNs := none
    leanCyclesPerSecond := calculateCyclesPerSecond cycles timeNs
    verilatorCyclesPerSecond := none
    speedup := none
  }

  IO.println (formatBenchmarkReport benchmark)

  return group "Lean ALU Benchmark (100 cycles)" (
    test "simulated correct number of cycles" (outputs.length == cycles) $
    test "simulation completed" (timeNs > 0) $
    test "outputs are correct" (
      -- Verify first few outputs
      outputs[0]! == 30#16 &&  -- 10 + 20
      outputs[1]! == 32#16 &&  -- 11 + 21
      outputs[2]! == 34#16     -- 12 + 22
    ) $
    test "performance measured" (benchmark.leanCyclesPerSecond > 0.0)
  )

/-!
## Datapath Simulation Benchmark

Test hierarchical module (ALU + register) performance.
-/

def test_lean_datapath_benchmark : IO TestSeq := do
  -- Create test signals
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 10)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 5)⟩
  let sel := Signal.pure false
  let result := datapath sel a b

  -- Benchmark
  let cycles := 100
  let (outputs, timeNs) ← runLeanSimulation result cycles

  let benchmark : BenchmarkResult := {
    moduleName := "Sparkle16_Datapath"
    cycles := cycles
    leanTimeNs := timeNs
    verilatorTimeNs := none
    leanCyclesPerSecond := calculateCyclesPerSecond cycles timeNs
    verilatorCyclesPerSecond := none
    speedup := none
  }

  IO.println (formatBenchmarkReport benchmark)

  return group "Lean Datapath Benchmark (100 cycles)" (
    test "simulated correct number of cycles" (outputs.length == cycles) $
    test "simulation completed" (timeNs > 0) $
    test "register delay works" (
      -- t=0: initial value (0)
      -- t=1: still 0 (register delay)
      -- t=2: alu(t=1) = 10 + 5 = 15
      outputs[0]! == 0#16 &&
      outputs[1]! == 0#16 &&
      outputs[2]! == 15#16
    ) $
    test "performance measured" (benchmark.leanCyclesPerSecond > 0.0)
  )

/-!
## Bit-Accurate Comparison Tests

Test comparison infrastructure (without actual Verilator for now).
-/

def test_bit_accuracy_comparison : IO TestSeq := do
  -- Create test data
  let leanOutputs := [10#16, 20#16, 30#16, 40#16, 50#16]
  let verilatorOutputs := [10#16, 20#16, 30#16, 40#16, 50#16]  -- Same
  let mismatchOutputs := [10#16, 20#16, 31#16, 40#16, 50#16]   -- Different at index 2

  let resultMatch := verifyBitAccuracy leanOutputs verilatorOutputs
  let resultMismatch := verifyBitAccuracy leanOutputs mismatchOutputs

  IO.println (formatComparisonReport resultMatch)
  IO.println (formatComparisonReport resultMismatch)

  return group "Bit-Accuracy Comparison" (
    test "matching outputs are bit-accurate" resultMatch.bitAccurate $
    test "matching has no mismatches" (resultMatch.mismatchCycles.isEmpty) $
    test "matching has correct total" (resultMatch.totalCycles == 5) $
    test "matching has all matching" (resultMatch.matchingCycles == 5) $
    test "mismatch detected" (not resultMismatch.bitAccurate) $
    test "mismatch count correct" (resultMismatch.matchingCycles == 4) $
    test "mismatch location identified" (resultMismatch.mismatchCycles == [2])
  )

/-!
## Verilator Availability Test

Check if Verilator is installed for full co-simulation.
-/

def test_verilator_availability : IO TestSeq := do
  let available ← verilatorAvailable

  if available then
    IO.println "✓ Verilator is available for co-simulation"
  else
    IO.println "⚠ Verilator not found - skipping Verilator co-simulation tests"
    IO.println "  Install Verilator to enable full co-simulation: sudo apt-get install verilator"

  return group "Verilator Availability" (
    test "verilator check completed" true  -- Always passes, just informational
  )

/-!
## Large-Scale Benchmark

Test performance with more cycles to get meaningful measurements.
-/

def test_large_scale_benchmark : IO TestSeq := do
  IO.println "\n=== Large-Scale Benchmark (1000 cycles) ==="

  -- ALU benchmark
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t % 256)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 ((t * 3) % 256)⟩
  let sel := Signal.pure false
  let aluResult := alu sel a b

  let cycles := 1000
  let (aluOutputs, aluTime) ← runLeanSimulation aluResult cycles

  let aluBench : BenchmarkResult := {
    moduleName := "Sparkle16_ALU_Large"
    cycles := cycles
    leanTimeNs := aluTime
    verilatorTimeNs := none
    leanCyclesPerSecond := calculateCyclesPerSecond cycles aluTime
    verilatorCyclesPerSecond := none
    speedup := none
  }

  IO.println (formatBenchmarkReport aluBench)

  -- Datapath benchmark
  let datapathResult := datapath sel a b
  let (datapathOutputs, datapathTime) ← runLeanSimulation datapathResult cycles

  let datapathBench : BenchmarkResult := {
    moduleName := "Sparkle16_Datapath_Large"
    cycles := cycles
    leanTimeNs := datapathTime
    verilatorTimeNs := none
    leanCyclesPerSecond := calculateCyclesPerSecond cycles datapathTime
    verilatorCyclesPerSecond := none
    speedup := none
  }

  IO.println (formatBenchmarkReport datapathBench)

  return group "Large-Scale Benchmark" (
    test "ALU: 1000 cycles simulated" (aluOutputs.length == cycles) $
    test "Datapath: 1000 cycles simulated" (datapathOutputs.length == cycles) $
    test "ALU performance > 1k cycles/sec" (aluBench.leanCyclesPerSecond > 1000.0) $
    test "Datapath performance > 1k cycles/sec" (datapathBench.leanCyclesPerSecond > 1000.0) $
    test "Both simulations completed" (aluTime > 0 && datapathTime > 0)
  )

/-!
## Combined Test Suite
-/

def coSimTests : IO TestSeq := do
  let verilogGen ← test_generate_alu_verilog
  let aluBench ← test_lean_alu_benchmark
  let datapathBench ← test_lean_datapath_benchmark
  let bitAccuracy ← test_bit_accuracy_comparison
  let verilatorAvail ← test_verilator_availability
  let largeBench ← test_large_scale_benchmark

  return group "Co-Simulation and Benchmarking Tests" (
    verilogGen ++
    aluBench ++
    datapathBench ++
    bitAccuracy ++
    verilatorAvail ++
    largeBench
  )

end Sparkle16.Test
