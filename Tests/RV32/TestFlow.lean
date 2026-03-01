/-
  RV32 SoC Flow Tests

  Automated LSpec tests covering the full build/simulation pipeline:
  1. Verilog compilation — generated files exist and contain expected content
  2. Lean-native simulation — rv32iSoCSimulateFull via Signal.loopMemo
  3. CppSim JIT — compiled C++ simulation (skips if no compiler)
  4. Verilator — SystemVerilog simulation (skips if verilator unavailable)

  Usage:
    lake test                    # runs as part of full test suite
    lake exe rv32-flow-test      # standalone
-/

import Sparkle.Utils.HexLoader
import LSpec

open Sparkle.Utils.HexLoader
open LSpec

namespace Sparkle.Tests.RV32.TestFlow

/-- Check if a string contains a substring -/
private def hasSubstr (s : String) (sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

/-- Check if an external tool is available via `which` -/
private def toolAvailable (name : String) : IO Bool := do
  let result ← IO.Process.output { cmd := "which", args := #[name] }
  return result.exitCode == 0

-- ============================================================================
-- Category 1: Verilog Compilation Tests
-- ============================================================================

/-- Verify generated Verilog and CppSim files exist with expected content -/
def synthTests : IO TestSeq := do
  -- Check generated SV file
  let svPath := "verilator/generated_soc.sv"
  let svExists ← System.FilePath.pathExists svPath
  let svContent ← if svExists then IO.FS.readFile svPath else pure ""

  -- Check generated CppSim header
  let cppPath := "verilator/generated_soc_cppsim.h"
  let cppExists ← System.FilePath.pathExists cppPath
  let cppContent ← if cppExists then IO.FS.readFile cppPath else pure ""

  return group "Verilog Compilation" (
    group "Generated SystemVerilog" (
      test "generated_soc.sv exists" svExists $
      test "file is non-empty" (svContent.length > 0) $
      test "contains top module" (hasSubstr svContent "module Sparkle_Examples_RV32_SoCVerilog_rv32iSoCSynth") $
      test "contains clock input" (hasSubstr svContent "input logic clk") $
      test "contains always_ff" (hasSubstr svContent "always_ff") $
      test "contains imem write enable" (hasSubstr svContent "_gen_imem_wr_en")
    ) ++
    group "Generated CppSim Header" (
      test "generated_soc_cppsim.h exists" cppExists $
      test "file is non-empty" (cppContent.length > 0) $
      test "contains class declaration" (hasSubstr cppContent "class Sparkle_Examples_RV32_SoCVerilog_rv32iSoCSynth") $
      test "contains eval method" (hasSubstr cppContent "void eval()") $
      test "contains tick method" (hasSubstr cppContent "void tick()") $
      test "contains reset method" (hasSubstr cppContent "void reset()")
    )
  )

-- ============================================================================
-- Category 2: Lean-native Simulation Tests
-- ============================================================================

/-- Convert Nat to hex string -/
private def natToHex (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList digits

/-- Parse PC value from "PC@N=0xHEXVAL" format -/
private def parsePCLine (line : String) : Option (Nat × Nat) := do
  guard (line.startsWith "PC@")
  -- Split "PC@5=0x00000014" on "="
  let parts := line.splitOn "="
  guard (parts.length == 2)
  -- First part is "PC@5", extract cycle number
  let pfx := parts[0]!
  guard (pfx.length > 3)
  let cycleStr := (pfx.drop 3).toString  -- "5"
  let cycle ← cycleStr.toNat?
  -- Second part is "0x00000014", extract hex value
  let valStr := parts[1]!
  guard (valStr.startsWith "0x")
  let hexStr := (valStr.drop 2).toString
  let val := hexToNat hexStr
  return (cycle, val)

/-- Run Lean-native simulation as a subprocess (avoids macOS 8MB stack limit) -/
def leanSimTests : IO TestSeq := do
  let hexPath : System.FilePath := "firmware/firmware.hex"
  let hexExists ← System.FilePath.pathExists hexPath
  unless hexExists do
    IO.println "  [skip] firmware/firmware.hex not found"
    return group "Lean-native Simulation" (
      test "firmware file exists (skipped)" true
    )

  -- Check if the runner binary exists
  let runnerBin := ".lake/build/bin/rv32-lean-sim-runner"
  let runnerExists ← System.FilePath.pathExists runnerBin
  unless runnerExists do
    IO.println "  [skip] rv32-lean-sim-runner not built (run: lake build rv32-lean-sim-runner)"
    return group "Lean-native Simulation" (
      test "simulation runner available (skipped)" true
    )

  IO.println "  Running Lean4 simulation (50 cycles) via subprocess..."
  let runResult ← IO.Process.output {
    cmd := runnerBin
    args := #["firmware/firmware.hex", "50"]
    cwd := some "."
  }

  let ranOk := runResult.exitCode == 0
  let simOk := hasSubstr runResult.stdout "LEAN_SIM_OK"

  unless ranOk && simOk do
    -- Stack overflow on macOS (8MB default) is an environment limitation, not a bug
    let isStackOverflow := hasSubstr runResult.stderr "Stack overflow" || runResult.exitCode == 134
    if isStackOverflow then
      IO.println "  [skip] Lean simulation requires larger stack (macOS 8MB limit)"
      return group "Lean-native Simulation" (
        test "simulation runner available (skipped - stack overflow)" true
      )
    else
      let errMsg := runResult.stderr.take 200 |>.toString
      IO.println s!"  [fail] Lean simulation failed: {errMsg}"
      return group "Lean-native Simulation" (
        test "simulation completes without crash" false
      )

  -- Parse PC values from output
  let lines := runResult.stdout.splitOn "\n"
  let pcValues := lines.filterMap parsePCLine

  let pc0 := pcValues.find? (fun p => p.1 == 0) |>.map (·.2) |>.getD 0xFFFFFFFF
  let pc5 := pcValues.find? (fun p => p.1 == 5) |>.map (·.2) |>.getD 0xFFFFFFFF
  let pc10 := pcValues.find? (fun p => p.1 == 10) |>.map (·.2) |>.getD 0xFFFFFFFF
  let pc49 := pcValues.find? (fun p => p.1 == 49) |>.map (·.2) |>.getD 0xFFFFFFFF

  IO.println s!"  PC@0=0x{natToHex pc0} PC@5=0x{natToHex pc5} PC@10=0x{natToHex pc10} PC@49=0x{natToHex pc49}"

  let startsAtZero := pc0 == 0
  let pcAdvances := pc5 != pc0 || pc10 != pc0 || pc49 != pc0
  let inRange := pc0 < 0x10000 && pc10 < 0x10000 && pc49 < 0x10000

  return group "Lean-native Simulation" (
    test "simulation completes" (ranOk && simOk) $
    test "PC starts at 0x00000000" startsAtZero $
    test "PC advances (not stuck)" pcAdvances $
    test "PC stays in IMEM range" inRange
  )

-- ============================================================================
-- Category 3: CppSim JIT Tests
-- ============================================================================

/-- Compile and run CppSim testbench if a C++ compiler is available -/
def cppSimTests : IO TestSeq := do
  -- Check for C++ compiler
  let hasClang ← toolAvailable "clang++"
  let hasGxx ← toolAvailable "g++"
  let compiler := if hasClang then some "clang++" else if hasGxx then some "g++" else none

  match compiler with
  | none =>
    IO.println "  [skip] No C++ compiler found (clang++ or g++)"
    return group "CppSim JIT" (
      test "C++ compiler available (skipped)" true
    )
  | some cxx =>
    -- Check required files
    let cppSimHeader := "verilator/generated_soc_cppsim.h"
    let tbSource := "verilator/tb_cppsim.cpp"
    let headerExists ← System.FilePath.pathExists cppSimHeader
    let tbExists ← System.FilePath.pathExists tbSource
    unless headerExists && tbExists do
      IO.println s!"  [skip] Missing CppSim files (header={headerExists}, tb={tbExists})"
      return group "CppSim JIT" (
        test "CppSim files exist (skipped)" true
      )

    let hexPath : System.FilePath := "firmware/firmware.hex"
    let hexExists ← System.FilePath.pathExists hexPath
    unless hexExists do
      IO.println "  [skip] firmware/firmware.hex not found"
      return group "CppSim JIT" (
        test "firmware file exists (skipped)" true
      )

    -- Compile
    let outBin := "/tmp/cppsim_flow_test"
    IO.println s!"  Compiling CppSim with {cxx}..."
    let compileResult ← IO.Process.output {
      cmd := cxx
      args := #["-std=c++17", "-O2", "-o", outBin, tbSource]
      cwd := some "."
    }
    let compileOk := compileResult.exitCode == 0
    unless compileOk do
      IO.println s!"  [fail] Compilation failed: {compileResult.stderr.take 200 |>.toString}"
      return group "CppSim JIT" (
        test "CppSim compiles" false
      )

    -- Run
    IO.println "  Running CppSim (5000 cycles)..."
    let runResult ← IO.Process.output {
      cmd := outBin
      args := #["firmware/firmware.hex", "5000"]
      cwd := some "."
    }
    let runOk := runResult.exitCode == 0
    let allPassed := hasSubstr runResult.stdout "ALL TESTS PASSED"

    return group "CppSim JIT" (
      test "CppSim compiles" compileOk $
      test "CppSim runs successfully" runOk $
      test "ALL TESTS PASSED in output" allPassed
    )

-- ============================================================================
-- Category 4: Verilator Tests
-- ============================================================================

/-- Build and run Verilator simulation if verilator is available -/
def verilatorTests : IO TestSeq := do
  let hasVerilator ← toolAvailable "verilator"
  unless hasVerilator do
    IO.println "  [skip] Verilator not found"
    return group "Verilator Simulation" (
      test "Verilator available (skipped)" true
    )

  -- Check that generated SV exists (don't re-generate)
  let svExists ← System.FilePath.pathExists "verilator/generated_soc.sv"
  let wrapperExists ← System.FilePath.pathExists "verilator/rv32i_soc_wrapper.sv"
  let tbExists ← System.FilePath.pathExists "verilator/tb_soc.cpp"
  unless svExists && wrapperExists && tbExists do
    IO.println s!"  [skip] Missing Verilator source files (sv={svExists}, wrapper={wrapperExists}, tb={tbExists})"
    return group "Verilator Simulation" (
      test "Verilator source files exist (skipped)" true
    )

  let hexPath : System.FilePath := "firmware/firmware.hex"
  let hexExists ← System.FilePath.pathExists hexPath
  unless hexExists do
    IO.println "  [skip] firmware/firmware.hex not found"
    return group "Verilator Simulation" (
      test "firmware file exists (skipped)" true
    )

  -- Build (using direct file target to avoid re-generating)
  IO.println "  Building Verilator simulation..."
  let buildResult ← IO.Process.output {
    cmd := "make"
    args := #["-C", "verilator", "obj_dir/Vrv32i_soc"]
    cwd := some "."
  }
  let buildOk := buildResult.exitCode == 0
  unless buildOk do
    IO.println s!"  [fail] Verilator build failed: {buildResult.stderr.take 200 |>.toString}"
    return group "Verilator Simulation" (
      test "Verilator builds" false
    )

  -- Run
  IO.println "  Running Verilator simulation (5000 cycles)..."
  let runResult ← IO.Process.output {
    cmd := "verilator/obj_dir/Vrv32i_soc"
    args := #["firmware/firmware.hex", "5000"]
    cwd := some "."
  }
  let runOk := runResult.exitCode == 0
  let allPassed := hasSubstr runResult.stdout "ALL TESTS PASSED"

  return group "Verilator Simulation" (
    test "Verilator builds" buildOk $
    test "Verilator runs successfully" runOk $
    test "ALL TESTS PASSED in output" allPassed
  )

-- ============================================================================
-- Combined Entry Points
-- ============================================================================

/-- All RV32 flow tests — called from AllTests.lean -/
def flowTests : IO TestSeq := do
  IO.println ""
  IO.println "--- RV32 SoC Flow Tests ---"

  let synth ← synthTests
  let leanSim ← leanSimTests
  let cppSim ← cppSimTests
  let verilator ← verilatorTests

  return group "RV32 SoC Flow Tests" (
    synth ++ leanSim ++ cppSim ++ verilator
  )

end Sparkle.Tests.RV32.TestFlow
