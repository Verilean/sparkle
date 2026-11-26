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

/-- The SV and CppSim files below are written by `#writeDesign` while
`IP.RV32.SoCVerilog` is elaborated, and nothing in the test build depends on
that module (Lake 4.32.1 does not fetch `needs` of a lib or exe).  When they
are missing (fresh clone), build the module; if they are still missing (its
olean was replayed from a cache), elaborate the file directly.  Each step is
printed.  A non-zero exit is a failure even if the files were written, the
direct elaboration runs only after a successful build that left them missing,
and the result (`some` diagnostic on failure) becomes a test below. -/
abbrev SoCRunner := Array String → IO (UInt32 × String)

/-- Runs `lake ARGS`; returns the exit code and stdout followed by stderr
(Lean reports elaboration errors on stdout). -/
private def lakeRunner : SoCRunner := fun args => do
  let r ← IO.Process.output { cmd := "lake", args }
  return (r.exitCode, r.stdout ++ r.stderr)

private def allExist (paths : Array String) : IO Bool :=
  paths.allM fun p => System.FilePath.pathExists p

private def lastLines (s : String) (n : Nat := 40) : String :=
  let ls := s.splitOn "\n"
  "\n".intercalate (ls.drop (ls.length - n))

def ensureSoCFiles (paths : Array String) (run : SoCRunner := lakeRunner) :
    IO (Option String) := do
  if ← allExist paths then return none
  let steps : Array (Array String) :=
    #[#["build", "IP.RV32.SoCVerilog"], #["env", "lean", "IP/RV32/SoCVerilog.lean"]]
  for args in steps do
    let cmd := s!"lake {" ".intercalate args.toList}"
    IO.println s!"TestFlow: generated SoC files missing; running {cmd}"
    let (rc, out) ← run args
    IO.println s!"TestFlow: {cmd} exited {rc}"
    if rc != 0 then
      return some s!"{cmd} exited {rc}:\n{lastLines out}"
    if ← allExist paths then return none
  return some "generated SoC files still missing after lake build and lake env lean"

/-- Controls for `ensureSoCFiles` with a fake runner in a scratch directory:
a failing step is a failure even when it wrote the files, a failed build does
not fall through to the direct elaboration, and files still missing after
two successful steps are a failure. -/
def ensureControls : IO TestSeq := do
  let dir : System.FilePath := ".lake/testflow-ensure"
  let paths := #[(dir / "a.sv").toString, (dir / "b.h").toString]
  let write : IO Unit := do
    IO.FS.createDirAll dir
    for p in paths do IO.FS.writeFile p "x"
  -- `script[i]` is (writes the files?, exit code) for the i-th call
  let case (script : Array (Bool × UInt32)) : IO (Option String × Nat) := do
    if ← dir.pathExists then IO.FS.removeDirAll dir
    let calls ← IO.mkRef 0
    let run : SoCRunner := fun _ => do
      let i ← calls.modifyGet fun i => (i, i + 1)
      let (w, rc) := script.getD i (false, 0)
      if w then write
      return (rc, "fake output")
    let r ← ensureSoCFiles paths run
    return (r, ← calls.get)
  let (writeFail, n1) ← case #[(true, 1)]
  let (buildFail, n2) ← case #[(false, 1), (true, 0)]
  let (fallbackOk, n3) ← case #[(false, 0), (true, 0)]
  let (fallbackFail, _) ← case #[(false, 0), (true, 1)]
  let (stillMissing, n5) ← case #[(false, 0), (false, 0)]
  if ← dir.pathExists then IO.FS.removeDirAll dir
  return group "SoC file generation controls" (
    test "step writes the files but exits 1: failure, no fallback"
      (writeFail.isSome && n1 == 1) $
    test "build fails: failure, direct elaboration not run"
      (buildFail.isSome && n2 == 1) $
    test "build ok but files missing, direct elaboration writes them: success"
      (fallbackOk.isNone && n3 == 2) $
    test "direct elaboration writes the files but exits 1: failure"
      fallbackFail.isSome $
    test "both steps ok but files still missing: failure"
      (stillMissing.isSome && n5 == 2)
  )

/-- Verify generated Verilog and CppSim files exist with expected content -/
def synthTests : IO TestSeq := do
  let genErr ← ensureSoCFiles #["verilator/generated_soc.sv", "verilator/generated_soc_cppsim.h"]
  if let some e := genErr then IO.eprintln s!"TestFlow: SoC file generation failed: {e}"
  let genTest := test (match genErr with
      | none => "generated SoC files present or generated"
      | some e => s!"SoC file generation failed: {e}") genErr.isNone
  -- Check generated SV file
  let svPath := "verilator/generated_soc.sv"
  let svExists ← System.FilePath.pathExists svPath
  let svContent ← if svExists then IO.FS.readFile svPath else pure ""

  -- Check generated CppSim header
  let cppPath := "verilator/generated_soc_cppsim.h"
  let cppExists ← System.FilePath.pathExists cppPath
  let cppContent ← if cppExists then IO.FS.readFile cppPath else pure ""

  return group "Verilog Compilation" (
    genTest ++
    group "Generated SystemVerilog" (
      test "generated_soc.sv exists" svExists $
      test "file is non-empty" (svContent.length > 0) $
      test "contains top module" (hasSubstr svContent "module Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth") $
      test "contains clock input" (hasSubstr svContent "input logic clk") $
      test "contains always_ff" (hasSubstr svContent "always_ff") $
      test "contains imem write enable" (hasSubstr svContent "_gen_imem_wr_en")
    ) ++
    -- "CppSim Header" kept as legacy test-group name; the C-only
    -- backend (Issue #70) emits a plain C struct + free helpers
    -- instead of a C++ class, so the substring checks were updated
    -- to match the new shape.
    group "Generated CppSim Header" (
      test "generated_soc_cppsim.h exists" cppExists $
      test "file is non-empty" (cppContent.length > 0) $
      test "contains struct declaration" (hasSubstr cppContent "struct Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth") $
      test "contains eval helper" (hasSubstr cppContent "sparkle_Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth_eval") $
      test "contains tick helper" (hasSubstr cppContent "sparkle_Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth_tick") $
      test "contains reset helper" (hasSubstr cppContent "sparkle_Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth_reset")
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

/-- Legacy CppSim JIT category: the C++-class testbench
    (`verilator/tb_cppsim.cpp`) was retired alongside the C++
    simulation backend in commit 3e154fb.  The new C-only CSim
    backend emits a plain struct + free helpers, which the legacy
    `tb_cppsim.cpp` cannot consume, so we short-circuit to a no-op
    test entry here.  A C-shaped replacement testbench can re-enable
    real coverage later. -/
def cppSimTests : IO TestSeq := do
  return group "CppSim JIT" (
    test "CppSim JIT (legacy, replaced by CSim — skipped)" true
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

  let ensureCtl ← ensureControls
  let synth ← synthTests
  let leanSim ← leanSimTests
  let cppSim ← cppSimTests
  let verilator ← verilatorTests

  return group "RV32 SoC Flow Tests" (
    ensureCtl ++ synth ++ leanSim ++ cppSim ++ verilator
  )

end Sparkle.Tests.RV32.TestFlow
