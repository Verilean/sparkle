/-
  UVM testbenches generated from the Lean transaction-level tests
  (`Sparkle.Verification.Tlm.Uvm`), run on the Verilog Sparkle emits.

  Emission always runs: for each design the testbench is written to
  `.lake/build/gen/uvm/<name>_tb.sv`.  With `SPARKLE_UVM_HOME` pointing at
  a UVM library source tree (the directory that contains `src/uvm_pkg.sv`,
  e.g. a checkout of accellera-official/uvm-core) and `verilator` on PATH,
  each testbench is compiled and run:

    * FIFO, and the 3x+1 stage, with the consumer ready in 60 % of cycles:
      zero UVM errors and every expected transaction matched;
    * the stage that drops data under back-pressure: the UVM scoreboard
      must report errors.

  The stimulus and the expected results are the ones the Lean tests use
  (`Tests.TlmTest.items`, `stageModel`).
-/
import Sparkle.Verification.TlmUvm
import Tests.TlmTest

open Sparkle.Verification.Tlm.Uvm
open Sparkle.Tests.TlmTest

/-- The count on a `UVM_ERROR :    N` summary line. -/
def uvmCount (log severity : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun line =>
    match line.splitOn s!"{severity} :" with
    | [_, rest] => rest.trim.toNat?
    | _ => none

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def main : IO Unit := do
  let dir := ".lake/build/gen/uvm"
  IO.FS.createDirAll dir
  -- (bench, DUT Verilog written by `#sim`, expect a clean run)
  let cases : List (Bench × String × Bool) :=
    [ (fifoBench, ".lake/build/gen/sim/fifoTop.sv", true)
    , (stageBench "stage_tb" "Sparkle_Tests_TlmTest_stage" 60, ".lake/build/gen/sim/stage.sv", true)
    , (stageBench "drops_tb" "Sparkle_Tests_TlmTest_stageDrops" 50, ".lake/build/gen/sim/stageDrops.sv", false) ]
  let mut ok := true
  for (b, dutSv, _) in cases do
    let tb := emit b
    IO.FS.writeFile s!"{dir}/{b.name}.sv" tb
    let shape := contains tb s!"class {b.name}_test extends uvm_test" &&
      contains tb s!"{b.dutModule} dut (" && contains tb "uvm_config_db #(virtual"
    if !shape || !(← System.FilePath.pathExists dutSv) then
      IO.eprintln s!"[uvm] {b.name}: bad emission, or {dutSv} is missing (build Tests.TlmTest)"
      ok := false
    else IO.println s!"[uvm] emitted {dir}/{b.name}.sv ({tb.length} chars)"
  let uvmHome? ← IO.getEnv "SPARKLE_UVM_HOME"
  let haveVerilator := (← IO.Process.output { cmd := "which", args := #["verilator"] }).exitCode == 0
  match uvmHome?, haveVerilator with
  | some uvmHome, true =>
    for (b, dutSv, expectClean) in cases do
      let objDir := s!"{dir}/{b.name}_obj"
      let r ← IO.Process.output {
        cmd := "verilator"
        args := #["--binary", "--timing", "-j", "4", "--Mdir", objDir,
                  "-Wno-fatal", "-Wno-lint", "-Wno-style", "+define+UVM_NO_DPI",
                  s!"+incdir+{uvmHome}/src", s!"{uvmHome}/src/uvm_pkg.sv",
                  dutSv, s!"{dir}/{b.name}.sv", "--top-module", s!"{b.name}_top"]
        stdin := .null }
      if r.exitCode != 0 then
        IO.eprintln s!"[uvm] {b.name}: verilator failed:\n{r.stderr.take 3000}"
        ok := false
        continue
      let run ← IO.Process.output { cmd := s!"{objDir}/V{b.name}_top", args := #[], stdin := .null }
      let log := run.stdout
      IO.FS.writeFile s!"{dir}/{b.name}.log" log
      let errors := uvmCount log "UVM_ERROR"
      let fatals := uvmCount log "UVM_FATAL"
      let matched := contains log "SCOREBOARD PASS"
      let good :=
        if expectClean then errors == some 0 && fatals == some 0 && matched
        else fatals == some 0 && (errors.getD 0) > 0 && !matched
      let what := if expectClean then "clean run" else "scoreboard errors"
      if good then
        IO.println s!"[uvm] {b.name}: {what} as expected (UVM_ERROR {errors.getD 0}, scoreboard pass: {matched}) ✓"
      else
        IO.eprintln s!"[uvm] {b.name}: expected {what}; UVM_ERROR {errors}, UVM_FATAL {fatals}, scoreboard pass {matched} — see {dir}/{b.name}.log"
        ok := false
  | _, _ =>
    IO.println "[uvm] SPARKLE_UVM_HOME not set or verilator missing — emit-only"
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"
