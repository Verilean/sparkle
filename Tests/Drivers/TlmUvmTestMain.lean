/-
  UVM testbenches generated from the Lean transaction-level tests, compiled
  and run with Verilator.

  Emission always runs: each testbench is written to
  `.lake/build/gen/uvm/<name>.sv`.  With `SPARKLE_UVM_HOME` pointing at a
  UVM library source tree (the directory that contains `src/uvm_pkg.sv`,
  e.g. a checkout of accellera-official/uvm-core) and `verilator` on PATH,
  each is compiled and run (about a minute each; `SPARKLE_UVM_ONLY=a,b`
  restricts the run).

  Ready/valid benches on Sparkle-emitted designs (`Tlm.Uvm.emit`):
    * FIFO and the 3x+1 stage — clean;
    * the stage that drops data under back-pressure — the scoreboard must
      report errors.
  AXI benches (`Tlm.Uvm.emitAxi`), each first run with the Lean agents; the
  UVM scoreboard checks against what the Lean monitor reported:
    * `axil_regs.sv`, an AXI4-Lite register block in SystemVerilog — clean;
    * the same block built to ignore `wstrb`, against what the correct one
      did — must fail;
    * a Sparkle design under AXI4-Stream port names — clean;
    * with `Examples/SvInterop/fetch.sh` run: verilog-axi `axil_ram` and
      verilog-axis `axis_adapter` — clean.
-/
import Sparkle.Verification.TlmUvm
import Sparkle.Verification.TlmAxiUvm
import Tests.TlmTest
import Tests.SvInteropTest

open Sparkle.Core.Sim
open Sparkle.Verification.Tlm
open Sparkle.Verification.Tlm.Uvm
open Sparkle.Tests.TlmTest
open Sparkle.Tests.SvInteropTest

/-- The count on a `UVM_ERROR :    N` summary line. -/
def uvmCount (log severity : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun line =>
    match line.splitOn s!"{severity} :" with
    | [_, rest] => rest.trim.toNat?
    | _ => none

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- One generated testbench: name, text, the design's sources, and whether
    the run must be clean. -/
structure Case where
  name : String
  tb : String
  sources : List String
  expectClean : Bool

/-- A directed AXI4-Lite sequence for the register block: whole words,
    byte enables, the read-only word, a bad address. -/
def regsSequence : List AxiLiteTxn :=
  [ { write := true, addr := 0x00, data := 0xDEADBEEF, strb := 0xF }
  , { write := true, addr := 0x0C, data := 0x12345678, strb := 0xF }
  , { write := false, addr := 0x00, data := 0, strb := 0xF }
  , { write := true, addr := 0x00, data := 0x0000AA00, strb := 0x2 }
  , { write := false, addr := 0x00, data := 0, strb := 0xF }
  , { write := true, addr := 0x04, data := 0xCAFEF00D, strb := 0xF }
  , { write := true, addr := 0x04, data := 0x000000EE, strb := 0x1 }
  , { write := false, addr := 0x04, data := 0, strb := 0xF }
  , { write := false, addr := 0x10, data := 0, strb := 0xF }
  , { write := true, addr := 0x10, data := 0, strb := 0xF }
  , { write := false, addr := 0x40, data := 0, strb := 0xF } ]

/-- Run an AXI4-Lite sequence on a design with the LEAN agents and return
    what the monitor reported — the expected list for the UVM run. -/
def leanAxil (cfg : Sv.Config) (pfx : String) (seq : List AxiLiteTxn) :
    IO (Sv.Dut × List AxiLiteTxn) := do
  let dut ← Sv.Dut.load cfg
  let b ← Bench.new dut dut.idle (maxCycles := 20000)
  let bus ← AxiLiteBus.fromPrefix dut.pins pfx
  let m ← AxiLiteMaster.new b bus
  let mon ← AxiLiteMonitor.new b bus
  m.run seq
  return (dut, ← mon.items)

/-- Send frames through a design with the Lean agents; the frames received. -/
def leanAxis (cfg : Sv.Config) (sPfx mPfx : String) (frames : List AxiStreamFrame) :
    IO (Sv.Dut × List AxiStreamFrame) := do
  let dut ← Sv.Dut.load cfg
  let b ← Bench.new dut dut.idle (maxCycles := 20000)
  let src ← AxiStreamSource.new b (← AxiStreamBus.fromPrefix dut.pins sPfx)
  let snk ← AxiStreamSink.new b (← AxiStreamBus.fromPrefix dut.pins mPfx) (.every 2)
  for f in frames do src.send f
  let mut got : List AxiStreamFrame := []
  for _ in frames do
    if let some f ← snk.recv then got := got ++ [f]
  return (dut, got)

def absPaths (xs : List String) : IO (List String) :=
  xs.mapM fun (x : String) => do return (← IO.FS.realPath x).toString

/-- The AXI benches: each is first run in Lean, and the UVM testbench is
    generated with the same sequence and what Lean observed. -/
def axiCases : IO (List Case) := do
  if !(← Sv.available) then return []
  let mut cases : List Case := []
  let gen (b : AxiBench) : IO String := IO.ofExcept ((emitAxi b).mapError IO.userError)
  -- 1. the SystemVerilog register block
  let cfg := regsConfig true
  let (dut, expected) ← leanAxil cfg "s_axil" regsSequence
  let bench := { AxiBench.ofDut "axil_regs_tb" cfg dut with axil := [("s_axil", regsSequence, expected)] }
  cases := cases ++ [{ name := "axil_regs_tb", tb := ← gen bench, sources := ← absPaths cfg.sources, expectClean := true }]
  -- 2. the same block ignoring wstrb, against what the correct one did
  let badCfg := regsConfig false
  let badBench := { bench with name := "axil_regs_bug_tb", config := badCfg }
  cases := cases ++ [{ name := "axil_regs_bug_tb", tb := ← gen badBench, sources := ← absPaths badCfg.sources, expectClean := false }]
  Sim.destroy dut
  -- 3. a Sparkle design under AXI4-Stream names
  IO.FS.writeFile wrapperPath (Sparkle.Backend.SvWrapper.emit axisScaleWrapper)
  let sCfg : Sv.Config := { sources := [wrapperPath, ".lake/build/gen/sv/axis_scale_core.sv"], top := "axis_scale" }
  let (sDut, got) ← leanAxis sCfg "s_axis" "m_axis" wordFrames
  if got != wordFrames.map scaleFrame then
    throw (IO.userError "axis_scale: the Lean run did not produce 3x+1 per word")
  let sBench := { AxiBench.ofDut "axis_scale_tb" sCfg sDut with
                  axisIn := [("s_axis", wordFrames)], axisOut := [("m_axis", got)], readyPercent := 60 }
  cases := cases ++ [{ name := "axis_scale_tb", tb := ← gen sBench, sources := ← absPaths sCfg.sources, expectClean := true }]
  Sim.destroy sDut
  -- 4./5. third-party designs, when fetched
  if ← System.FilePath.pathExists s!"{thirdParty}/verilog-axi/rtl/axil_ram.v" then
    let rCfg : Sv.Config := { sources := [s!"{thirdParty}/verilog-axi/rtl/axil_ram.v"], top := "axil_ram"
                              params := [("ADDR_WIDTH", 12)] }
    let seq : List AxiLiteTxn := (List.range 8).flatMap fun k =>
      [ { write := true, addr := 0x40 + 4 * k, data := 0x01010101 * (k + 1), strb := if k % 2 == 0 then 0xF else 0x6 }
      , { write := false, addr := 0x40 + 4 * k, data := 0, strb := 0xF } ]
    let (rDut, rExpected) ← leanAxil rCfg "s_axil" seq
    let rBench := { AxiBench.ofDut "axil_ram_tb" rCfg rDut with axil := [("s_axil", seq, rExpected)] }
    cases := cases ++ [{ name := "axil_ram_tb", tb := ← gen rBench, sources := ← absPaths rCfg.sources, expectClean := true }]
    Sim.destroy rDut
    let aCfg : Sv.Config :=
      { sources := [s!"{thirdParty}/verilog-axis/rtl/axis_adapter.v"], top := "axis_adapter"
        params := [("S_DATA_WIDTH", 8), ("M_DATA_WIDTH", 32), ("S_KEEP_ENABLE", 1), ("M_KEEP_ENABLE", 1)] }
    let (aDut, aGot) ← leanAxis aCfg "s_axis" "m_axis" frames
    let aBench := { AxiBench.ofDut "axis_adapter_tb" aCfg aDut with
                    axisIn := [("s_axis", frames)], axisOut := [("m_axis", aGot)], readyPercent := 50 }
    cases := cases ++ [{ name := "axis_adapter_tb", tb := ← gen aBench, sources := ← absPaths aCfg.sources, expectClean := true }]
    Sim.destroy aDut
  return cases

def main : IO Unit := do
  let dir := ".lake/build/gen/uvm"
  IO.FS.createDirAll dir
  -- ready/valid benches on Sparkle-emitted designs
  let streamCases : List (Bench × String × Bool) :=
    [ (fifoBench, ".lake/build/gen/sim/fifoTop.sv", true)
    , (stageBench "stage_tb" "Sparkle_Tests_TlmTest_stage" 60, ".lake/build/gen/sim/stage.sv", true)
    , (stageBench "drops_tb" "Sparkle_Tests_TlmTest_stageDrops" 50, ".lake/build/gen/sim/stageDrops.sv", false) ]
  let mut ok := true
  let mut cases : List Case := []
  for (b, dutSv, expectClean) in streamCases do
    let tb := emit b
    let shape := contains tb s!"class {b.name}_test extends uvm_test" &&
      contains tb s!"{b.dutModule} dut (" && contains tb "uvm_config_db #(virtual"
    if !shape || !(← System.FilePath.pathExists dutSv) then
      IO.eprintln s!"[uvm] {b.name}: bad emission, or {dutSv} is missing (build Tests.TlmTest)"
      ok := false
    else cases := cases ++ [{ name := b.name, tb, sources := [dutSv], expectClean }]
  -- AXI benches (existing SystemVerilog designs and a wrapped Sparkle design)
  cases := cases ++ (← axiCases)
  -- SPARKLE_UVM_ONLY=name1,name2 restricts the run (each bench takes about
  -- a minute to compile)
  if let some only := ← IO.getEnv "SPARKLE_UVM_ONLY" then
    cases := cases.filter fun c => (only.splitOn ",").contains c.name
  for c in cases do
    IO.FS.writeFile s!"{dir}/{c.name}.sv" c.tb
    IO.println s!"[uvm] emitted {dir}/{c.name}.sv ({c.tb.length} chars)"
  let uvmHome? ← IO.getEnv "SPARKLE_UVM_HOME"
  let haveVerilator := (← IO.Process.output { cmd := "which", args := #["verilator"] }).exitCode == 0
  match uvmHome?, haveVerilator with
  | some uvmHome, true =>
    for c in cases do
      let objDir := s!"{dir}/{c.name}_obj"
      let r ← IO.Process.output {
        cmd := "verilator"
        args := #["--binary", "--timing", "-j", "4", "--Mdir", objDir,
                  "-Wno-fatal", "-Wno-lint", "-Wno-style", "+define+UVM_NO_DPI",
                  s!"+incdir+{uvmHome}/src", s!"{uvmHome}/src/uvm_pkg.sv"]
                ++ c.sources.toArray ++ #[s!"{dir}/{c.name}.sv", "--top-module", s!"{c.name}_top"]
        stdin := .null }
      if r.exitCode != 0 then
        IO.eprintln s!"[uvm] {c.name}: verilator failed:\n{r.stderr.take 3000}"
        ok := false
        continue
      let run ← IO.Process.output { cmd := s!"{objDir}/V{c.name}_top", args := #[], stdin := .null }
      let log := run.stdout
      IO.FS.writeFile s!"{dir}/{c.name}.log" log
      let errors := uvmCount log "UVM_ERROR"
      let fatals := uvmCount log "UVM_FATAL"
      let matched := contains log "SCOREBOARD PASS"
      let good :=
        if c.expectClean then errors == some 0 && fatals == some 0 && matched
        else fatals == some 0 && (errors.getD 0) > 0 && !matched
      let what := if c.expectClean then "clean run" else "scoreboard errors"
      if good then
        IO.println s!"[uvm] {c.name}: {what} as expected (UVM_ERROR {errors.getD 0}, scoreboard pass: {matched}) ✓"
      else
        IO.eprintln s!"[uvm] {c.name}: expected {what}; UVM_ERROR {errors}, UVM_FATAL {fatals}, scoreboard pass {matched} — see {dir}/{c.name}.log"
        ok := false
  | _, _ =>
    IO.println "[uvm] SPARKLE_UVM_HOME not set or verilator missing — emit-only"
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"
