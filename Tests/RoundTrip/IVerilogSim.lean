/-
  External-tool round-trip: Sparkle → SystemVerilog → iverilog → vvp.

  Each fixture:
    1. Synthesises a Sparkle circuit to IR via `synthesizeCombinational`.
    2. Emits SystemVerilog through the same optimiser+emitter pair
       that `#synthesizeVerilog` uses (PR #48).
    3. Builds a tiny testbench in Lean, drives the design with known
       inputs, and prints the outputs via `$display`.
    4. Invokes `iverilog -g2012` + `vvp` to compile and run.
    5. Parses the printed output and compares it against the
       reference value computed in Lean.

  The IR → Verilog → IR round-trip test (Tests/RoundTrip/IRVerilogIR.lean)
  only proves Sparkle's own parser agrees with its own emitter — that's
  necessary but not sufficient.  This test proves that an *independent*
  Verilog implementation (Icarus 13.0) also agrees, which is the
  strongest guarantee available without running a real FPGA.

  If `iverilog` is not on PATH the run is skipped — useful for the
  user's local development loop.  CI is expected to install iverilog
  and verify each fixture in turn.

  Run: `lake exe iverilog-roundtrip-test`
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog
open Sparkle.IR.AST

namespace Sparkle.Tests.RoundTrip.IVerilogSim

/-- `verilogOf! <ident>` — synthesise `<ident>` to SystemVerilog *at
    elaboration time* and elaborate to a string literal containing
    the resulting Verilog source.  Bundles the optimisation pass
    (same as `#synthesizeVerilog`).  This pushes the MetaM/Sparkle
    elab work into `lake build`, so the produced `lean_exe` only has
    to do IO (write files, spawn iverilog/vvp) — no MetaM-from-IO
    reducibility headaches. -/
syntax (name := verilogOfCmd) "verilogOf! " ident : term

open Lean Elab Term Meta in
@[term_elab verilogOfCmd]
def elabVerilogOf : TermElab := fun stx _ => do
  match stx with
  | `(verilogOf! $id:ident) => do
    let declName ← Lean.resolveGlobalConstNoOverload id
    let (module, _) ← synthesizeCombinational declName
    let optimized := Sparkle.IR.Optimize.optimizeModule module
    let verilog := toVerilog optimized
    -- Elaborate the captured string as a Lean string literal.
    Lean.Elab.Term.elabTerm
      (Lean.Syntax.mkStrLit verilog) none
  | _ => throwUnsupportedSyntax

/-- Bundle of the module name + pre-elaborated SystemVerilog source
    for one fixture.  Computed at compile time via `verilogOf!`. -/
structure PreSynth where
  modName : String
  verilog : String

end Sparkle.Tests.RoundTrip.IVerilogSim
namespace Sparkle.Tests.RoundTrip.IVerilogSim

-- ============================================================================
-- Fixtures — same circuits as Tests/RoundTrip/IRVerilogIR.lean,
-- duplicated here so each module pulls in only what it needs.
-- ============================================================================

/-- 1-bit D flip-flop. -/
def dff {dom : DomainConfig} (d : Signal dom Bool) : Signal dom Bool :=
  circuit do
    let q ← Signal.reg false
    q <~ d
    return q

/-- 8-bit register. -/
def reg8 {dom : DomainConfig}
    (d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let q ← Signal.reg (0#8)
    q <~ d
    return q

/-- 8-bit counter — `q` increments by 1 every cycle from 0. -/
def counter8 {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let q ← Signal.reg (0#8)
    q <~ q.1 + 1#8
    return q

/-- Pure combinational adder. -/
def add8 {dom : DomainConfig}
    (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a + b

-- ============================================================================
-- Testbench construction
-- ============================================================================

/-- One row of stimulus: (cycle-index, input-name → value).  Inputs are
    referenced by their Sparkle-emitted port name (e.g. `_gen_d`,
    `_gen_a`).  Sequential fixtures get `clk` toggled automatically. -/
structure Stimulus where
  /-- Number of clock cycles to run.  0 for combinational fixtures —
      then only the initial input snapshot is evaluated. -/
  cycles : Nat
  /-- Input bindings per cycle.  `inputs[i]` is the binding to apply
      *before* cycle `i`'s posedge.  `inputs.length` should equal
      `cycles` for sequential fixtures, or `1` for combinational. -/
  inputs : List (List (String × Nat))
  /-- The single output port to probe each cycle. -/
  outputName : String
  /-- Expected output values per cycle.  `expected.length` should equal
      `inputs.length`. -/
  expected : List Nat
  /-- Whether the design needs a clock (sequential vs. combinational). -/
  isSequential : Bool

/-- Generate a SystemVerilog testbench that drives `inputs`, samples
    `outputName`, and prints each sampled value via `$display`.  The
    output format is one decimal value per line so the Lean side can
    parse it with `String.toNat?`. -/
def emitTestbench (modName : String) (st : Stimulus) : String :=
  let inputPorts := st.inputs.head?.getD [] |>.map (·.1)
  let portDecls := inputPorts.map fun n =>
    -- Pessimistically declare every input as 64-bit reg so the
    -- testbench compiles regardless of the design port width.  The
    -- module instance below uses the design's declared width via
    -- `.<port>(<reg>)` connect-by-name; iverilog truncates.
    s!"  reg [63:0] {n};"
  let clkDecl :=
    if st.isSequential then "  reg clk = 0;\n  reg rst = 0;\n" else ""
  let portConns :=
    let dataConns := inputPorts.map fun n => s!".{n}({n})"
    let ctrl := if st.isSequential then [".clk(clk)", ".rst(rst)"] else []
    let outConn := s!".{st.outputName}(out_signal)"
    String.intercalate ", " (dataConns ++ ctrl ++ [outConn])
  -- Build the stimulus body — one `<-` posedge per cycle for
  -- sequential designs; just settle and sample for combinational.
  let stimulusLines :=
    if st.isSequential then
      -- Pulse rst high for one clock to bring registers to a known
      -- state, then drop it before exercising the design.
      let resetSeq := [
        "    rst = 1;",
        "    #1 clk = 1;",
        "    #1 clk = 0;",
        "    rst = 0;"
      ]
      let lines := st.inputs.zipIdx.flatMap fun (binds, i) =>
        let assigns := binds.map fun (n, v) => s!"    {n} = {v};"
        let display := s!"    $display(\"%0d\", out_signal);"
        -- Pulse clock: low, then high; the posedge happens between.
        assigns ++ [
          "    #1 clk = 1;",
          "    #1 clk = 0;",
          display,
        ]
      String.intercalate "\n" (resetSeq ++ lines)
    else
      -- Combinational: just one snapshot.
      let binds := st.inputs.head?.getD []
      let assigns := binds.map fun (n, v) => s!"    {n} = {v};"
      String.intercalate "\n" (assigns ++ [
        "    #1;",
        s!"    $display(\"%0d\", out_signal);"
      ])
  let body := s!"
module tb;
{String.intercalate "\n" portDecls}
{clkDecl}  wire [63:0] out_signal;

  {modName} dut ({portConns});

  initial begin
{stimulusLines}
    $finish;
  end
endmodule
"
  body

-- ============================================================================
-- External-tool runner
-- ============================================================================

/-- Check whether an external command is available via `which`. -/
def toolAvailable (name : String) : IO Bool := do
  let result ← IO.Process.output { cmd := "which", args := #[name] }
  return result.exitCode == 0

structure RunOutcome where
  /-- The vvp stdout captured.  Each printed line is one cycle. -/
  stdout : String
  /-- The vvp exit code.  Non-zero indicates an iverilog / vvp error
      (most often a parse failure of the Sparkle-emitted Verilog). -/
  exitCode : UInt32

/-- Compile `verilog ++ testbench` with iverilog, then run vvp.  Both
    files land in `/tmp` under the fixture name. -/
def runOnce (label : String) (verilog testbench : String) :
    IO RunOutcome := do
  let svPath := s!"/tmp/sparkle_iv_{label}.sv"
  let tbPath := s!"/tmp/sparkle_iv_{label}_tb.sv"
  let vvpPath := s!"/tmp/sparkle_iv_{label}.vvp"
  IO.FS.writeFile svPath verilog
  IO.FS.writeFile tbPath testbench
  -- Compile.
  let ivCompile ← IO.Process.output
    { cmd := "iverilog"
    , args := #["-g2012", "-o", vvpPath, svPath, tbPath] }
  if ivCompile.exitCode != 0 then
    return { stdout := ivCompile.stderr, exitCode := ivCompile.exitCode }
  -- Simulate.
  let vvpRun ← IO.Process.output
    { cmd := "vvp", args := #[vvpPath] }
  return { stdout := vvpRun.stdout, exitCode := vvpRun.exitCode }

/-- Parse vvp's stdout into one decimal value per line.  Anything
    that doesn't parse as a Nat is dropped — vvp prints its own
    banner lines (`VCD info: …`) we don't want to inspect. -/
def parseVvpOutput (s : String) : List Nat :=
  s.splitOn "\n" |>.filterMap fun ln =>
    let trimmed := ln.trim
    String.toNat? trimmed

-- ============================================================================
-- Fixture cases
-- ============================================================================

structure FixtureCase where
  declName : Lean.Name
  label : String
  stimulus : Stimulus

/-- dff: drive `d=1` for 3 cycles, then `d=0` for 3.  Output trails
    by one cycle since the register latches on posedge. -/
private def dffStimulus : Stimulus :=
  { cycles := 6
  , inputs := List.replicate 3 [("_gen_d", 1)] ++
              List.replicate 3 [("_gen_d", 0)]
  , outputName := "out"
  -- After cycle 0 (d=1): q = 1.  Cycle 1: 1.  Cycle 2: 1.  Cycle 3 (d=0): 0.  …
  , expected := [1, 1, 1, 0, 0, 0]
  , isSequential := true }

/-- reg8: drive a few 8-bit values, observe one-cycle delay. -/
private def reg8Stimulus : Stimulus :=
  { cycles := 4
  , inputs := [[("_gen_d", 0x42)],
               [("_gen_d", 0xA5)],
               [("_gen_d", 0xFF)],
               [("_gen_d", 0x00)]]
  , outputName := "out"
  , expected := [0x42, 0xA5, 0xFF, 0x00]
  , isSequential := true }

/-- counter8: just count up. -/
private def counter8Stimulus : Stimulus :=
  { cycles := 5
  , inputs := List.replicate 5 []  -- no inputs
  , outputName := "out"
  , expected := [1, 2, 3, 4, 5]
  , isSequential := true }

/-- add8: combinational, single sample. -/
private def add8Stimulus : Stimulus :=
  { cycles := 0
  , inputs := [[("_gen_a", 10), ("_gen_b", 32)]]
  , outputName := "out"
  , expected := [42]
  , isSequential := false }

def fixtures : List FixtureCase :=
  [ { declName := ``dff,      label := "dff",      stimulus := dffStimulus }
  , { declName := ``reg8,     label := "reg8",     stimulus := reg8Stimulus }
  , { declName := ``counter8, label := "counter8", stimulus := counter8Stimulus }
  , { declName := ``add8,     label := "add8",     stimulus := add8Stimulus }
  ]

-- ============================================================================
-- Pre-synthesised Verilog for each fixture.  `verilogOf!` runs the
-- Sparkle synthesiser at *elaboration* time, so by the time the
-- driver executes we already have plain string literals in hand
-- (no MetaM bootstrap from IO needed).  This sidesteps the
-- "Cannot synthesise runCircuitH: not inlinable" issue that hits
-- a plain `MetaM.toIO synthesizeCombinational` call.
-- ============================================================================

def dffVerilog      : String := verilogOf! dff
def reg8Verilog     : String := verilogOf! reg8
def counter8Verilog : String := verilogOf! counter8
def add8Verilog     : String := verilogOf! add8

/-- The Sparkle emitter prefixes the module name with the Lean
    namespace, so the testbench needs `Tests_RoundTrip_IVerilogSim_dff`
    etc. as the instance type name.  Pull it back out of the
    generated Verilog by reading the first `module …` token. -/
def parseModuleName (verilog : String) : String :=
  let lines := verilog.splitOn "\n"
  let modLine := lines.find? fun l => l.trim.startsWith "module "
  match modLine with
  | none => "unknown"
  | some l =>
    -- "module foo (" → "foo"
    let toks := l.trim.splitOn " "
    if toks.length < 2 then "unknown"
    else
      let raw := toks[1]!
      -- strip trailing "(" if module decl puts it on the same line
      String.mk (raw.toList.reverse.dropWhile (fun c => c == '(' || c == ' ') |>.reverse)

def fixtureVerilogs : List (FixtureCase × String) :=
  [ ({ declName := ``dff,      label := "dff",      stimulus := dffStimulus },      dffVerilog)
  , ({ declName := ``reg8,     label := "reg8",     stimulus := reg8Stimulus },     reg8Verilog)
  , ({ declName := ``counter8, label := "counter8", stimulus := counter8Stimulus }, counter8Verilog)
  , ({ declName := ``add8,     label := "add8",     stimulus := add8Stimulus },     add8Verilog) ]

-- ============================================================================
-- Driver
-- ============================================================================

def main : IO UInt32 := do
  IO.println "=== Sparkle → SystemVerilog → iverilog round-trip ==="
  if !(← toolAvailable "iverilog") then
    IO.println "  SKIP: iverilog not on PATH"
    return 0
  if !(← toolAvailable "vvp") then
    IO.println "  SKIP: vvp not on PATH"
    return 0
  let mut passed := 0
  let mut failed := 0
  for (fc, verilog) in fixtureVerilogs do
    IO.print s!"  {fc.label} ... "
    let modName := parseModuleName verilog
    let tb := emitTestbench modName fc.stimulus
    let outcome ← runOnce fc.label verilog tb
    if outcome.exitCode != 0 then
      IO.println s!"FAIL (iverilog/vvp exit={outcome.exitCode})"
      IO.println "    stderr/stdout:"
      for line in outcome.stdout.splitOn "\n" do
        IO.println s!"    | {line}"
      IO.println "    Verilog under test:"
      for line in verilog.splitOn "\n" do
        IO.println s!"    | {line}"
      IO.println "    Testbench:"
      for line in tb.splitOn "\n" do
        IO.println s!"    | {line}"
      failed := failed + 1
    else
      let got := parseVvpOutput outcome.stdout
      if got == fc.stimulus.expected then
        IO.println "PASS"
        passed := passed + 1
      else
        IO.println s!"FAIL: expected {fc.stimulus.expected}, got {got}"
        IO.println "    Raw vvp stdout:"
        for line in outcome.stdout.splitOn "\n" do
          IO.println s!"    | {line}"
        failed := failed + 1
  IO.println s!"\n=== Results: {passed} passed, {failed} failed ==="
  return if failed == 0 then 0 else 1

end Sparkle.Tests.RoundTrip.IVerilogSim
