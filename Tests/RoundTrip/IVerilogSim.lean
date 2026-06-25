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
import IP.Net.CRC32
import IP.Net.Ethernet

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

/-- IP.Net.CRC32 byte-feed engine wrapped at a fixed domain so
    `synthesizeCombinational` has a fully-resolved type.  Same body
    as `Sparkle.IP.Net.CRC32.crc32Engine`. -/
def crc32EngineTop
    (byte : Signal defaultDomain (BitVec 8))
    (feed reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 32) :=
  Sparkle.IP.Net.CRC32.crc32Engine byte feed reset

/-- IP.Net.Ethernet rxFramer DMAC output — projection-routed
    single Signal output from a 6-field RxOut record return.
    Exercises the structure-projection path in
    `handleDefinitionUnfold` end-to-end (Sparkle → Verilog →
    iverilog → vvp). -/
def rxFramerDmacTop
    (byte : Signal defaultDomain (BitVec 8))
    (valid sop eop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 48) :=
  (Sparkle.IP.Net.Ethernet.rxFramer byte valid sop eop).dmac

/-- IP.Net.Ethernet rxFramer payloadValid — Bool projection
    from the same record.  Pairs with `rxFramerDmacTop` to
    cover both wide (BitVec 48) and narrow (Bool) projection
    arms of the multi-output split. -/
def rxFramerPayloadValidTop
    (byte : Signal defaultDomain (BitVec 8))
    (valid sop eop : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (Sparkle.IP.Net.Ethernet.rxFramer byte valid sop eop).payloadValid

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

/-- IP.Net.CRC32.crc32EngineTop: byte-feed CRC engine.

    The Stimulus framework's `resetSeq` already pulses `rst=1` for
    one clock and drops it before the user's per-cycle bindings
    run.  The Sparkle-emitted CRC engine treats `rst` as the
    synchronous "load 0xFFFFFFFF" trigger, so by the time the loop's
    cycle-0 binding lands we're already past the reset edge — the
    register reads 0xFFFFFFFF on the first $display.

    Three-cycle stimulus (per-cycle output observed after posedge):
      cycle 0  reset=1, feed=0, byte=0     → reg = 0xFFFFFFFF
                                            (overwrites Stimulus-rst
                                             but holds at the same
                                             value, so still 0xFFFFFFFF)
      cycle 1  reset=0, feed=1, byte=0x31  → reg = 0x7C231048
                                            (one CRC step over '1')
      cycle 2  reset=0, feed=0, byte=0     → reg = 0x7C231048 (hold)

    These per-cycle values match the Lean-side reference
    (`crc32Ref [0x31] ^^^ 0xFFFFFFFF` = 0x7C231048).  The
    Sparkle.Tests.IP.Net.CRC32Test sim test already validates the
    full IEEE 802.3 golden vectors at the Signal layer; this
    fixture proves iverilog accepts the emitted Verilog and
    produces the same per-cycle register trace. -/
private def crc32EngineTopStimulus : Stimulus :=
  { cycles := 3
  , inputs := [ [("_gen_byte", 0),    ("_gen_feed", 0), ("_gen_reset", 1)]
              , [("_gen_byte", 0x31), ("_gen_feed", 1), ("_gen_reset", 0)]
              , [("_gen_byte", 0),    ("_gen_feed", 0), ("_gen_reset", 0)] ]
  , outputName := "out"
  , expected := [4294967295, 2082672712, 2082672712]
  , isSequential := true }

/-- IP.Net.Ethernet rxFramerDmacTop fixture.

    Drives the same 18-byte synthetic frame as the Lean sim test
    (`Tests/IP/Net/EthernetTest.lean:frameBytes`):
      DMAC : AA BB CC DD EE FF
      SMAC : 11 22 33 44 55 66
      EthType : 08 00
      Payload : DE AD BE EF

    SOP pulses on cycle 0; valid stays high for all 18 bytes.
    The `dmac` register accumulates via shiftIn48, so each cycle
    snapshots one more byte; the full DMAC 0xAABBCCDDEEFF is
    visible on cycle 6 and persists for the rest of the frame.
    Expected values were captured from the Lean sim — see
    `Tests/Drivers/EthTraceMain.lean` for the trace utility. -/
private def rxFramerDmacStimulus : Stimulus :=
  let frame : List Nat :=
    [ 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
    , 0x11, 0x22, 0x33, 0x44, 0x55, 0x66
    , 0x08, 0x00
    , 0xDE, 0xAD, 0xBE, 0xEF ]
  let n : Nat := frame.length
  let inputs : List (List (String × Nat)) :=
    frame.zipIdx.map fun (b, i) =>
      [ ("_gen_byte",  b)
      , ("_gen_valid", 1)
      , ("_gen_sop",   if i == 0 then 1 else 0)
      , ("_gen_eop",   if i == n - 1 then 1 else 0) ]
  -- Note: the testbench's reset pulse advances the design state
  -- by one cycle relative to the Lean sim, so iverilog's printed
  -- "cycle k" corresponds to Lean sim cycle k+1.  See
  -- Tests/Drivers/EthTraceMain.lean for the per-cycle Lean trace.
  { cycles := 8
  , inputs := inputs.take 8
  , outputName := "out"
  , expected :=
      [           170                                    -- sim c1: 0xAA
      ,         43707                                    -- sim c2: 0xAABB
      ,      11189196                                    -- sim c3: 0xAABBCC
      ,    2864434397                                    -- sim c4: 0xAABBCCDD
      ,  733295205870                                    -- sim c5: 0xAABBCCDDEE
      , 187723572702975                                  -- sim c6: 0xAABBCCDDEEFF
      , 187723572702975                                  -- sim c7: holds
      , 187723572702975 ]                                -- sim c8: holds
  , isSequential := true }

/-- IP.Net.Ethernet rxFramerPayloadValidTop — Bool output
    covering the BitVec-1 / Bool projection arm.  payloadValid
    latches to 1 on cycle 14 (when the engine first enters the
    sticky PAYLOAD state after consuming all 14 header bytes
    AND valid is high). -/
private def rxFramerPayloadValidStimulus : Stimulus :=
  let frame : List Nat :=
    [ 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
    , 0x11, 0x22, 0x33, 0x44, 0x55, 0x66
    , 0x08, 0x00
    , 0xDE, 0xAD, 0xBE, 0xEF ]
  let n : Nat := frame.length
  let inputs : List (List (String × Nat)) :=
    frame.zipIdx.map fun (b, i) =>
      [ ("_gen_byte",  b)
      , ("_gen_valid", 1)
      , ("_gen_sop",   if i == 0 then 1 else 0)
      , ("_gen_eop",   if i == n - 1 then 1 else 0) ]
  -- iverilog's "cycle k" = Lean sim cycle k+1.  payloadValid
  -- latches to 1 on sim cycle 14, so iverilog sees the rising
  -- edge at its index 13.  Sample 16 cycles → 13 zeros + 3 ones.
  { cycles := 16
  , inputs := inputs.take 16
  , outputName := "out"
  , expected := List.replicate 13 0 ++ [1, 1, 1]
  , isSequential := true }

def fixtures : List FixtureCase :=
  [ { declName := ``dff,              label := "dff",              stimulus := dffStimulus }
  , { declName := ``reg8,             label := "reg8",             stimulus := reg8Stimulus }
  , { declName := ``counter8,         label := "counter8",         stimulus := counter8Stimulus }
  , { declName := ``add8,             label := "add8",             stimulus := add8Stimulus }
  , { declName := ``crc32EngineTop,   label := "crc32EngineTop",   stimulus := crc32EngineTopStimulus }
  , { declName := ``rxFramerDmacTop,         label := "rxFramerDmac",         stimulus := rxFramerDmacStimulus }
  , { declName := ``rxFramerPayloadValidTop, label := "rxFramerPayloadValid", stimulus := rxFramerPayloadValidStimulus }
  ]

-- ============================================================================
-- Pre-synthesised Verilog for each fixture.  `verilogOf!` runs the
-- Sparkle synthesiser at *elaboration* time, so by the time the
-- driver executes we already have plain string literals in hand
-- (no MetaM bootstrap from IO needed).  This sidesteps the
-- "Cannot synthesise runCircuitH: not inlinable" issue that hits
-- a plain `MetaM.toIO synthesizeCombinational` call.
-- ============================================================================

def dffVerilog            : String := verilogOf! dff
def reg8Verilog           : String := verilogOf! reg8
def counter8Verilog       : String := verilogOf! counter8
def add8Verilog           : String := verilogOf! add8
def crc32EngineTopVerilog : String := verilogOf! crc32EngineTop
def rxFramerDmacVerilog   : String := verilogOf! rxFramerDmacTop
def rxFramerPayloadValidVerilog : String := verilogOf! rxFramerPayloadValidTop

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
  [ ({ declName := ``dff,            label := "dff",            stimulus := dffStimulus },            dffVerilog)
  , ({ declName := ``reg8,           label := "reg8",           stimulus := reg8Stimulus },           reg8Verilog)
  , ({ declName := ``counter8,       label := "counter8",       stimulus := counter8Stimulus },       counter8Verilog)
  , ({ declName := ``add8,           label := "add8",           stimulus := add8Stimulus },           add8Verilog)
  , ({ declName := ``crc32EngineTop, label := "crc32EngineTop", stimulus := crc32EngineTopStimulus }, crc32EngineTopVerilog)
  , ({ declName := ``rxFramerDmacTop,         label := "rxFramerDmac",         stimulus := rxFramerDmacStimulus },         rxFramerDmacVerilog)
  , ({ declName := ``rxFramerPayloadValidTop, label := "rxFramerPayloadValid", stimulus := rxFramerPayloadValidStimulus }, rxFramerPayloadValidVerilog) ]

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
