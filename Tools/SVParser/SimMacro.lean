/-
  sim! — One-Step Verilog-to-Typed-Simulator Macro

  Parses Verilog at compile time, generates JIT C++ code, and creates
  typed SimInput/SimOutput/Simulator in one step.

  Usage:

    sim! "
    module my_counter (input clk, input rst, output [7:0] count);
      reg [7:0] count_reg;
      assign count = count_reg;
      always @(posedge clk)
        if (rst) count_reg <= 0;
        else count_reg <= count_reg + 1;
    endmodule
    "

    open my_counter.Sim

    def main : IO Unit := do
      let handle ← JIT.compileAndLoad my_counter.Sim.jitCppPath
      let sim : Simulator := { handle }
      sim.reset
      sim.step { rst := 0 }
      let out ← sim.read
      IO.println s!"count = {out.count}"
      sim.destroy
-/

import Lean
import Tools.SVParser
import Sparkle.Backend.CppSim
import Sparkle.Core.JIT
import Sparkle.Core.SimParallel

open Lean Elab Command
open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Sparkle.Backend.CppSim
open Sparkle.Core.JIT
open Sparkle.IR.AST
open Sparkle.IR.Type

private def elabSimStr (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "sim! parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

/-- Sanitize a Verilog name to a valid Lean identifier -/
private def leanIdent (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Names treated as hidden from the user-facing SimInput.
    MUST match CppSim.lean's `emitSetInputSwitch` behaviour for port indexing:
    CppSim filters `clk` only at the raw JIT level, so user-input raw indices
    are positional over the clk-filtered list. Reset-like names are still
    present as raw inputs but hidden from SimInput for ergonomics. -/
private def isHiddenInput (name : String) : Bool :=
  ["rst", "reset", "RST", "rst_n", "resetn", "RESETN"].any (· == name)
  || name.endsWith "_clk" || name.endsWith "_rst"

/-- The sim! command: Verilog string → typed simulator -/
elab "sim!" src:str : command => do
  let vSrc := src.getString
  -- Parse and lower Verilog
  let design ← match parseAndLowerFlat vSrc with
    | .ok d => pure d
    | .error err => throwError "sim!: parse failed: {err}"
  let m ← match design.modules.head? with
    | some m => pure m
    | none => throwError "sim!: no module found"

  let ns := leanIdent m.name
  let lb := "{"
  let rb := "}"

  -- Generate JIT C++ and write to a deterministic path
  let jitCpp := toCppSimJIT design
  let jitPath := s!".lake/build/gen/sim/{ns}_jit.cpp"
  -- Write the file at elaboration time
  try
    IO.FS.createDirAll ".lake/build/gen/sim"
    IO.FS.writeFile jitPath jitCpp
  catch _ => pure ()  -- ignore write errors during elaboration

  -- Raw JIT inputs are positional after filtering `clk` only (matches
  -- CppSim.emitSetInputSwitch). User-visible inputs additionally hide
  -- reset-like names; we keep the RAW index for each surviving input so
  -- `JIT.setInput rawIdx` lands on the correct switch case.
  let rawInputs := m.inputs.filter (fun p => p.name != "clk")
  let rawIndexed : List (Nat × Sparkle.IR.AST.Port) :=
    (List.range rawInputs.length).zip rawInputs
  let userInputsIndexed : List (Nat × Sparkle.IR.AST.Port) :=
    rawIndexed.filter (fun (_, p) => !isHiddenInput p.name)
  let outputs := m.outputs
  let outputsIdx : List (Nat × Sparkle.IR.AST.Port) :=
    (List.range outputs.length).zip outputs

  elabSimStr s!"namespace {ns}.Sim"
  elabSimStr "open Sparkle.Core.JIT"

  -- jitCppPath: constant for the generated C++ file path
  elabSimStr s!"def jitCppPath : String := \"{jitPath}\""

  -- SimInput
  if userInputsIndexed.isEmpty then
    elabSimStr "structure SimInput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      userInputsIndexed.map fun (_, p) => s!"  {leanIdent p.name} : BitVec {p.ty.bitWidth}"
    elabSimStr s!"structure SimInput where\n{fields}\n  deriving Repr, BEq, Inhabited"

  -- SimOutput
  if outputs.isEmpty then
    elabSimStr "structure SimOutput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      outputs.map fun p => s!"  {leanIdent p.name} : BitVec {p.ty.bitWidth}"
    elabSimStr s!"structure SimOutput where\n{fields}\n  deriving Repr, BEq, Inhabited"

  -- Simulator
  elabSimStr "structure Simulator where\n  handle : JITHandle"

  -- step: uses raw JIT indices (not positional)
  let setCalls := userInputsIndexed.map fun (idx, p) =>
    s!"  JIT.setInput sim.handle {idx} i.{leanIdent p.name}.toNat.toUInt64"
  let stepBody := String.intercalate "\n" setCalls
  elabSimStr s!"def Simulator.step (sim : Simulator) (i : SimInput) : IO Unit := do\n{stepBody}\n  JIT.evalTick sim.handle"

  -- read
  let readLines := outputsIdx.map fun (idx, p) =>
    s!"  let v{idx} ← JIT.getOutput sim.handle {idx}\n  let {leanIdent p.name} := BitVec.ofNat {p.ty.bitWidth} v{idx}.toNat"
  let readBody := String.intercalate "\n" readLines
  let readReturn := String.intercalate ", " <| outputs.map fun p => leanIdent p.name
  elabSimStr s!"def Simulator.read (sim : Simulator) : IO SimOutput := do\n{readBody}\n  pure {lb} {readReturn} {rb}"

  -- reset / destroy
  elabSimStr "def Simulator.reset (sim : Simulator) : IO Unit :=\n  JIT.reset sim.handle"
  elabSimStr "def Simulator.destroy (sim : Simulator) : IO Unit :=\n  JIT.destroy sim.handle"

  -- Per-port raw-index constants (backwards compat)
  for (idx, p) in outputsIdx do
    elabSimStr s!"def outputPortIndex_{leanIdent p.name} : UInt32 := {idx}"
  for (idx, p) in userInputsIndexed do
    elabSimStr s!"def inputPortIndex_{leanIdent p.name} : UInt32 := {idx}"

  -- Name → raw-index lookup tables (used by runSim / runMultiDomainSim)
  let outLookup := if outputs.isEmpty then
      "def outputPortIndexByName : String → Option UInt32 := fun _ => none"
    else
      let cases := String.intercalate "\n" <|
        outputsIdx.map (fun (idx, p) => s!"  | \"{p.name}\" => some {idx}")
      s!"def outputPortIndexByName : String → Option UInt32\n{cases}\n  | _ => none"
  let inLookup := if userInputsIndexed.isEmpty then
      "def inputPortIndexByName : String → Option UInt32 := fun _ => none"
    else
      let cases := String.intercalate "\n" <|
        userInputsIndexed.map (fun (idx, p) => s!"  | \"{p.name}\" => some {idx}")
      s!"def inputPortIndexByName : String → Option UInt32\n{cases}\n  | _ => none"
  elabSimStr outLookup
  elabSimStr inLookup

  -- Name lists (for error messages)
  let outNamesLit := "[" ++ String.intercalate ", " (outputs.map (fun p => s!"\"{p.name}\"")) ++ "]"
  let inNamesLit := "[" ++ String.intercalate ", " (userInputsIndexed.map (fun (_, p) => s!"\"{p.name}\"")) ++ "]"
  elabSimStr s!"def outputPortNames : List String := {outNamesLit}"
  elabSimStr s!"def inputPortNames : List String := {inNamesLit}"

  -- toEndpoint: wraps Simulator for Sparkle.Core.SimParallel.runSim
  let epBody :=
    s!"  {lb} handle := sim.handle, moduleName := \"{ns}\"" ++
    ", lookupOutput := outputPortIndexByName" ++
    ", lookupInput := inputPortIndexByName" ++
    ", outputNames := outputPortNames" ++
    s!", inputNames := inputPortNames {rb}"
  elabSimStr s!"def Simulator.toEndpoint (sim : Simulator) : Sparkle.Core.SimParallel.SimEndpoint :=\n{epBody}"

  -- Convenience: load (compile + create Simulator)
  elabSimStr s!"def load : IO Simulator := do\n  let h ← JIT.compileAndLoad jitCppPath\n  pure {lb} handle := h {rb}"

  elabSimStr s!"end {ns}.Sim"
