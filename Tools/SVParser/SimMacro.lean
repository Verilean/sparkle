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

/-- Names treated as clock/reset (excluded from SimInput) -/
private def isClkRst (name : String) : Bool :=
  ["clk", "clock", "CLK", "rst", "reset", "RST", "rst_n", "resetn", "RESETN"].any (· == name)
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

  -- Extract ports (exclude clk/rst from inputs)
  let userInputs := m.inputs.filter fun p => !isClkRst p.name
  let outputs := m.outputs

  elabSimStr s!"namespace {ns}.Sim"
  elabSimStr "open Sparkle.Core.JIT"

  -- jitCppPath: constant for the generated C++ file path
  elabSimStr s!"def jitCppPath : String := \"{jitPath}\""

  -- SimInput
  if userInputs.isEmpty then
    elabSimStr "structure SimInput where\n  deriving Repr, BEq, Inhabited"
  else
    let fields := String.intercalate "\n" <|
      userInputs.map fun p => s!"  {leanIdent p.name} : BitVec {p.ty.bitWidth}"
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

  -- step
  let inputsIdx := (List.range userInputs.length).zip userInputs
  let setCalls := inputsIdx.map fun (idx, p) =>
    s!"  JIT.setInput sim.handle {idx} i.{leanIdent p.name}.toNat.toUInt64"
  let stepBody := String.intercalate "\n" setCalls
  elabSimStr s!"def Simulator.step (sim : Simulator) (i : SimInput) : IO Unit := do\n{stepBody}\n  JIT.evalTick sim.handle"

  -- read
  let outputsIdx := (List.range outputs.length).zip outputs
  let readLines := outputsIdx.map fun (idx, p) =>
    s!"  let v{idx} ← JIT.getOutput sim.handle {idx}\n  let {leanIdent p.name} := BitVec.ofNat {p.ty.bitWidth} v{idx}.toNat"
  let readBody := String.intercalate "\n" readLines
  let readReturn := String.intercalate ", " <| outputs.map fun p => leanIdent p.name
  elabSimStr s!"def Simulator.read (sim : Simulator) : IO SimOutput := do\n{readBody}\n  pure {lb} {readReturn} {rb}"

  -- reset / destroy
  elabSimStr "def Simulator.reset (sim : Simulator) : IO Unit :=\n  JIT.reset sim.handle"
  elabSimStr "def Simulator.destroy (sim : Simulator) : IO Unit :=\n  JIT.destroy sim.handle"

  -- Convenience: load (compile + create Simulator)
  elabSimStr s!"def load : IO Simulator := do\n  let h ← JIT.compileAndLoad jitCppPath\n  pure {lb} handle := h {rb}"

  elabSimStr s!"end {ns}.Sim"
