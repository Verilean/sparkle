/-
  SimTyped — Type-Safe JIT Simulation Wrapper Generator

  Generates typed SimInput/SimOutput/Simulator structures from:
  - Sparkle IR Module (auto-extracted from Verilog or Signal DSL)
  - Manual SimSpec (for custom configurations)

  Usage (automatic from IR):

    -- From Verilog:
    def design ← IO.ofExcept (parseAndLowerFlat myVerilog)
    run_cmd generateSimWrappersFromDesign design "MyModule"

    -- Or manually:
    run_cmd generateSimWrappers {
      moduleName := "MyModule"
      inputs  := [{ name := "enable", width := 1 }]
      outputs := [{ name := "count", width := 8 }]
    }

  Both generate:
    MyModule.Sim.SimInput   — typed input structure
    MyModule.Sim.SimOutput  — typed output structure
    MyModule.Sim.Simulator  — { handle : JITHandle } with step/read/reset
-/

import Lean
import Sparkle.Core.JIT
import Sparkle.IR.AST
import Sparkle.IR.Type

open Lean Elab Command
open Sparkle.Core.JIT
open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Port specification for typed wrapper generation -/
structure PortSpec where
  name : String
  width : Nat
  deriving Repr

/-- Module simulation specification -/
structure SimSpec where
  moduleName : String
  inputs : List PortSpec
  outputs : List PortSpec
  deriving Repr

/-- Names to exclude from SimInput (handled internally by evalTick/reset). -/
private def clockResetNames : List String :=
  ["clk", "clock", "CLK", "rst", "reset", "RST", "rst_n", "resetn", "RESETN"]

/-- Convert an IR Module to a SimSpec, auto-detecting clock/reset ports. -/
def simSpecFromModule (m : Sparkle.IR.AST.Module) (name : String := m.name) : SimSpec :=
  let isClockReset (p : Port) : Bool :=
    clockResetNames.any (· == p.name) || p.name.endsWith "_clk" || p.name.endsWith "_rst"
  { moduleName := name
    inputs := m.inputs.filter (!isClockReset ·) |>.map fun p =>
      { name := p.name, width := p.ty.bitWidth }
    outputs := m.outputs.map fun p =>
      { name := p.name, width := p.ty.bitWidth } }

/-- Convert an IR Design to a SimSpec (uses the first/top module). -/
def simSpecFromDesign (d : Design) (name : String := d.topModule) : SimSpec :=
  match d.modules.head? with
  | some m => simSpecFromModule m name
  | none => { moduleName := name, inputs := [], outputs := [] }

private def elabStr' (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "SimTyped parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

/-- Generate typed JIT wrappers from a SimSpec -/
def generateSimWrappers (spec : SimSpec) : CommandElabM Unit := do
  let ns := spec.moduleName
  let lb := "{"
  let rb := "}"

  elabStr' s!"namespace {ns}.Sim"
  elabStr' "open Sparkle.Core.JIT"

  -- SimInput
  if spec.inputs.isEmpty then
    elabStr' "structure SimInput where\n  deriving DecidableEq, Repr, BEq, Inhabited"
  else
    let inputFields := String.intercalate "\n" <|
      spec.inputs.map fun p => s!"  {p.name} : BitVec {p.width}"
    elabStr' s!"structure SimInput where\n{inputFields}\n  deriving DecidableEq, Repr, BEq, Inhabited"

  -- SimOutput
  if spec.outputs.isEmpty then
    elabStr' "structure SimOutput where\n  deriving DecidableEq, Repr, BEq, Inhabited"
  else
    let outputFields := String.intercalate "\n" <|
      spec.outputs.map fun p => s!"  {p.name} : BitVec {p.width}"
    elabStr' s!"structure SimOutput where\n{outputFields}\n  deriving DecidableEq, Repr, BEq, Inhabited"

  -- Simulator
  elabStr' "structure Simulator where\n  handle : JITHandle"

  -- step
  let inputsIndexed := (List.range spec.inputs.length).zip spec.inputs
  let setCalls := inputsIndexed.map fun (idx, p) =>
    s!"  JIT.setInput sim.handle {idx} i.{p.name}.toNat.toUInt64"
  let stepBody := String.intercalate "\n" setCalls
  elabStr' s!"def Simulator.step (sim : Simulator) (i : SimInput) : IO Unit := do\n{stepBody}\n  JIT.evalTick sim.handle"

  -- read
  let outputsIndexed := (List.range spec.outputs.length).zip spec.outputs
  let readLines := outputsIndexed.map fun (idx, p) =>
    s!"  let v{idx} ← JIT.getOutput sim.handle {idx}\n  let {p.name} := BitVec.ofNat {p.width} v{idx}.toNat"
  let readBody := String.intercalate "\n" readLines
  let readReturn := String.intercalate ", " <| spec.outputs.map (·.name)
  elabStr' s!"def Simulator.read (sim : Simulator) : IO SimOutput := do\n{readBody}\n  pure {lb} {readReturn} {rb}"

  -- reset
  elabStr' "def Simulator.reset (sim : Simulator) : IO Unit :=\n  JIT.reset sim.handle"

  -- destroy
  elabStr' "def Simulator.destroy (sim : Simulator) : IO Unit :=\n  JIT.destroy sim.handle"

  -- Port index constants (for advanced use / runCDC)
  for (idx, p) in outputsIndexed do
    elabStr' s!"def outputPortIndex_{p.name} : UInt32 := {idx}"
  for (idx, p) in inputsIndexed do
    elabStr' s!"def inputPortIndex_{p.name} : UInt32 := {idx}"

  elabStr' s!"end {ns}.Sim"
