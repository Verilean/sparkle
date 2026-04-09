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
import Sparkle.Core.SimParallel
import Sparkle.IR.AST
import Sparkle.IR.Type

open Lean Elab Command
open Sparkle.Core.JIT
open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Port specification for typed wrapper generation.
    `rawIndex` is the position in the raw JIT set_input/get_output switch
    (which filters `clk` only). The typed layer hides reset-like names from
    `SimInput` but keeps the raw index so `JIT.setInput rawIndex` always
    lands on the right case. -/
structure PortSpec where
  name : String
  width : Nat
  rawIndex : Nat := 0
  deriving Repr

/-- Module simulation specification -/
structure SimSpec where
  moduleName : String
  inputs : List PortSpec
  outputs : List PortSpec
  deriving Repr

/-- Names to hide from the user-visible SimInput surface (reset-like signals).
    Clock is ALWAYS filtered at the raw JIT level (see Sparkle.Backend.CppSim
    `emitSetInputSwitch`), so typed indices for `clk` would never be reachable.
    Reset-like names are still present at raw JIT index level; we hide them
    from `SimInput` for ergonomics but keep the raw index intact, so
    `setInput` calls use the exact same index as the generated C++ switch. -/
private def resetLikeNames : List String :=
  ["rst", "reset", "RST", "rst_n", "resetn", "RESETN"]

/-- True if this port should be hidden from the user-facing SimInput.
    Hides `clk` (same as raw JIT filter) and reset-like names. -/
private def isHiddenInput (name : String) : Bool :=
  name == "clk" || resetLikeNames.any (· == name) || name.endsWith "_clk" || name.endsWith "_rst"

/-- Convert an IR Module to a SimSpec. Hides clock/reset ports from the
    user-facing surface but preserves their raw-JIT index for the
    surviving ports (so `setInput rawIdx` still lands correctly).

    Raw JIT input indices match `emitSetInputSwitch` in CppSim.lean, which
    filters `clk` only. Outputs are indexed directly in declaration order. -/
def simSpecFromModule (m : Sparkle.IR.AST.Module) (name : String := m.name) : SimSpec :=
  -- Compute raw JIT input indices: filter clk, then assign positional index.
  let rawInputs := m.inputs.filter (fun p => p.name != "clk")
  let rawIndexed := (List.range rawInputs.length).zip rawInputs
  let userInputs := rawIndexed.filterMap fun (idx, p) =>
    if isHiddenInput p.name then none
    else some { name := p.name, width := p.ty.bitWidth, rawIndex := idx : PortSpec }
  { moduleName := name
    inputs := userInputs
    outputs := (List.range m.outputs.length).zip m.outputs |>.map fun (idx, p) =>
      { name := p.name, width := p.ty.bitWidth, rawIndex := idx : PortSpec } }

/-- Convert an IR Design to a SimSpec (uses the first/top module). -/
def simSpecFromDesign (d : Design) (name : String := d.topModule) : SimSpec :=
  match d.modules.head? with
  | some m => simSpecFromModule m name
  | none => { moduleName := name, inputs := [], outputs := [] }

private def elabStr' (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "SimTyped parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

/-- Normalize rawIndex: if all PortSpecs have the default rawIndex=0 (meaning
    the user didn't set it explicitly), fall back to positional ordering. -/
private def normalizeRawIndex (ps : List PortSpec) : List PortSpec :=
  if ps.all (·.rawIndex == 0) then
    (List.range ps.length).zip ps |>.map fun (i, p) => { p with rawIndex := i }
  else ps

/-- Generate typed JIT wrappers from a SimSpec -/
def generateSimWrappers (spec0 : SimSpec) : CommandElabM Unit := do
  let spec : SimSpec := { spec0 with
    inputs := normalizeRawIndex spec0.inputs
    outputs := normalizeRawIndex spec0.outputs }
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

  -- step: uses rawIndex (raw JIT case number), NOT positional typed index
  let setCalls := spec.inputs.map fun p =>
    s!"  JIT.setInput sim.handle {p.rawIndex} i.{p.name}.toNat.toUInt64"
  let stepBody := String.intercalate "\n" setCalls
  elabStr' s!"def Simulator.step (sim : Simulator) (i : SimInput) : IO Unit := do\n{stepBody}\n  JIT.evalTick sim.handle"

  -- read: outputs use their rawIndex (positional in declaration order)
  let readLines := spec.outputs.map fun p =>
    s!"  let v{p.name} ← JIT.getOutput sim.handle {p.rawIndex}\n  let {p.name} := BitVec.ofNat {p.width} v{p.name}.toNat"
  let readBody := String.intercalate "\n" readLines
  let readReturn := String.intercalate ", " <| spec.outputs.map (·.name)
  elabStr' s!"def Simulator.read (sim : Simulator) : IO SimOutput := do\n{readBody}\n  pure {lb} {readReturn} {rb}"

  -- reset
  elabStr' "def Simulator.reset (sim : Simulator) : IO Unit :=\n  JIT.reset sim.handle"

  -- destroy
  elabStr' "def Simulator.destroy (sim : Simulator) : IO Unit :=\n  JIT.destroy sim.handle"

  -- Per-port index constants (still handy for direct JIT.runCDC calls)
  for p in spec.outputs do
    elabStr' s!"def outputPortIndex_{p.name} : UInt32 := {p.rawIndex}"
  for p in spec.inputs do
    elabStr' s!"def inputPortIndex_{p.name} : UInt32 := {p.rawIndex}"

  -- Name → raw-index lookup tables (used by runSim / runMultiDomainSim)
  let outLookup := if spec.outputs.isEmpty then
      "def outputPortIndexByName : String → Option UInt32 := fun _ => none"
    else
      let cases := String.intercalate "\n" <|
        spec.outputs.map (fun p => s!"  | \"{p.name}\" => some {p.rawIndex}")
      s!"def outputPortIndexByName : String → Option UInt32\n{cases}\n  | _ => none"
  let inLookup := if spec.inputs.isEmpty then
      "def inputPortIndexByName : String → Option UInt32 := fun _ => none"
    else
      let cases := String.intercalate "\n" <|
        spec.inputs.map (fun p => s!"  | \"{p.name}\" => some {p.rawIndex}")
      s!"def inputPortIndexByName : String → Option UInt32\n{cases}\n  | _ => none"
  elabStr' outLookup
  elabStr' inLookup

  -- Name lists for error messages
  let outNamesLit := "[" ++ String.intercalate ", " (spec.outputs.map (fun p => s!"\"{p.name}\"")) ++ "]"
  let inNamesLit := "[" ++ String.intercalate ", " (spec.inputs.map (fun p => s!"\"{p.name}\"")) ++ "]"
  elabStr' s!"def outputPortNames : List String := {outNamesLit}"
  elabStr' s!"def inputPortNames : List String := {inNamesLit}"

  -- toEndpoint: build a SimEndpoint for Sparkle.Core.SimParallel.runSim
  let epBody :=
    s!"  {lb} handle := sim.handle, moduleName := \"{ns}\"" ++
    ", lookupOutput := outputPortIndexByName" ++
    ", lookupInput := inputPortIndexByName" ++
    ", outputNames := outputPortNames" ++
    s!", inputNames := inputPortNames {rb}"
  elabStr' s!"def Simulator.toEndpoint (sim : Simulator) : Sparkle.Core.SimParallel.SimEndpoint :=\n{epBody}"

  elabStr' s!"end {ns}.Sim"
