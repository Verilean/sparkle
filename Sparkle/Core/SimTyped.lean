/-
  sim_typed! — Type-Safe JIT Simulation Wrapper Generator

  Generates typed input/output structures and step/read/reset functions
  for any JIT-compiled module, whether from Verilog (via verilog!) or
  from Signal DSL (via #writeDesign).

  Usage:
    sim_typed! "DomainA" {
      inputs  := [("enable", 1)]
      outputs := [("count", 32), ("count2", 32)]
    }

  This generates DomainA.Sim.SimInput, SimOutput, Simulator with
  typed step/read/reset methods.
-/

import Lean
import Sparkle.Core.JIT

open Lean Elab Command
open Sparkle.Core.JIT

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

private def elabStr' (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .error err => throwError "sim_typed! parse error:\n{err}\n\nSource:\n{s}"
  | .ok stx => elabCommand stx

/-- Generate typed JIT wrappers from a SimSpec -/
def generateSimWrappers (spec : SimSpec) : CommandElabM Unit := do
  let ns := spec.moduleName
  let lb := "{"
  let rb := "}"

  elabStr' s!"namespace {ns}.Sim"
  elabStr' "open Sparkle.Core.JIT"

  -- SimInput
  let inputFields := String.intercalate "\n" <|
    spec.inputs.map fun p => s!"  {p.name} : BitVec {p.width}"
  elabStr' s!"structure SimInput where\n{inputFields}\n  deriving DecidableEq, Repr, BEq, Inhabited"

  -- SimOutput
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

  -- outputPortIndex (for runCDC)
  let outIdxDefs := outputsIndexed.map fun (idx, p) =>
    s!"def outputPortIndex_{p.name} : UInt32 := {idx}"
  for d in outIdxDefs do elabStr' d

  -- inputPortIndex
  let inIdxDefs := inputsIndexed.map fun (idx, p) =>
    s!"def inputPortIndex_{p.name} : UInt32 := {idx}"
  for d in inIdxDefs do elabStr' d

  elabStr' s!"end {ns}.Sim"

