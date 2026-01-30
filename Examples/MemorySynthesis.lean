/-
  Memory Verilog Synthesis Example

  Demonstrates Verilog generation for memory primitives.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog
open Lean

/-!
## Simple RAM Module for Synthesis

This example synthesizes a simple 256-byte RAM to Verilog.
-/

def simpleRAM
    (writeAddr : Signal defaultDomain (BitVec 8))
    (writeData : Signal defaultDomain (BitVec 8))
    (writeEnable : Signal defaultDomain Bool)
    (readAddr : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.memory writeAddr writeData writeEnable readAddr

def main : IO Unit := do
  IO.println "=== Memory Verilog Synthesis ==="
  IO.println ""

  -- Initialize Lean environment
  initSearchPath (← findSysroot)

  let env ← importModules
    #[{module := `Sparkle.Compiler.Elab}]
    {}
    (trustLevel := 1024)

  let coreCtx : Core.Context := {
    fileName := "<memory_synthesis>"
    fileMap := default
  }
  let coreState : Core.State := { env := env }

  try
    let ((module, _design), _) ← Meta.MetaM.toIO
      (synthesizeCombinational `simpleRAM)
      coreCtx
      coreState

    IO.println "✓ Synthesis successful!"
    IO.println ""
    IO.println "Generated Verilog:"
    IO.println "=================="
    IO.println (toVerilog module)
    IO.println ""

    IO.println "Module structure:"
    IO.println s!"  Inputs: {module.inputs.length}"
    for p in module.inputs do
      IO.println s!"    - {p.name}: {p.ty}"
    IO.println s!"  Outputs: {module.outputs.length}"
    for p in module.outputs do
      IO.println s!"    - {p.name}: {p.ty}"
    IO.println s!"  Internal wires: {module.wires.length}"
    IO.println s!"  Statements: {module.body.length}"

    -- Check if memory statement was generated
    let hasMemory := module.body.any fun s =>
      match s with
      | .memory .. => true
      | _ => false

    IO.println ""
    if hasMemory then
      IO.println "✓ Memory primitive successfully synthesized!"
    else
      IO.println "✗ Warning: No memory statement found in IR"

  catch e =>
    IO.println s!"✗ Synthesis failed: {e}"
