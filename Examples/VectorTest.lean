/-
  Vector Type Test Example

  Demonstrates hardware vector synthesis with array indexing.
  Generates: `reg [7:0] mem [0:3];` style Verilog arrays.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Vector
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog
open Sparkle.IR.AST

namespace Sparkle.Examples.VectorTest

/--
  Simple register file read: index into a 4-element vector of 8-bit values.

  Input: vec - Array of 4 x 8-bit values
         idx - 2-bit index (0-3)
  Output: 8-bit value at vec[idx]

  This should generate Verilog like:
    input logic [7:0] vec [3:0];
    input logic [1:0] idx;
    output logic [7:0] out;
    assign out = vec[idx];
-/
def registerFileRead (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    (idx : Signal defaultDomain (BitVec 2)) : Signal defaultDomain (BitVec 8) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

/--
  Constant index: read element 2 from the vector.

  This tests indexing with a constant value.
-/
def constantIndex (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    : Signal defaultDomain (BitVec 8) :=
  vec.map (fun v => v.get ⟨2, by omega⟩)

/--
  16-bit register file: larger elements
-/
def registerFile16 (vec : Signal defaultDomain (HWVector (BitVec 16) 8))
    (idx : Signal defaultDomain (BitVec 3)) : Signal defaultDomain (BitVec 16) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

def main : IO Unit := do
  IO.println "=== Sparkle Vector/Array Synthesis Test ==="
  IO.println ""

  -- Test 1: Register file read
  IO.println "Test 1: 4x8-bit register file read"
  let (regFileModule, design) ← Lean.Elab.Command.liftCoreM <| Lean.withoutModifyingEnv <| Lean.Meta.MetaM.run' <| synthesizeCombinational ``registerFileRead
  IO.println s!"  Module: {regFileModule.name}"
  IO.println s!"  Inputs: {regFileModule.inputs.length}"
  IO.println s!"  Outputs: {regFileModule.outputs.length}"
  IO.println s!"  Wires: {regFileModule.wires.length}"

  -- Check if vec input has array type
  match regFileModule.inputs.find? (fun p => p.name == "_gen_vec_0") with
  | some port =>
    IO.println s!"  Vec port type: {port.ty}"
    match port.ty with
    | .array size elemType =>
      IO.println s!"    ✓ Array detected: {size} elements of {elemType}"
    | _ =>
      IO.println s!"    ✗ Expected array type, got: {port.ty}"
  | none =>
    IO.println "    ✗ Vec port not found"

  let verilog := toVerilog regFileModule
  IO.println ""
  IO.println "Generated Verilog:"
  IO.println verilog

  -- Write to file
  writeVerilogFile regFileModule "/tmp/register_file_read.v"
  IO.println ""

  -- Test 2: Constant index
  IO.println "Test 2: Constant index access"
  let (constIdxModule, _) ← Lean.Elab.Command.liftCoreM <| Lean.withoutModifyingEnv <| Lean.Meta.MetaM.run' <| synthesizeCombinational ``constantIndex
  IO.println s!"  Module: {constIdxModule.name}"
  let verilog2 := toVerilog constIdxModule
  writeVerilogFile constIdxModule "/tmp/constant_index.v"
  IO.println ""

  -- Test 3: 16-bit register file
  IO.println "Test 3: 8x16-bit register file"
  let (regFile16Module, _) ← Lean.Elab.Command.liftCoreM <| Lean.withoutModifyingEnv <| Lean.Meta.MetaM.run' <| synthesizeCombinational ``registerFile16
  IO.println s!"  Module: {regFile16Module.name}"

  match regFile16Module.inputs.find? (fun p => p.name == "_gen_vec_0") with
  | some port =>
    IO.println s!"  Vec port type: {port.ty}"
  | none =>
    IO.println "  Vec port not found"

  writeVerilogFile regFile16Module "/tmp/register_file_16.v"

  IO.println ""
  IO.println "✓ All tests completed!"
  IO.println "Generated files:"
  IO.println "  - /tmp/register_file_read.v"
  IO.println "  - /tmp/constant_index.v"
  IO.println "  - /tmp/register_file_16.v"

end Sparkle.Examples.VectorTest
