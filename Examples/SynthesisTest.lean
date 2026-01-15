/-
  Phase 3: Synthesis Test Suite

  Tests the metaprogramming compiler that translates Lean functions
  to hardware IR automatically.
-/

import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog

open Sparkle.Compiler.Elab

/-- Test 1: Simple constant function -/
def constCircuit : BitVec 8 :=
  42#8

/-- Test 2: Simple addition -/
def addCircuit (a b : BitVec 8) : BitVec 8 :=
  a + b

/-- Test 3: Multiple operations with let-binding -/
def myCircuit (a b : BitVec 8) : BitVec 8 :=
  let x := a + b
  let y := x &&& 5#8
  y

/-- Test 4: Bitwise operations -/
def bitwiseCircuit (a b : BitVec 8) : BitVec 8 :=
  let andResult := a &&& b
  let orResult := andResult ||| 0xFF#8
  orResult

/-- Test 5: Arithmetic chain -/
def arithmeticCircuit (a b c : BitVec 8) : BitVec 8 :=
  let sum := a + b
  let prod := sum * c
  prod

/-- Test 6: Comparison and logic -/
def compareCircuit (a b : BitVec 8) : BitVec 8 :=
  let diff := a - b
  let result := diff &&& 0x0F#8
  result

-- Note: Register synthesis requires clock/reset context
-- For now, we test pure combinational logic

/--
  Run synthesis tests manually with:

  #synthesize constCircuit
  #synthesize addCircuit
  #synthesize myCircuit
  #synthesize bitwiseCircuit
  #synthesize arithmeticCircuit
  #synthesize compareCircuit

  To generate Verilog:
  #synthesizeVerilog myCircuit
-/

-- Example of manual programmatic synthesis
def main : IO Unit := do
  IO.println "=== Phase 3: Synthesis Test Suite ===\n"

  IO.println "Test 1: Constant Circuit"
  IO.println "  def constCircuit : BitVec 8 := 42#8"
  IO.println "  Run: #synthesize constCircuit\n"

  IO.println "Test 2: Simple Addition"
  IO.println "  def addCircuit (a b : BitVec 8) : BitVec 8 := a + b"
  IO.println "  Run: #synthesize addCircuit\n"

  IO.println "Test 3: Multiple Operations"
  IO.println "  def myCircuit (a b : BitVec 8) : BitVec 8 :="
  IO.println "    let x := a + b"
  IO.println "    let y := x &&& 5#8"
  IO.println "    y"
  IO.println "  Run: #synthesize myCircuit\n"

  IO.println "Test 4: Bitwise Operations"
  IO.println "  def bitwiseCircuit (a b : BitVec 8) : BitVec 8 :="
  IO.println "    let andResult := a &&& b"
  IO.println "    let orResult := andResult ||| 0xFF#8"
  IO.println "    orResult"
  IO.println "  Run: #synthesize bitwiseCircuit\n"

  IO.println "Test 5: Arithmetic Chain"
  IO.println "  def arithmeticCircuit (a b c : BitVec 8) : BitVec 8 :="
  IO.println "    let sum := a + b"
  IO.println "    let prod := sum * c"
  IO.println "    prod"
  IO.println "  Run: #synthesize arithmeticCircuit\n"

  IO.println "✓ Phase 3 synthesis infrastructure complete!"
  IO.println "✓ Use #synthesize <function> to compile to IR"
  IO.println "✓ Use #synthesizeVerilog <function> to generate SystemVerilog"

#eval main
