/-
  Signal-to-IR Synthesis Test

  Tests automatic compilation of Signal primitives (register, mux) to hardware IR.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Signal.Signal  -- Open Signal namespace for register, mux

-- Test 1: Simple Register
-- This should generate a module with:
-- - inputs: clk, rst
-- - output: out
-- - always_ff block for register
def simpleRegister {dom} : Signal dom (BitVec 8) :=
  let input := Signal.pure 42#8
  register 0#8 input

-- Test 2: Register Chain (2 cycles delay)
def registerChain {dom} (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  let delayed1 := register 0#8 input
  let delayed2 := register 0#8 delayed1
  delayed2

-- Test 3: Mux Selection
def muxTest {dom} (sel : Signal dom Bool) (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  mux sel a b

-- Test 4: Combined Register and Mux
-- A simple enable-controlled register
def enabledRegister {dom} (en : Signal dom Bool) (input : Signal dom (BitVec 8))
    : Signal dom (BitVec 8) :=
  let current := register 0#8 input
  mux en input current

-- Interactive synthesis commands (run in Lean REPL or VS Code):
-- #synthesize simpleRegister
-- #synthesizeVerilog simpleRegister

-- #synthesize registerChain
-- #synthesizeVerilog registerChain

-- #synthesize muxTest
-- #synthesizeVerilog muxTest

-- #synthesize enabledRegister
-- #synthesizeVerilog enabledRegister

def main : IO Unit := do
  IO.println "=== Signal Synthesis Test Suite ===\n"

  IO.println "Test 1: Simple Register"
  IO.println "  def simpleRegister : Signal dom (BitVec 8) := register 0#8 (pure 42#8)"
  IO.println "  Expected: Module with clk, rst inputs and always_ff block\n"

  IO.println "Test 2: Register Chain"
  IO.println "  def registerChain (input : Signal dom (BitVec 8)) : Signal dom (BitVec 8)"
  IO.println "  Expected: Two chained registers (2-cycle delay)\n"

  IO.println "Test 3: Mux Selection"
  IO.println "  def muxTest (sel a b : Signal) : Signal := mux sel a b"
  IO.println "  Expected: Ternary operator in Verilog: sel ? a : b\n"

  IO.println "Test 4: Enabled Register"
  IO.println "  def enabledRegister (en input : Signal) : Signal"
  IO.println "  Expected: Register with mux feedback\n"

  IO.println "✓ To run synthesis, use #synthesize or #synthesizeVerilog commands"
  IO.println "✓ Check that generated Verilog has proper always_ff and ternary operators"
  IO.println "\nNote: Interactive synthesis commands (#synthesize, #synthesizeVerilog)"
  IO.println "      require a Lean REPL or VS Code environment."
  IO.println "      This test file verifies that definitions are well-formed."

#eval main
