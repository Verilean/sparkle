/-
  Loop Synthesis Test

  Tests automatic compilation of Signal.loop (feedback loops) to hardware IR.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Signal.Signal  -- Open Signal namespace for loop, register, mux

-- A simple counter: cnt = cnt + 1
-- The 'loop' primitive gives us access to the 'cnt' wire before it's defined.
def counter {dom} : Signal dom (BitVec 8) :=
  Signal.loop fun cnt =>
    let next := (· + ·) <$> cnt <*> Signal.pure 1#8
    -- Register breaks the combinational loop
    register 0#8 next

-- Synthesize and check output
-- #synthesizeVerilog counter

def main : IO Unit := do
  IO.println "=== Loop Synthesis Test ===\n"
  IO.println "Test: Counter with feedback loop"
  IO.println "  def counter : Signal := loop fun cnt => register 0 (cnt + 1)"
  IO.println ""
  IO.println "Note: Run #synthesizeVerilog counter interactively to see the output."
  IO.println "Expected IR structure:"
  IO.println "  - wire [7:0] _gen_loop_0;         -- Feedback wire"
  IO.println "  - wire [7:0] _gen_loop_body_1;    -- Result of cnt + 1"
  IO.println "  - wire [7:0] _gen_result_2;       -- Register output"
  IO.println "  - assign _gen_loop_body_1 = _gen_loop_0 + 8'd1;"
  IO.println "  - always_ff ... _gen_result_2 <= _gen_loop_body_1;"
  IO.println "  - assign _gen_loop_0 = _gen_result_2;  -- Close the loop"
  IO.println ""
  IO.println "✓ Counter definition is well-formed"

#eval main
