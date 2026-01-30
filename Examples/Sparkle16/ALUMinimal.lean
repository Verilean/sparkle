/-
  Minimal ALU for Sparkle-16

  Simple 2-operation ALU to test hierarchical synthesis.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle16

/-- Simple 2-operation ALU: sel=false → ADD, sel=true → SUB -/
def alu (sel : Signal Domain Bool)
        (a b : Signal Domain (BitVec 16))
        : Signal Domain (BitVec 16) :=
  let addResult := (· + ·) <$> a <*> b
  let subResult := (· - ·) <$> a <*> b
  Signal.mux sel subResult addResult

end Sparkle16

-- Synthesize the ALU to Verilog
#synthesizeVerilog Sparkle16.alu

/-!
## Output

The generated Verilog module has:
- Inputs: sel (1-bit), a (16-bit), b (16-bit)
- Output: out (16-bit)
- Logic: Multiplexer selecting between ADD and SUB based on sel

This ALU can now be used hierarchically in larger designs!
-/
