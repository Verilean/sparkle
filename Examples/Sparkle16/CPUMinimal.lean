/-
  Minimal CPU demonstrating hierarchical synthesis for Sparkle-16

  This shows how to build a hierarchical design where the top module
  instantiates the ALU as a submodule.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle16

/-!
## Hierarchical CPU with ALU

This demonstrates:
1. ALU as a separate, reusable module
2. Top-level module instantiating ALU hierarchically
3. Automatic Verilog generation for both modules
-/

/-- Simple 2-operation ALU: sel=false → ADD, sel=true → SUB -/
def alu (sel : Signal Domain Bool)
        (a b : Signal Domain (BitVec 16))
        : Signal Domain (BitVec 16) :=
  let addResult := (· + ·) <$> a <*> b
  let subResult := (· - ·) <$> a <*> b
  Signal.mux sel subResult addResult

/-- Simple datapath: runs ALU and stores result in a register -/
def datapath (opSel : Signal Domain Bool)
             (a b : Signal Domain (BitVec 16))
             : Signal Domain (BitVec 16) :=
  -- Compute ALU result (hierarchical instantiation!)
  let aluResult := alu opSel a b
  -- Register the result
  Signal.register 0#16 aluResult

end Sparkle16

-- Synthesize both modules
#synthesizeVerilog Sparkle16.alu
#synthesizeVerilog Sparkle16.datapath

/-!
## Expected Output

This should generate TWO Verilog modules:
1. `Sparkle16_alu` - The ALU submodule
2. `Sparkle16_datapath` - The top module that instantiates the ALU

The datapath module will have an `inst_Sparkle16_alu` instance connecting
the signals hierarchically!
-/
