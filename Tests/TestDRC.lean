import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# DRC Tests — Registered Output Check

Test that the DRC pass correctly warns for combinational outputs
and passes for registered outputs.
-/

-- Test 1: Combinational output (SHOULD produce DRC warning)
def drc_combo_output (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  (· + ·) <$> a <*> b

#synthesizeVerilog drc_combo_output

-- Test 2: Registered output (should NOT produce DRC warning)
def drc_registered_output (a : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  Signal.register 0#8 a

#synthesizeVerilog drc_registered_output
