import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Test Circuit Definitions

Hardware circuit definitions used for Verilog generation testing.
-/

-- Combinational circuits (no registers, no state)
def test_add (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + ·) <$> a <*> b

def test_sub (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· - ·) <$> a <*> b

def test_and (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· &&& ·) <$> a <*> b

def test_mux (sel : Signal Domain Bool) (a b : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  Signal.mux sel a b

def test_hierarchical_alu (op : Signal Domain Bool) (a b : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  let addResult := test_add a b
  let subResult := test_sub a b
  Signal.mux op subResult addResult

-- Sequential circuits (with flip-flops/registers)
def test_flipflop (input : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  Signal.register (0 : BitVec 16) input
