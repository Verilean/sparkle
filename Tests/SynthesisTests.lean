import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Synthesis Unit Tests

Comprehensive tests for all synthesis features.
Run with: lake env lean Tests/SynthesisTests.lean
-/

-- ============================================================================
-- Test 1: Basic Operations
-- ============================================================================

def test_add (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + ·) <$> a <*> b

def test_sub (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· - ·) <$> a <*> b

-- ============================================================================
-- Test 2: Hierarchical Module Instantiation
-- ============================================================================

def test_hierarchical_alu (op : Signal Domain Bool) (a b : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  let addResult := test_add a b
  let subResult := test_sub a b
  Signal.mux op subResult addResult

-- ============================================================================
-- Test 3: Tuple Operations
-- ============================================================================

def test_tuple (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16 × BitVec 16) :=
  bundle2 a b

def test_tuple_extract (ab : Signal Domain (BitVec 16 × BitVec 16)) : Signal Domain (BitVec 16) :=
  Signal.map Prod.fst ab

-- ============================================================================
-- Test 4: Constants (if supported)
-- ============================================================================

def test_add_constant (x : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + (5 : BitVec 16)) <$> x

-- ============================================================================
-- Test 5: Mux Trees
-- ============================================================================

def test_mux2 (sel : Signal Domain Bool)
    (v1 v0 : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  Signal.mux sel v1 v0

-- ============================================================================
-- Run All Tests
-- ============================================================================

-- Test 1: Basic ops
#synthesizeVerilog test_add
#synthesizeVerilog test_sub

-- Test 2: Hierarchical (should instantiate test_add and test_sub)
#synthesizeVerilogDesign test_hierarchical_alu

-- Test 3: Tuples
#synthesizeVerilog test_tuple
#synthesizeVerilog test_tuple_extract

-- Test 4: Constants
-- #synthesizeVerilog test_add_constant  -- May fail if constants not supported yet

-- Test 5: Mux
#synthesizeVerilog test_mux2

-- ============================================================================
-- Test 6: Stateful Components (Registers with Feedback)
-- ============================================================================

-- NOTE: Feedback loops currently don't work with let-bindings due to
-- forward reference issues. This is a known limitation.
-- Workaround: Use manual IR construction (see Examples/Sparkle16/ALU.lean)

-- Simple register without feedback (works)
def test_simple_register (input : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  Signal.register (0 : BitVec 16) input

-- Test 6: Stateful (simple case)
#synthesizeVerilog test_simple_register
