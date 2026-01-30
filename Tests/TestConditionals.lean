import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Conditional Expressions in Synthesis

This test demonstrates limitations with if-then-else in Signal contexts
and shows the correct solution using Signal.mux.

## The Problem

Standard if-then-else expressions get compiled to `ite` which becomes
`Decidable.rec` - a general recursor that the synthesis compiler cannot handle.

## The Solution

Use `Signal.mux` which is specifically designed for hardware multiplexers.
-/

-- ============================================================================
-- RIGHT: Use Signal.mux for hardware multiplexers
-- ============================================================================

def test_mux_RIGHT (cond : Signal Domain Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  Signal.mux cond a b  -- ✓ Works! Generates proper Verilog mux

-- Example: Using mux in a practical circuit - select between add or subtract
def add_or_sub (sel : Signal Domain Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  let sum := (· + ·) <$> a <*> b
  let diff := (· - ·) <$> a <*> b
  Signal.mux sel sum diff

-- ============================================================================
-- WRONG: if-then-else doesn't work in Signal contexts
-- ============================================================================

-- Uncomment to see the errors:

-- def test_if_WRONG (cond : Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
--   if cond then a else b  -- ❌ Error: Cannot instantiate Decidable.rec

-- def test_if_pure_WRONG (x : BitVec 8) : Signal Domain (BitVec 8) :=
--   Signal.pure (if x == 0 then 1 else x + 1)  -- ❌ Error: expected BitVec constant

-- ============================================================================
-- Test Synthesis
-- ============================================================================

#synthesizeVerilog test_mux_RIGHT
#synthesizeVerilog add_or_sub

/-!
## Summary

**Never use if-then-else in Signal contexts. Always use Signal.mux.**

Why:
- if-then-else compiles to Decidable.rec (general recursor)
- General recursors cannot be synthesized to hardware
- This is a fundamental limitation, not a bug

Solution:
- Signal.mux is designed specifically for hardware multiplexers
- It generates proper Verilog ternary operators or case statements
- Type signature: Signal.mux (cond : Signal d Bool) (ifTrue ifFalse : Signal d α) : Signal d α

✓ Always use Signal.mux for conditional hardware!
-/
