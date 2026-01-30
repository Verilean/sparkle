import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# unbundle2 Fundamental Limitation

This test demonstrates why unbundle2 doesn't work in synthesis and why
.fst/.snd methods are the correct solution.

## The Problem

unbundle2 returns: `(Signal α × Signal β)` - a **Lean-level tuple**
The synthesis compiler needs: `Signal (α × β)` - a **Signal-level tuple**

When you write:
  let (a, b) := unbundle2 signal

Lean compiles this pattern match into intermediate forms that the synthesis
compiler cannot track, resulting in "Unbound variable: _uniq.XXX" errors.

## The Solution

Use .fst and .snd methods which operate on Signal-level tuples:
  let a := signal.fst  -- ✓ Works!
  let b := signal.snd  -- ✓ Works!
-/

-- ============================================================================
-- WRONG: This fails with "Unbound variable" error
-- ============================================================================

-- Uncomment to see the error:
-- def test_unbundle2_WRONG (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
--   let (a, b) := unbundle2 input  -- ❌ FAILS: Unbound variable
--   (· + ·) <$> a <*> b

-- ============================================================================
-- RIGHT: Use .fst and .snd methods
-- ============================================================================

def test_projection_RIGHT (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let a := input.fst  -- ✓ Works!
  let b := input.snd  -- ✓ Works!
  (· + ·) <$> a <*> b

-- ============================================================================
-- Practical Example: Half Adder
-- ============================================================================

def halfAdder (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8 × BitVec 8) :=
  let sum := (· ^^^ ·) <$> a <*> b
  let carry := (· &&& ·) <$> a <*> b
  bundle2 sum carry

def useHalfAdder (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  let result := halfAdder a b
  -- Extract using .fst and .snd
  let sum := result.fst
  let carry := result.snd
  (· ||| ·) <$> sum <*> carry

-- Test synthesis
#synthesizeVerilog test_projection_RIGHT
#synthesizeVerilog useHalfAdder

/-!
## Summary

**unbundle2 fundamentally cannot work with pattern matching in synthesis.**

The issue is not a bug that can be fixed - it's a fundamental limitation of how
Lean compiles pattern matches and how the synthesis compiler works.

**Always use .fst/.snd (for 2-tuples) or .proj3_X (for 3+ tuples) instead.**

These methods:
- Work directly on Signal-level tuples
- Are recognized by the synthesis compiler
- Generate correct Verilog slice operations
- Are more readable than Signal.map Prod.fst/snd

✓ This is the recommended and tested solution!
-/
