import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Tuple Projection Test

Demonstrates readable tuple projection using .fst, .snd, and .projN_M methods
instead of verbose `Signal.map Prod.fst`.
-/

-- ============================================================================
-- Example: 2-Tuple Projection (Much More Readable!)
-- ============================================================================

def example_2tuple_fst (ab : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  -- OLD WAY (hard to read):
  -- Signal.map Prod.fst ab

  -- NEW WAY (readable):
  ab.fst

def example_2tuple_snd (ab : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  ab.snd

-- ============================================================================
-- Example: 3-Tuple Projection
-- ============================================================================

def example_3tuple_first (abc : Signal Domain (BitVec 8 × BitVec 8 × BitVec 8))
    : Signal Domain (BitVec 8) :=
  abc.proj3_1

def example_3tuple_second (abc : Signal Domain (BitVec 8 × BitVec 8 × BitVec 8))
    : Signal Domain (BitVec 8) :=
  abc.proj3_2

def example_3tuple_third (abc : Signal Domain (BitVec 8 × BitVec 8 × BitVec 8))
    : Signal Domain (BitVec 8) :=
  abc.proj3_3

-- ============================================================================
-- Example: 4-Tuple Projection
-- ============================================================================

def example_4tuple_third (abcd : Signal Domain (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8))
    : Signal Domain (BitVec 8) :=
  abcd.proj4_3

-- ============================================================================
-- Working Example: Using .fst and .snd in real hardware
-- ============================================================================

def halfAdder (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8 × BitVec 8) :=
  let sum := (· ^^^ ·) <$> a <*> b
  let carry := (· &&& ·) <$> a <*> b
  bundle2 sum carry

def addThreeNumbers (a b c : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  let ab := halfAdder a b
  let sum_ab := ab.fst      -- ✨ Readable projection!
  let carry_ab := ab.snd    -- ✨ Readable projection!

  let abc := halfAdder sum_ab c
  let final_sum := abc.fst

  final_sum

-- Test synthesis
#synthesizeVerilog example_2tuple_fst
#synthesizeVerilog addThreeNumbers

/-!
## Summary

The problem with unbundle2 wasn't its definition - it's that Lean pattern matching
doesn't work in the synthesis context.

### Solutions:

1. **For 2-tuples:** Use `.fst` and `.snd` methods
   ```lean
   let a := signal.fst  -- Instead of: Signal.map Prod.fst signal
   let b := signal.snd  -- Instead of: Signal.map Prod.snd signal
   ```

2. **For 3-tuples:** Use `.proj3_1`, `.proj3_2`, `.proj3_3` methods
   ```lean
   let a := signal.proj3_1
   let b := signal.proj3_2
   let c := signal.proj3_3
   ```

3. **For 4-tuples:** Use `.proj4_1` through `.proj4_4` methods

4. **For 5-8 tuples:** Use `unbundle5` through `unbundle8` and tuple projections
   ```lean
   let abcde := unbundle5 signal
   let a := abcde.1
   let b := abcde.2.1
   -- etc.
   ```

Much more readable than `Signal.map Prod.fst`! ✨
-/
