import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Error Detection Tests

This file tests that the synthesis compiler detects problematic patterns
and provides helpful error messages instead of cryptic "Unbound variable" errors.

These examples are commented out because they should fail with helpful errors.
To test, uncomment one at a time and verify the error message.
-/

-- ============================================================================
-- Test 1: if-then-else should show helpful error about Signal.mux
-- ============================================================================

-- Uncomment to test error message:
-- def test_if_error (cond : Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
--   if cond then a else b  -- Should error: "Use Signal.mux instead"
--
-- #synthesizeVerilog test_if_error

-- ============================================================================
-- Test 2: unbundle2 pattern matching should show helpful error
-- ============================================================================

-- Uncomment to test error message:
-- def test_unbundle2_error (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
--   let (a, b) := unbundle2 input  -- Should error: "Use .fst and .snd instead"
--   (· + ·) <$> a <*> b
--
-- #synthesizeVerilog test_unbundle2_error

-- ============================================================================
-- Test 3: unbundle3 pattern matching should show helpful error
-- ============================================================================

-- Uncomment to test error message:
-- def test_unbundle3_error (input : Signal Domain (BitVec 8 × BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
--   let (a, b, c) := unbundle3 input  -- Should error: "Use .proj3_1, .proj3_2, .proj3_3 instead"
--   (· + · + ·) <$> a <*> b <*> c
--
-- #synthesizeVerilog test_unbundle3_error

-- ============================================================================
-- Working examples (these should compile without errors)
-- ============================================================================

def test_mux_works (cond : Signal Domain Bool) (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  Signal.mux cond a b  -- ✓ Works!

def test_fst_snd_works (input : Signal Domain (BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let a := input.fst  -- ✓ Works!
  let b := input.snd  -- ✓ Works!
  (· + ·) <$> a <*> b

def test_proj3_works (input : Signal Domain (BitVec 8 × BitVec 8 × BitVec 8)) : Signal Domain (BitVec 8) :=
  let a := input.proj3_1  -- ✓ Works!
  let b := input.proj3_2  -- ✓ Works!
  let c := input.proj3_3  -- ✓ Works!
  ((· + ·) <$> ((· + ·) <$> a <*> b) <*> c)

-- Synthesize the working examples to verify they compile
#synthesizeVerilog test_mux_works
#synthesizeVerilog test_fst_snd_works
#synthesizeVerilog test_proj3_works

/-!
## Testing Instructions

To test that error messages work correctly:

1. Uncomment one of the error test cases (test_if_error, test_unbundle2_error, test_unbundle3_error)
2. Run: `lake env lean Tests/TestErrorDetection.lean`
3. Verify that you see a helpful error message (not "Unbound variable")
4. The error message should explain what's wrong and show the correct solution
5. Comment it back out and test the next one

Expected error messages:

**For test_if_error**:
```
if-then-else expressions cannot be synthesized to hardware.

Use Signal.mux instead:
❌ WRONG: if cond then a else b
✓ RIGHT:  Signal.mux cond a b

See Tests/TestConditionals.lean for examples.
```

**For test_unbundle2_error**:
```
unbundle{n} cannot be used with pattern matching in synthesis.

❌ WRONG: let (a, b) := unbundle2 signal
✓ RIGHT:  let a := signal.fst
✓ RIGHT:  let b := signal.snd

Use projection methods instead:
- For 2-tuples: .fst and .snd
- For 3-tuples: .proj3_1, .proj3_2, .proj3_3
- For 4-tuples: .proj4_1 through .proj4_4

See Tests/TestUnbundle2.lean for examples.
```

**For test_unbundle3_error**:
Same as above but triggered by unbundle3 usage.

The working examples at the bottom should always compile successfully.
-/
