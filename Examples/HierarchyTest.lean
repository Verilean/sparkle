import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- Sub-module: Half adder
def halfAdder (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8 × BitVec 8) :=
  let sum := (· ^^^ ·) <$> a <*> b
  let carry := (· &&& ·) <$> a <*> b
  bundle2 sum carry

-- Top-level module that instantiates halfAdder twice
--
-- IMPORTANT: Tuple Extraction Pattern
-- ====================================
-- Use Signal.map Prod.fst/snd for extracting tuple components:
--   ✓ let sum1 := Signal.map Prod.fst res1
--   ✓ let carry1 := Signal.map Prod.snd res1
--
-- DO NOT use pattern matching on unbundle2:
--   ✗ let (sum1, carry1) := unbundle2 res1
--
-- Why unbundle2 pattern matching doesn't work:
-- -------------------------------------------
-- unbundle2 returns a Lean-level tuple: (Signal α × Signal β)
-- When you write: let (a, b) := unbundle2 x
-- Lean compiles this pattern match into:
--   1. A custom match function (e.g., fullAdder.match_1)
--   2. Nested lambda abstractions that destructure the tuple
--   3. Complex reduced expressions where fvars are deeply embedded
--
-- By the time the Sparkle compiler sees the code, the pattern match has been
-- compiled away into deeply nested Signal operations with references to fvars
-- that are no longer accessible at the let-binding level. The compiler cannot
-- intercept and properly wire these pattern variables.
--
-- In contrast, Signal.map Prod.fst/snd works because:
--   - It stays at the Signal DSL level
--   - No Lean-level pattern matching is involved
--   - The compiler has explicit handlers that recognize these patterns
--   - The generated Verilog correctly creates slice wires for tuple components
--
def fullAdder (a b cin : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8 × BitVec 8) :=
  let res1 := halfAdder a b
  let sum1 := Signal.map Prod.fst res1
  let carry1 := Signal.map Prod.snd res1
  let res2 := halfAdder sum1 cin
  let sum2 := Signal.map Prod.fst res2
  let carry2 := Signal.map Prod.snd res2
  let carryOut := (· ||| ·) <$> carry1 <*> carry2
  bundle2 sum2 carryOut

-- Sub-module: 8-bit XOR gate
def xor8 (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  (· ^^^ ·) <$> a <*> b

-- Sub-module: 8-bit AND gate
def and8 (a b : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  (· &&& ·) <$> a <*> b

-- Top-level: XOR then AND
def xorThenAnd (a b c : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  let xorResult := xor8 a b
  and8 xorResult c

-- Test individual module synthesis
#synthesizeVerilog halfAdder

-- Test xor8
#synthesizeVerilog xor8

-- Test hierarchical synthesis with simple example
#synthesizeVerilogDesign xorThenAnd

-- Test hierarchical synthesis with halfAdder/fullAdder (tuple extraction working!)
#synthesizeVerilogDesign fullAdder
