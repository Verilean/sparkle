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
-- Use .fst/.snd methods for extracting tuple components:
--   ✓ let sum1 := res1.fst
--   ✓ let carry1 := res1.snd
--
-- DO NOT use pattern matching on unbundle2:
--   ✗ let (sum1, carry1) := unbundle2 res1
--
-- Why pattern matching doesn't work:
-- Lean compiles pattern matches into match functions that get reduced away
-- during elaboration, causing "unbound variable" errors in the synthesis context.
--
-- Solution: Use readable projection methods (.fst, .snd, .proj3_1, etc.)
-- These are much more readable than the old Signal.map Prod.fst/snd style!
--
def fullAdder (a b cin : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8 × BitVec 8) :=
  let res1 := halfAdder a b
  let sum1 := res1.fst       -- ✨ Readable!
  let carry1 := res1.snd     -- ✨ Readable!
  let res2 := halfAdder sum1 cin
  let sum2 := res2.fst
  let carry2 := res2.snd
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
