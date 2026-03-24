/-
  Compiler Extension Tests

  Tests for new compiler features needed by the RV32 Signal DSL rewrite:
  - Bit slice (BitVec.extractLsb')
  - Concatenation (BitVec.append / HAppend)
  - Shift operations (<<<, >>>, arithmetic shift right)
  - Negation (-x)
  - Bitwise NOT (~~~x)
  - Register with enable (Signal.registerWithEnable)
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- ============================================================================
-- Test 1: Shift Left (<<<)
-- ============================================================================

def test_shl (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· <<< ·) <$> a <*> b

#synthesizeVerilog test_shl

-- ============================================================================
-- Test 2: Logical Shift Right (>>>)
-- ============================================================================

def test_shr (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· >>> ·) <$> a <*> b

#synthesizeVerilog test_shr

-- ============================================================================
-- Test 3: Negation (-x)
-- ============================================================================

def test_neg (a : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (- ·) <$> a

#synthesizeVerilog test_neg

-- ============================================================================
-- Test 4: Bitwise NOT (~~~x)
-- ============================================================================

def test_not (a : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (~~~ ·) <$> a

#synthesizeVerilog test_not

-- ============================================================================
-- Test 5: Bit Slice via extractLsb' in Signal.map
-- Extracts bits [7:0] from a 16-bit signal
-- ============================================================================

def test_slice_map (a : Signal Domain (BitVec 16)) : Signal Domain (BitVec 8) :=
  a.map (BitVec.extractLsb' 0 8 ·)

#synthesizeVerilog test_slice_map

-- ============================================================================
-- Test 6: Bit Slice - extract upper bits [15:8]
-- ============================================================================

def test_slice_upper (a : Signal Domain (BitVec 16)) : Signal Domain (BitVec 8) :=
  a.map (BitVec.extractLsb' 8 8 ·)

#synthesizeVerilog test_slice_upper

-- ============================================================================
-- Test 7: Concatenation via Signal.ap
-- Concatenates two 8-bit signals into a 16-bit signal
-- ============================================================================

def test_concat (hi lo : Signal Domain (BitVec 8)) : Signal Domain (BitVec 16) :=
  hi ++ lo

#synthesizeVerilog test_concat

-- ============================================================================
-- Test 8: Register with enable
-- ============================================================================

def test_reg_enable (en : Signal Domain Bool) (input : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  Signal.registerWithEnable (0 : BitVec 16) en input

#synthesizeVerilog test_reg_enable

-- ============================================================================
-- Test 9: Combined - extract opcode field (RV32 decoder pattern)
-- ============================================================================

def test_extract_opcode (inst : Signal Domain (BitVec 32))
    : Signal Domain (BitVec 7) :=
  inst.map (BitVec.extractLsb' 0 7 ·)  -- opcode = bits [6:0]

#synthesizeVerilog test_extract_opcode

-- ============================================================================
-- Test 10: Multiple slices (decoder pattern)
-- ============================================================================

def test_decoder_fields (inst : Signal Domain (BitVec 32))
    : Signal Domain (BitVec 7 × BitVec 5) :=
  let opcode := inst.map (BitVec.extractLsb' 0 7 ·)   -- bits [6:0]
  let rd := inst.map (BitVec.extractLsb' 7 5 ·)        -- bits [11:7]
  bundle2 opcode rd

#synthesizeVerilog test_decoder_fields
