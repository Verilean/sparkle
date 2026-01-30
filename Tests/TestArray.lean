/-
  Array/Vector Unit Tests

  Tests for hardware vector types and HWType operations.
-/

import Sparkle
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Vector
open Sparkle.IR.Type
open LSpec

namespace Sparkle.Test.Array

/--
  Simple register file read: index into a 4-element vector of 8-bit values.
-/
def registerFileRead (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    (idx : Signal defaultDomain (BitVec 2)) : Signal defaultDomain (BitVec 8) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

/--
  Constant index access: read element 2 from a 4-element vector.
-/
def constantIndex (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    : Signal defaultDomain (BitVec 8) :=
  vec.map (fun v => v.get ⟨2, by omega⟩)

/--
  16-bit register file: 8 elements of 16 bits each
-/
def registerFile16 (vec : Signal defaultDomain (HWVector (BitVec 16) 8))
    (idx : Signal defaultDomain (BitVec 3)) : Signal defaultDomain (BitVec 16) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

/--
  Simple 2-element array of 4-bit values
-/
def smallArray (vec : Signal defaultDomain (HWVector (BitVec 4) 2))
    (idx : Signal defaultDomain (BitVec 1)) : Signal defaultDomain (BitVec 4) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

/-! ## HWVector Tests -/

def test_hwvector_operations : IO TestSeq := do
  -- Create a simple vector
  let vec := HWVector.ofList [1#8, 2#8, 3#8, 4#8]

  pure (
    test "HWVector.get element 0" (vec.get ⟨0, by decide⟩ == 1#8) $
    test "HWVector.get element 2" (vec.get ⟨2, by decide⟩ == 3#8) $
    test "HWVector.get element 3" (vec.get ⟨3, by decide⟩ == 4#8)
  )

def test_hwvector_set : IO TestSeq := do
  let vec := HWVector.ofList [1#8, 2#8, 3#8, 4#8]
  let vec' := vec.set ⟨1, by decide⟩ 99#8

  pure (
    test "HWVector.set updates element" (vec'.get ⟨1, by decide⟩ == 99#8) $
    test "HWVector.set preserves other elements" (vec'.get ⟨0, by decide⟩ == 1#8)
  )

def test_hwvector_replicate : IO TestSeq := do
  let vec := HWVector.replicate 4 (42#8)

  pure (
    test "HWVector.replicate creates correct size" (vec.data.size == 4) $
    test "HWVector.replicate element 0" (vec.get ⟨0, by decide⟩ == 42#8) $
    test "HWVector.replicate element 3" (vec.get ⟨3, by decide⟩ == 42#8)
  )

def test_hwvector_map : IO TestSeq := do
  let vec := HWVector.ofList [1#8, 2#8, 3#8, 4#8]
  let doubled := vec.map (· * 2#8)

  pure (
    test "HWVector.map doubles element 0" (doubled.get ⟨0, by decide⟩ == 2#8) $
    test "HWVector.map doubles element 1" (doubled.get ⟨1, by decide⟩ == 4#8) $
    test "HWVector.map doubles element 2" (doubled.get ⟨2, by decide⟩ == 6#8) $
    test "HWVector.map doubles element 3" (doubled.get ⟨3, by decide⟩ == 8#8)
  )

/-! ## HWType Array Tests -/

def test_hwtype_array_basics : IO TestSeq := do
  let arrayType := HWType.array 4 (.bitVector 8)
  let vecType := HWType.bitVector 8

  pure (
    test "HWType.array bitWidth calculation" (arrayType.bitWidth == 32) $  -- 4 * 8 = 32
    test "HWType.isArray predicate" arrayType.isArray $
    test "HWType.bitVector is not array" (not vecType.isArray) $
    test "HWType.bit is not array" (not HWType.bit.isArray)
  )

def test_hwtype_array_nested : IO TestSeq := do
  let nestedArray := HWType.array 2 (.array 4 (.bitVector 8))

  pure (
    test "Nested array bitWidth" (nestedArray.bitWidth == 64) $  -- 2 * 4 * 8 = 64
    test "Nested array is array" nestedArray.isArray
  )

def test_hwtype_array_sizes : IO TestSeq := do
  let arr8x16 := HWType.array 8 (.bitVector 16)
  let arr2x4 := HWType.array 2 (.bitVector 4)
  let arr256x8 := HWType.array 256 (.bitVector 8)

  pure (
    test "8x16 array bitWidth" (arr8x16.bitWidth == 128) $  -- 8 * 16 = 128
    test "2x4 array bitWidth" (arr2x4.bitWidth == 8) $      -- 2 * 4 = 8
    test "256x8 array bitWidth" (arr256x8.bitWidth == 2048)  -- 256 * 8 = 2048
  )

def test_hwtype_array_toString : IO TestSeq := do
  let arrayType := HWType.array 4 (.bitVector 8)
  let nested := HWType.array 2 (.array 4 (.bitVector 8))

  pure (
    test "HWType.array toString" (arrayType.toString == "Array[4](BitVec8)") $
    test "Nested array toString" (nested.toString == "Array[2](Array[4](BitVec8))")
  )

/-! ## Signal Definitions Type Check -/

def test_signal_definitions : IO TestSeq := do
  -- Just test that our signal definitions type-check
  pure (
    test "registerFileRead type-checks" true $
    test "constantIndex type-checks" true $
    test "registerFile16 type-checks" true $
    test "smallArray type-checks" true
  )

/-! ## Combined Test Suite -/

def arrayTests : IO TestSeq := do
  let tests1 ← test_hwvector_operations
  let tests2 ← test_hwvector_set
  let tests3 ← test_hwvector_replicate
  let tests4 ← test_hwvector_map
  let tests5 ← test_hwtype_array_basics
  let tests6 ← test_hwtype_array_nested
  let tests7 ← test_hwtype_array_sizes
  let tests8 ← test_hwtype_array_toString
  let tests9 ← test_signal_definitions

  return group "Array/Vector Tests" (
    tests1 ++ tests2 ++ tests3 ++ tests4 ++ tests5 ++ tests6 ++ tests7 ++ tests8 ++ tests9
  )

end Sparkle.Test.Array
