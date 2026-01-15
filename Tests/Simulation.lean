/-
  Simulation Test Suite

  Tests Phase 1 functionality: Signal simulation, registers, combinational logic
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Test 1: Pure combinational logic -/
def testCombinational : IO Unit := do
  IO.println "Test 1: Combinational Logic"

  let a : Signal defaultDomain (BitVec 8) := Signal.pure 5#8
  let b : Signal defaultDomain (BitVec 8) := Signal.pure 3#8

  let sum := (· + ·) <$> a <*> b
  let diff := (· - ·) <$> a <*> b
  let prod := (· * ·) <$> a <*> b

  assert! sum.atTime 0 == 8#8
  assert! diff.atTime 0 == 2#8
  assert! prod.atTime 0 == 15#8

  IO.println "  ✓ Addition, subtraction, multiplication work"

/-- Test 2: Register delays -/
def testRegisterDelay : IO Unit := do
  IO.println "\nTest 2: Register Delays"

  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 (t * 10)⟩
  let delayed := Signal.register 99#8 input

  -- At t=0, should output initial value
  assert! delayed.atTime 0 == 99#8

  -- At t=1, should output input at t=0
  assert! delayed.atTime 1 == 0#8

  -- At t=2, should output input at t=1
  assert! delayed.atTime 2 == 10#8

  IO.println "  ✓ Register delays by one cycle correctly"

/-- Test 3: Register chain (multi-cycle delay) -/
def testRegisterChain : IO Unit := do
  IO.println "\nTest 3: Register Chain"

  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
  let delay1 := Signal.register 255#8 input
  let delay2 := Signal.register 254#8 delay1
  let delay3 := Signal.register 253#8 delay2

  -- Check 3-cycle delay
  assert! delay3.atTime 0 == 253#8
  assert! delay3.atTime 1 == 254#8
  assert! delay3.atTime 2 == 255#8
  assert! delay3.atTime 3 == 0#8
  assert! delay3.atTime 4 == 1#8

  IO.println "  ✓ Multi-cycle delays work correctly"

/-- Test 4: Multiplexer -/
def testMux : IO Unit := do
  IO.println "\nTest 4: Multiplexer"

  let sel : Signal defaultDomain Bool := ⟨fun t => t % 2 == 0⟩
  let a : Signal defaultDomain (BitVec 8) := Signal.pure 0xAA#8
  let b : Signal defaultDomain (BitVec 8) := Signal.pure 0xBB#8
  let result := Signal.mux sel a b

  assert! result.atTime 0 == 0xAA#8  -- sel = true
  assert! result.atTime 1 == 0xBB#8  -- sel = false
  assert! result.atTime 2 == 0xAA#8  -- sel = true

  IO.println "  ✓ Multiplexer selects correctly"

/-- Test 5: Map and register composition -/
def testMapWithRegister : IO Unit := do
  IO.println "\nTest 5: Map + Register Composition"

  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
  let doubled := input.map (· * 2#8)
  let registered := Signal.register 0#8 doubled

  assert! input.atTime 3 == 3#8
  assert! doubled.atTime 3 == 6#8
  assert! registered.atTime 3 == 4#8  -- Previous doubled value (2*2)

  IO.println "  ✓ Composition of map and register works"

/-- Test 6: BitPack round-trip -/
def testBitPack : IO Unit := do
  IO.println "\nTest 6: BitPack Round-trip"
  IO.println "  ✓ BitPack tested in separate file"

/-- Test 7: Bundle and unbundle -/
def testBundle : IO Unit := do
  IO.println "\nTest 7: Bundle and Unbundle"

  let a : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 t⟩
  let b : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 (t + 10)⟩
  let bundled := bundle2 a b

  let (a', b') := unbundle2 bundled

  assert! a'.atTime 2 == 2#4
  assert! b'.atTime 2 == 12#4

  IO.println "  ✓ Bundle and unbundle preserve values"

/-- Run all simulation tests -/
def main : IO Unit := do
  IO.println "=== Sparkle Simulation Test Suite ===\n"

  testCombinational
  testRegisterDelay
  testRegisterChain
  testMux
  testMapWithRegister
  testBitPack
  testBundle

  IO.println "\n✅ All simulation tests passed!"

#eval main
