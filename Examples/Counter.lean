/-
  Example: Simple Counter Circuit

  Demonstrates Phase 1 functionality:
  - Signal simulation
  - Register (sequential logic)
  - Functor/Applicative operations (combinational logic)
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Example: Combinational logic on signals -/
def testCombinational : IO Unit := do
  let a : Signal defaultDomain (BitVec 8) := Signal.pure 5#8
  let b : Signal defaultDomain (BitVec 8) := Signal.pure 3#8
  let sum := (· + ·) <$> a <*> b
  let product := (· * ·) <$> a <*> b

  IO.println "Combinational logic:"
  IO.println s!"  a = {a.atTime 0}"
  IO.println s!"  b = {b.atTime 0}"
  IO.println s!"  a + b = {sum.atTime 0}"
  IO.println s!"  a * b = {product.atTime 0}"

/-- Example: Register delays signal by one cycle -/
def testRegisterDelay : IO Unit := do
  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 (t * 10)⟩
  let delayed := Signal.register 99#8 input

  IO.println "\nRegister delay test:"
  for i in [:5] do
    IO.println s!"  t={i}: input={input.atTime i}, delayed={delayed.atTime i}"

/-- Example: Register chain (two-cycle delay) -/
def testRegisterChain : IO Unit := do
  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
  let delayed1 := Signal.register 255#8 input
  let delayed2 := Signal.register 254#8 delayed1

  IO.println "\nRegister chain (two-cycle delay):"
  for i in [:8] do
    IO.println s!"  t={i}: input={input.atTime i}, delayed1={delayed1.atTime i}, delayed2={delayed2.atTime i}"

/-- Example: Mux (multiplexer) -/
def testMux : IO Unit := do
  let sel : Signal defaultDomain Bool := ⟨fun t => t % 2 == 0⟩
  let a : Signal defaultDomain (BitVec 8) := Signal.pure 0xAA#8
  let b : Signal defaultDomain (BitVec 8) := Signal.pure 0xBB#8
  let result := Signal.mux sel a b

  IO.println "\nMux test (select between 0xAA and 0xBB):"
  for i in [:6] do
    IO.println s!"  t={i}: sel={sel.atTime i}, result={result.atTime i}"

/-- Example: Combining map and register -/
def testMapWithRegister : IO Unit := do
  let input : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
  let doubled := input.map (· * 2#8)
  let registered := Signal.register 0#8 doubled

  IO.println "\nMap with register (double then delay):"
  for i in [:6] do
    IO.println s!"  t={i}: input={input.atTime i}, doubled={doubled.atTime i}, registered={registered.atTime i}"

/-- Example: Bundle signals -/
def testBundle : IO Unit := do
  let a : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 t⟩
  let b : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 (t + 10)⟩
  let bundled := bundle2 a b

  IO.println "\nBundle test:"
  for i in [:4] do
    IO.println s!"  t={i}: a={a.atTime i}, b={b.atTime i}, bundled={bundled.atTime i}"

/-- Main: Run all tests -/
def main : IO Unit := do
  testCombinational
  testRegisterDelay
  testRegisterChain
  testMux
  testMapWithRegister
  testBundle
  IO.println "\n✓ Phase 1 simulation tests complete!"

-- Evaluate at compile time
#eval testCombinational
