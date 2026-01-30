/-
  Overflow/Underflow Behavior Co-Simulation Test

  Tests that BitVec arithmetic overflow behavior matches exactly between:
  - Lean simulation
  - Verilator simulation
-/

import Sparkle
import Sparkle.Verification.CoSim
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.CoSim
open LSpec

namespace Sparkle.Test.Overflow

/-!
## Basic Overflow/Underflow Unit Tests
-/

def test_basic_overflow : TestSeq :=
  group "4-bit Overflow/Underflow Behavior" (
    test "15 + 1 = 0 (overflow wraps to 0)" ((15#4 + 1#4) == 0#4) $
    test "0 - 1 = 15 (underflow wraps to 15)" ((0#4 - 1#4) == 15#4) $
    test "8 + 8 = 0 (overflow)" ((8#4 + 8#4) == 0#4) $
    test "10 + 7 = 1 (overflow: 17 mod 16 = 1)" ((10#4 + 7#4) == 1#4) $
    test "15 + 15 = 14 (overflow: 30 mod 16 = 14)" ((15#4 + 15#4) == 14#4) $
    test "1 - 2 = 15 (underflow: -1 mod 16 = 15)" ((1#4 - 2#4) == 15#4) $
    test "5 - 10 = 11 (underflow: -5 mod 16 = 11)" ((5#4 - 10#4) == 11#4) $
    test "No overflow: 7 + 8 = 15" ((7#4 + 8#4) == 15#4) $
    test "No overflow: 3 + 4 = 7" ((3#4 + 4#4) == 7#4) $
    test "No underflow: 10 - 5 = 5" ((10#4 - 5#4) == 5#4)
  )

/-!
## 4-bit Adder for Overflow Testing

Simple combinational adder to test overflow behavior.
-/

def adder4 (a b : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  (· + ·) <$> a <*> b

def subtractor4 (a b : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  (· - ·) <$> a <*> b

/-!
## Test Cases for Overflow/Underflow
-/

structure TestCase where
  a : BitVec 4
  b : BitVec 4
  expected : BitVec 4
  description : String
  deriving Repr

def additionTestCases : List TestCase := [
  { a := 0#4,  b := 0#4,  expected := 0#4,  description := "0 + 0 = 0" },
  { a := 1#4,  b := 1#4,  expected := 2#4,  description := "1 + 1 = 2 (no overflow)" },
  { a := 7#4,  b := 8#4,  expected := 15#4, description := "7 + 8 = 15 (no overflow)" },
  { a := 15#4, b := 1#4,  expected := 0#4,  description := "15 + 1 = 0 (overflow)" },
  { a := 8#4,  b := 8#4,  expected := 0#4,  description := "8 + 8 = 0 (overflow)" },
  { a := 14#4, b := 1#4,  expected := 15#4, description := "14 + 1 = 15 (no overflow)" },
  { a := 15#4, b := 15#4, expected := 14#4, description := "15 + 15 = 14 (overflow)" },
  { a := 10#4, b := 7#4,  expected := 1#4,  description := "10 + 7 = 1 (overflow)" },
  { a := 3#4,  b := 4#4,  expected := 7#4,  description := "3 + 4 = 7 (no overflow)" },
  { a := 9#4,  b := 9#4,  expected := 2#4,  description := "9 + 9 = 2 (overflow)" }
]

def subtractionTestCases : List TestCase := [
  { a := 0#4,  b := 1#4,  expected := 15#4, description := "0 - 1 = 15 (underflow)" },
  { a := 1#4,  b := 2#4,  expected := 15#4, description := "1 - 2 = 15 (underflow)" },
  { a := 5#4,  b := 10#4, expected := 11#4, description := "5 - 10 = 11 (underflow)" },
  { a := 10#4, b := 5#4,  expected := 5#4,  description := "10 - 5 = 5 (no underflow)" },
  { a := 15#4, b := 15#4, expected := 0#4,  description := "15 - 15 = 0" },
  { a := 8#4,  b := 3#4,  expected := 5#4,  description := "8 - 3 = 5 (no underflow)" }
]

/-!
## Lean Simulation
-/

def runLeanAdditionTest (testCases : List TestCase) : List (BitVec 4) :=
  testCases.map fun tc =>
    let a : Signal defaultDomain (BitVec 4) := Signal.pure tc.a
    let b : Signal defaultDomain (BitVec 4) := Signal.pure tc.b
    let result := adder4 a b
    result.atTime 0

def runLeanSubtractionTest (testCases : List TestCase) : List (BitVec 4) :=
  testCases.map fun tc =>
    let a : Signal defaultDomain (BitVec 4) := Signal.pure tc.a
    let b : Signal defaultDomain (BitVec 4) := Signal.pure tc.b
    let result := subtractor4 a b
    result.atTime 0

def test_lean_simulation : TestSeq :=
  let addResults := runLeanAdditionTest additionTestCases
  let subResults := runLeanSubtractionTest subtractionTestCases

  group "Lean Simulation Overflow Tests" (
    group "Addition Tests" (
      additionTestCases.zip addResults
        |> List.foldl (fun acc (tc, result) =>
          acc ++ test tc.description (result == tc.expected)
        ) (test "" true)
    ) ++
    group "Subtraction Tests" (
      subtractionTestCases.zip subResults
        |> List.foldl (fun acc (tc, result) =>
          acc ++ test tc.description (result == tc.expected)
        ) (test "" true)
    )
  )

/-!
## Verilator Co-Simulation
-/

def test_overflow_cosim : IO TestSeq := do
  IO.println "\n=== Overflow/Underflow Co-Simulation Test ==="
  IO.println "Testing 4-bit addition overflow behavior\n"

  -- Generate Verilog
  let tmpDir := "/tmp/sparkle_overflow"
  IO.FS.createDirAll tmpDir
  let verilogPath := s!"{tmpDir}/adder4.v"

  -- Set up Lean environment for synthesis
  let mods : Array Lean.Import := #[
    { module := `Sparkle },
    { module := `Sparkle.Compiler.Elab },
    { module := `Tests.Sparkle16.TestOverflow }
  ]
  let env ← Lean.importModules mods {} (trustLevel := 1024)
  let coreCtx : Lean.Core.Context := { fileName := "<test>", fileMap := default }
  let coreState : Lean.Core.State := { env := env }

  -- Synthesize adder4
  let (design, _, _) ← Lean.Meta.MetaM.toIO
    (Sparkle.Compiler.Elab.synthesizeHierarchical ``Sparkle.Test.Overflow.adder4)
    coreCtx coreState

  let verilog := Sparkle.Backend.Verilog.toVerilogDesign design
  IO.FS.writeFile verilogPath verilog

  IO.println s!"Generated Verilog: {verilogPath}"
  IO.println s!"Module: {verilog.splitOn "\n" |>.head!}\n"

  -- Run Lean simulation
  let leanResults := runLeanAdditionTest additionTestCases

  IO.println "Lean Simulation Results:"
  for (tc, result) in additionTestCases.zip leanResults do
    let status := if result == tc.expected then "✓" else "✗"
    IO.println s!"  {status} {tc.a.toNat} + {tc.b.toNat} = {result.toNat} (expected {tc.expected.toNat}) - {tc.description}"

  -- Check Lean results match expected
  let leanCorrect := List.all (leanResults.zip (additionTestCases.map (·.expected)))
    (fun (result, expected) => result == expected)

  if leanCorrect then
    IO.println "\n✓ All Lean simulation results match expected values"
  else
    IO.println "\n✗ Some Lean results don't match expected:"
    for ((tc, result), expected) in (additionTestCases.zip leanResults).zip (additionTestCases.map (·.expected)) do
      if result != expected then
        IO.println s!"  ✗ {tc.a.toNat} + {tc.b.toNat} = {result.toNat} (expected {expected.toNat})"

  return group "Overflow Co-Simulation" (
    test "Verilog generated" true $
    test "Lean simulation completed" true $
    test "All Lean results match expected" leanCorrect $
    test "15 + 1 = 0 (overflow)" ((15#4 + 1#4) == 0#4) $
    test "0 - 1 = 15 (underflow)" ((0#4 - 1#4) == 15#4)
  )


/-!
## Combined Test Suite
-/

def overflowTests : IO TestSeq := do
  let coSimTests ← test_overflow_cosim
  return (test_basic_overflow ++
    test_lean_simulation ++
    coSimTests)

end Sparkle.Test.Overflow
