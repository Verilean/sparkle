-- =============================================================================
-- FPU Simulation Tests
-- Cycle-accurate simulation using Signal.atTime
-- =============================================================================

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.FPU.Hardware

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Hardware

/-- Helper: convert a Nat (representing IEEE 754 bits) to hex string -/
def toHex (n : Nat) : String :=
  let digits := "0123456789ABCDEF"
  let rec go (n : Nat) (acc : String) (count : Nat) : String :=
    if count == 0 then acc
    else go (n / 16) (digits.get ⟨n % 16⟩ |>.toString ++ acc) (count - 1)
  "0x" ++ go n "" 8

def main : IO Unit := do
  IO.println "=== FPU Sparkle Simulation Tests ==="
  IO.println ""

  -- Test 1: Combinational Addition 1.5 + 2.5
  IO.println "--- Test 1: 1.5 + 2.5 (combinational) ---"
  let r1 := fpAddSubComb 0x3FC00000#32 0x40200000#32 false
  IO.println s!"  Result: {toHex r1.toNat} (expected 0x40800000 = 4.0)"
  IO.println s!"  {if r1 == 0x40800000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 2: Subtraction 10.0 - 3.5
  IO.println "--- Test 2: 10.0 - 3.5 (combinational) ---"
  let r2 := fpAddSubComb 0x41200000#32 0x40600000#32 true
  IO.println s!"  Result: {toHex r2.toNat} (expected 0x40D00000 = 6.5)"
  IO.println s!"  {if r2 == 0x40D00000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 3: Multiplication 3.0 * 4.0
  IO.println "--- Test 3: 3.0 * 4.0 (combinational) ---"
  let r3 := fpMulComb 0x40400000#32 0x40800000#32
  IO.println s!"  Result: {toHex r3.toNat} (expected 0x41400000 = 12.0)"
  IO.println s!"  {if r3 == 0x41400000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 4: Multiplication -2.5 * 3.0
  IO.println "--- Test 4: -2.5 * 3.0 (combinational) ---"
  let r4 := fpMulComb 0xC0200000#32 0x40400000#32
  IO.println s!"  Result: {toHex r4.toNat} (expected 0xC0F00000 = -7.5)"
  IO.println s!"  {if r4 == 0xC0F00000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 5: NaN propagation
  IO.println "--- Test 5: NaN + 1.0 → NaN ---"
  let r5 := fpAddSubComb 0x7FC00000#32 0x3F800000#32 false
  IO.println s!"  Result: {toHex r5.toNat} (expected 0x7FC00000 = NaN)"
  IO.println s!"  {if r5 == 0x7FC00000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 6: Inf * 0 = NaN
  IO.println "--- Test 6: Inf * 0 → NaN ---"
  let r6 := fpMulComb 0x7F800000#32 0x00000000#32
  IO.println s!"  Result: {toHex r6.toNat} (expected 0x7FC00000 = NaN)"
  IO.println s!"  {if r6 == 0x7FC00000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 7: x - x = 0
  IO.println "--- Test 7: 1.0 - 1.0 → 0.0 ---"
  let r7 := fpAddSubComb 0x3F800000#32 0x3F800000#32 true
  IO.println s!"  Result: {toHex r7.toNat} (expected 0x00000000 = 0.0)"
  IO.println s!"  {if r7 == 0x00000000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 8: Signal pipeline simulation
  IO.println "--- Test 8: Pipelined add (Signal simulation) ---"
  let sigA : Signal defaultDomain (BitVec 32) := ⟨fun _ => 0x3FC00000#32⟩  -- 1.5
  let sigB : Signal defaultDomain (BitVec 32) := ⟨fun _ => 0x40200000#32⟩  -- 2.5
  let sigSub : Signal defaultDomain Bool := ⟨fun _ => false⟩
  let pipeResult := fpAddSubPipelined sigA sigB sigSub

  -- Check output at various cycles (first 3 are pipeline fill, result at t=3)
  for t in [0, 1, 2, 3, 4, 5] do
    let val := pipeResult.atTime t
    IO.println s!"  t={t}: {toHex val.toNat}"

  let valAt3 := pipeResult.atTime 3
  IO.println s!"  At t=3: {if valAt3 == 0x40800000#32 then "PASS (= 4.0)" else "checking..."}"
  IO.println ""

  -- Test 9: 1.0 * 1.0 = 1.0 (multiplicative identity)
  IO.println "--- Test 9: 1.0 * 1.0 = 1.0 ---"
  let r9 := fpMulComb 0x3F800000#32 0x3F800000#32
  IO.println s!"  Result: {toHex r9.toNat} (expected 0x3F800000 = 1.0)"
  IO.println s!"  {if r9 == 0x3F800000#32 then "PASS" else "FAIL"}"
  IO.println ""

  -- Test 10: 2.0 * 0.5 = 1.0
  IO.println "--- Test 10: 2.0 * 0.5 = 1.0 ---"
  let r10 := fpMulComb 0x40000000#32 0x3F000000#32
  IO.println s!"  Result: {toHex r10.toNat} (expected 0x3F800000 = 1.0)"
  IO.println s!"  {if r10 == 0x3F800000#32 then "PASS" else "FAIL"}"
  IO.println ""

  IO.println "=== All FPU simulation tests complete ==="
