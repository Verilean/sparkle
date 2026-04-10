/-
  TimeMux BitLinear simulation test.

  Verifies the FSM produces correct ternary MAC results by driving
  the circuit through Signal.atTime.

  Run: lake exe timemux-sim-test
-/

import Sparkle
import IP.BitNet.BitLinear.TimeMux

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.BitNet.BitLinear

/-- Build a TimeMux circuit with pre-loaded weights and test activation. -/
def timeMuxSimTest : IO UInt32 := do
  IO.println "=== TimeMux BitLinear Simulation Test ==="

  -- dim=4, weights = [+1, -1, +1, 0] (codes: 10, 00, 10, 01)
  -- activation = 100 (broadcast to all)
  -- Expected: 100 - 100 + 100 + 0 = 100

  -- Weight write signals: write 4 weights at addresses 0-3
  -- cycle 0: addr=0, data=0b10 (+1), en=true
  -- cycle 1: addr=1, data=0b00 (-1), en=true
  -- cycle 2: addr=2, data=0b10 (+1), en=true
  -- cycle 3: addr=3, data=0b01 (0),  en=true
  -- cycle 4+: en=false

  let wAddr : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if t == 0 then 0#16
    else if t == 1 then 1#16
    else if t == 2 then 2#16
    else if t == 3 then 3#16
    else 0#16⟩

  let wData : Signal defaultDomain (BitVec 2) := ⟨fun t =>
    if t == 0 then 0b10#2  -- +1
    else if t == 1 then 0b00#2  -- -1
    else if t == 2 then 0b10#2  -- +1
    else if t == 3 then 0b01#2  -- 0
    else 0#2⟩

  let wEn : Signal defaultDomain Bool := ⟨fun t => t < 4⟩

  -- Start computation at cycle 5
  let start : Signal defaultDomain Bool := ⟨fun t => t == 5⟩

  -- Activation = 100 constant
  let act : Signal defaultDomain (BitVec 32) := Signal.pure 100#32

  -- Run the circuit
  let state := bitLinearTimeMux 3#16 wAddr wData wEn start act
  let result := bitLinearTimeMuxResult state
  let done := bitLinearTimeMuxDone state

  -- Sample outputs at various times
  IO.println s!"  Weights loaded at t=0..3"
  IO.println s!"  Start pulse at t=5"

  let mut foundDone := false
  let mut doneTime := 0
  for t in List.range 20 do
    let d := done.atTime t
    let r := result.atTime t
    if d && !foundDone then
      foundDone := true
      doneTime := t
      IO.println s!"  t={t}: done=true, result={r.toInt}"

  if !foundDone then
    IO.println "  ❌ FAIL: done never asserted in 20 cycles"
    return 1

  let finalResult := result.atTime doneTime
  -- Expected: +1×100 + (-1)×100 + (+1)×100 + 0×100 = 100
  let expected : BitVec 32 := 100#32
  if finalResult == expected then
    IO.println s!"  ✅ PASS: result={finalResult.toInt} (expected {expected.toInt})"
    return 0
  else
    IO.println s!"  ❌ FAIL: result={finalResult.toInt} (expected {expected.toInt})"
    return 1

/-- Test 2: all +1 weights, dim=4, activation=7. Expected: 7*4 = 28 -/
def timeMuxSimTest2 : IO Bool := do
  IO.println "  Test 2: all +1, activation=7"
  let wAddr : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if t < 4 then BitVec.ofNat 16 t else 0#16⟩
  let wData : Signal defaultDomain (BitVec 2) := Signal.pure 0b10#2  -- all +1
  let wEn : Signal defaultDomain Bool := ⟨fun t => t < 4⟩
  let start : Signal defaultDomain Bool := ⟨fun t => t == 5⟩
  let act : Signal defaultDomain (BitVec 32) := Signal.pure 7#32
  let state := bitLinearTimeMux 3#16 wAddr wData wEn start act
  let result := bitLinearTimeMuxResult state
  let done := bitLinearTimeMuxDone state
  let mut foundTime := 0
  for t in List.range 20 do
    if done.atTime t then foundTime := t; break
  let r := result.atTime foundTime
  let ok := r == 28#32
  IO.println s!"    result={r.toInt}, expected=28 → {if ok then "✅" else "❌"}"
  return ok

/-- Test 3: all -1 weights, dim=4, activation=10. Expected: -40 -/
def timeMuxSimTest3 : IO Bool := do
  IO.println "  Test 3: all -1, activation=10"
  let wAddr : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if t < 4 then BitVec.ofNat 16 t else 0#16⟩
  let wData : Signal defaultDomain (BitVec 2) := Signal.pure 0b00#2  -- all -1
  let wEn : Signal defaultDomain Bool := ⟨fun t => t < 4⟩
  let start : Signal defaultDomain Bool := ⟨fun t => t == 5⟩
  let act : Signal defaultDomain (BitVec 32) := Signal.pure 10#32
  let state := bitLinearTimeMux 3#16 wAddr wData wEn start act
  let result := bitLinearTimeMuxResult state
  let done := bitLinearTimeMuxDone state
  let mut foundTime := 0
  for t in List.range 20 do
    if done.atTime t then foundTime := t; break
  let r := result.atTime foundTime
  -- -40 as 32-bit two's complement
  let expected := (BitVec.ofInt 32 (-40) : BitVec 32)
  let ok := r == expected
  IO.println s!"    result={r.toInt}, expected=-40 → {if ok then "✅" else "❌"}"
  return ok

def main : IO UInt32 := do
  let ok1 ← timeMuxSimTest
  let ok2 ← timeMuxSimTest2
  let ok3 ← timeMuxSimTest3
  if ok1 == 0 && ok2 && ok3 then
    IO.println "\n=== All TimeMux tests PASSED ==="
    return 0
  else
    IO.println "\n=== Some TimeMux tests FAILED ==="
    return 1
