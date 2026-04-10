/-
  Golden value comparison: combinational vs TimeMux BitLinear.

  Verifies that the time-multiplexed FSM produces the same result
  as the combinational (@[reducible] List-based) implementation
  for the same weights and activations.

  Run: lake exe golden-compare-test
-/

import Sparkle
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.TimeMux

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear

/-- Compute combinational BitLinear result via @[reducible] helpers. -/
def combBitLinear (weights : List Int) (act : BitVec 32) : BitVec 32 :=
  let acts : List (Signal defaultDomain (BitVec 32)) :=
    weights.map (fun _ => (Signal.pure act : Signal defaultDomain (BitVec 32)))
  let result := bitLinearSignal (weights.toArray) (acts.toArray)
  result.atTime 0

/-- Compute TimeMux BitLinear result via FSM simulation. -/
def timeMuxBitLinear (weightCodes : List (BitVec 2)) (act : BitVec 32) : IO (BitVec 32) := do
  let dim := weightCodes.length
  -- Weight write signals
  let wAddr : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if t < dim then BitVec.ofNat 16 t else 0#16⟩
  let wData : Signal defaultDomain (BitVec 2) := ⟨fun t =>
    if t < dim then weightCodes.getD t 0#2 else 0#2⟩
  let wEn : Signal defaultDomain Bool := ⟨fun t => t < dim⟩
  let startTime := dim + 1
  let start : Signal defaultDomain Bool := ⟨fun t => t == startTime⟩
  let activation : Signal defaultDomain (BitVec 32) := Signal.pure act

  let state := bitLinearTimeMux (BitVec.ofNat 16 (dim - 1)) wAddr wData wEn start activation
  let result := bitLinearTimeMuxResult state
  let done := bitLinearTimeMuxDone state

  -- Find when done
  for t in List.range (startTime + dim + 10) do
    if done.atTime t then
      return result.atTime t
  return 0#32  -- should not reach

/-- Encode Int weight to 2-bit ternary code. -/
def encodeWeight (w : Int) : BitVec 2 :=
  if w == 1 then 0b10#2
  else if w == -1 then 0b00#2
  else 0b01#2

def main : IO UInt32 := do
  IO.println "=== Golden Value Comparison: Combinational vs TimeMux ==="
  IO.println ""

  let testCases : List (String × List Int × BitVec 32) := [
    ("all +1, act=0x10000", [1, 1, 1, 1], 0x10000#32),
    ("all +1, act=0x20000", [1, 1, 1, 1], 0x20000#32),
    ("mixed, act=100",      [1, -1, 1, 0], 100#32),
    ("all -1, act=10",      [-1, -1, -1, -1], 10#32),
    ("all 0, act=999",      [0, 0, 0, 0], 999#32),
    ("single +1, act=42",   [1, 0, 0, 0], 42#32),
    ("alternating, act=0x30000", [1, -1, 1, -1], 0x30000#32)
  ]

  let mut allPass := true
  for (name, weights, act) in testCases do
    let combResult := combBitLinear weights act
    let codes := weights.map encodeWeight
    let tmResult ← timeMuxBitLinear codes act
    let ok := combResult == tmResult
    if !ok then allPass := false
    let tag := if ok then "✅" else "❌"
    IO.println s!"  {tag} {name}: comb={combResult.toInt}, timemux={tmResult.toInt}"

  IO.println ""
  if allPass then
    IO.println "=== ALL GOLDEN COMPARISONS PASS ==="
    return 0
  else
    IO.println "=== SOME GOLDEN COMPARISONS FAILED ==="
    return 1
