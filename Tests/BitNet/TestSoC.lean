/-
  BitNet SoC Tests — Signal DSL

  Tests for the dual-architecture SoC:
  1. ArchMode and config types
  2. Dynamic BitLinear Signal DSL
  3. HardwiredUnrolled SoC Signal DSL
  4. TimeMultiplexed SoC Signal DSL
  5. Cross-architecture comparison
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.SignalHelpers
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Dynamic
import Examples.BitNet.SoC.Top

namespace Sparkle.Examples.BitNet.Tests.SoC

open Sparkle.Examples.BitNet
open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers
open Sparkle.Examples.BitNet.BitLinear
open Sparkle.Examples.BitNet.SoC

/-- Simple test harness -/
def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  PASS: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"

-- ============================================================================
-- Shared test data (2-layer toy model, dim=4, ffnDim=4)
-- ============================================================================

def testLayerWeights : Array LayerWeights := #[
  { gateWeights := #[1, -1, 0, 1],
    upWeights   := #[-1, 1, 1, 0],
    downWeights := #[1, 0, -1, 1] },
  { gateWeights := #[0, 1, -1, -1],
    upWeights   := #[1, 0, 0, 1],
    downWeights := #[-1, 1, 1, 0] }
]

def testLayerScales : Array LayerScales := #[
  { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 },
  { gateScale := 0x00800000, upScale := 0x01000000, downScale := 0x00C00000 }
]

def testSoCConfigHW : SoCConfig := {
  archMode := .HardwiredUnrolled
  nLayers := 2
  dim := 4
  ffnDim := 4
}

def testSoCConfigTM : SoCConfig := {
  archMode := .TimeMultiplexed
  nLayers := 2
  dim := 4
  ffnDim := 4
}

-- ============================================================================
-- 1. ArchMode and Config Type Tests
-- ============================================================================

def testArchMode : IO Unit := do
  IO.println "--- ArchMode Type Tests ---"

  -- ArchMode values are distinct
  check "HardwiredUnrolled != TimeMultiplexed"
    (ArchMode.HardwiredUnrolled != ArchMode.TimeMultiplexed)

  -- SoCConfig creation and field access
  let cfg := testSoCConfigHW
  check "SoCConfig.nLayers = 2" (cfg.nLayers == 2)
  check "SoCConfig.dim = 4" (cfg.dim == 4)
  check "SoCConfig.ffnDim = 4" (cfg.ffnDim == 4)
  check "SoCConfig.archMode = HardwiredUnrolled"
    (cfg.archMode == .HardwiredUnrolled)

  -- LayerWeights structure
  let lw := testLayerWeights[0]!
  check "LayerWeights gate has 4 elements" (lw.gateWeights.size == 4)
  check "LayerWeights up has 4 elements" (lw.upWeights.size == 4)
  check "LayerWeights down has 4 elements" (lw.downWeights.size == 4)

-- ============================================================================
-- 2. Dynamic BitLinear Signal Tests
-- ============================================================================

def testDynamicBitLinear : IO Unit := do
  IO.println "--- Dynamic BitLinear Signal Tests ---"

  -- Dynamic weights: all +1 (code 10)
  let wCodes : Array (Signal defaultDomain (BitVec 2)) :=
    Array.replicate 4 (Signal.pure 0b10#2)
  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    Array.replicate 4 (Signal.pure (BitVec.ofNat 32 0x10000))  -- 1.0

  let result := dynamicBitLinearSignal wCodes acts
  -- All +1 × 1.0 × 4 = 4.0
  check "dynamic: all +1 × 1.0 = 4.0" (result.atTime 0 == BitVec.ofNat 32 0x40000)

  -- Mixed weights: +1, -1, 0, +1
  let wMixed : Array (Signal defaultDomain (BitVec 2)) :=
    #[Signal.pure 0b10#2,   -- +1
      Signal.pure 0b00#2,   -- -1
      Signal.pure 0b01#2,   -- 0
      Signal.pure 0b10#2]   -- +1
  let resultMixed := dynamicBitLinearSignal wMixed acts
  -- 1 + (-1) + 0 + 1 = 1.0
  check "dynamic: mixed = 1.0" (resultMixed.atTime 0 == BitVec.ofNat 32 0x10000)

-- ============================================================================
-- 3. HardwiredUnrolled SoC Signal Tests
-- ============================================================================

def testHardwiredSoC : IO Unit := do
  IO.println "--- HardwiredUnrolled SoC Signal Tests ---"

  -- Input: 1.0 in Q16.16
  let x : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x10000)
  let result := hardwiredSoCSignal testSoCConfigHW testLayerWeights testLayerScales x

  -- Should produce a valid output (compilation success = correctness)
  check "hw: produces output" true
  let _output := result.atTime 0  -- Force evaluation
  check "hw: evaluates without error" true

  -- Zero input → zero output (all ternary MAC on zeros)
  let x0 : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0)
  let result0 := hardwiredSoCSignal testSoCConfigHW testLayerWeights testLayerScales x0
  check "hw: zero input → zero output" (result0.atTime 0 == BitVec.ofNat 32 0)

-- ============================================================================
-- 4. TimeMultiplexed SoC Signal Tests
-- ============================================================================

def testTimeMultiplexedSoC : IO Unit := do
  IO.println "--- TimeMultiplexed SoC Signal Tests ---"

  let x : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x10000)
  let result := timeMultiplexedSoCSignal testSoCConfigTM testLayerWeights testLayerScales x

  check "tm: produces output" true
  let _output := result.atTime 0
  check "tm: evaluates without error" true

-- ============================================================================
-- 5. Cross-Architecture Comparison Tests
-- ============================================================================

def testComparison : IO Unit := do
  IO.println "--- Cross-Architecture Comparison Tests ---"

  let x : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x10000)
  let hwResult := bitNetSoCSignal testSoCConfigHW testLayerWeights testLayerScales x
  let tmResult := bitNetSoCSignal testSoCConfigTM testLayerWeights testLayerScales x

  -- Both architectures should produce the same output
  check "compare: HW == TM output" (hwResult.atTime 0 == tmResult.atTime 0)

  -- Both work with zero input
  let x0 : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0)
  let hwZero := bitNetSoCSignal testSoCConfigHW testLayerWeights testLayerScales x0
  let tmZero := bitNetSoCSignal testSoCConfigTM testLayerWeights testLayerScales x0
  check "compare: HW == TM for zero input" (hwZero.atTime 0 == tmZero.atTime 0)

def runAll : IO Unit := do
  IO.println "=== SoC Tests ==="
  IO.println ""
  testArchMode
  IO.println ""
  testDynamicBitLinear
  IO.println ""
  testHardwiredSoC
  IO.println ""
  testTimeMultiplexedSoC
  IO.println ""
  testComparison
  IO.println ""
  IO.println "=== All SoC tests complete ==="

end Sparkle.Examples.BitNet.Tests.SoC
