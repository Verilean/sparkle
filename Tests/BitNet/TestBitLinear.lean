/-
  BitNet BitLinear Tests — Signal DSL

  Tests for the BitLinear engine:
  - Ternary encoding (pure spec)
  - Sign extension (pure spec)
  - Fixed-point scale (pure spec)
  - Dot product (pure spec)
  - Config and memory map (pure spec)
  - BitLinear Signal DSL functional tests
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Examples.BitNet.MemoryMap
import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.SignalHelpers
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Top
import Examples.BitNet.BitLinear.Dynamic

namespace Sparkle.Examples.BitNet.Tests.BitLinear

open Sparkle.Examples.BitNet
open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers
open Sparkle.Examples.BitNet.BitLinear

/-- Simple test harness -/
def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  PASS: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"

-- ============================================================================
-- Ternary encoding tests (kept from original)
-- ============================================================================

def testTernaryEncoding : IO Unit := do
  IO.println "--- Ternary Encoding Tests ---"

  -- Test extractTernaryCode
  -- Word with known pattern: position 0 = 00 (-1), position 1 = 01 (0), position 2 = 10 (+1)
  -- Bits: ...10_01_00 = 0b100100 = 0x24
  let word : PackedWord := BitVec.ofNat 256 0x24
  let code0 := extractTernaryCode word 0
  let code1 := extractTernaryCode word 1
  let code2 := extractTernaryCode word 2

  check "extract pos 0 = 00" (code0 == 0b00#2)
  check "extract pos 1 = 01" (code1 == 0b01#2)
  check "extract pos 2 = 10" (code2 == 0b10#2)

  -- Test decodeTernary
  check "decode 00 = negOne" (decodeTernary 0b00#2 == .negOne)
  check "decode 01 = zero"   (decodeTernary 0b01#2 == .zero)
  check "decode 10 = posOne" (decodeTernary 0b10#2 == .posOne)
  check "decode 11 = zero"   (decodeTernary 0b11#2 == .zero)

  -- Test ternaryToInt
  check "negOne → -1" (ternaryToInt .negOne == -1)
  check "zero → 0"    (ternaryToInt .zero == 0)
  check "posOne → +1" (ternaryToInt .posOne == 1)

-- ============================================================================
-- Sign extension tests (kept from original)
-- ============================================================================

def testSignExtension : IO Unit := do
  IO.println "--- Sign Extension Tests ---"

  -- Positive value: 0x00010000 (1.0 in Q16.16)
  let posVal : BitVec 32 := BitVec.ofNat 32 0x00010000
  let posExt := signExtend32to48 posVal
  check "sign-ext positive" (posExt.toNat == 0x000000010000)

  -- Negative value: 0xFFFF0000 (-1.0 in Q16.16)
  let negVal : BitVec 32 := BitVec.ofNat 32 0xFFFF0000
  let negExt := signExtend32to48 negVal
  -- In 48-bit: 0xFFFFFFFF0000
  check "sign-ext negative" (negExt.toNat == 0xFFFFFFFF0000)

  -- Zero
  let zeroVal : BitVec 32 := BitVec.ofNat 32 0
  let zeroExt := signExtend32to48 zeroVal
  check "sign-ext zero" (zeroExt.toNat == 0)

-- ============================================================================
-- Fixed-point scale tests (kept from original)
-- ============================================================================

def testFixedPointScale : IO Unit := do
  IO.println "--- Fixed-Point Scale Tests ---"

  let acc1 : Accumulator := BitVec.ofNat 48 0x10000
  let scale1 : ScaleFactor := BitVec.ofNat 32 0x01000000
  let result1 := fixedPointScale acc1 scale1
  check "1.0 * 1.0 = 1.0" (result1.toNat == 0x10000)

  let acc2 : Accumulator := BitVec.ofNat 48 0x20000
  let scale2 : ScaleFactor := BitVec.ofNat 32 0x00800000
  let result2 := fixedPointScale acc2 scale2
  check "2.0 * 0.5 = 1.0" (result2.toNat == 0x10000)

-- ============================================================================
-- Dot product tests (kept from original)
-- ============================================================================

def testDotProduct : IO Unit := do
  IO.println "--- Dot Product Tests ---"

  let allPosWord : PackedWord := Id.run do
    let mut word : Nat := 0
    for i in [:128] do
      word := word ||| (2 <<< (i * 2))  -- code 10 = +1
    pure (BitVec.ofNat 256 word)

  let activations : Array Activation := Array.replicate 128 (BitVec.ofNat 32 0x10000)
  let result := ternaryDotGroup allPosWord activations
  check "all +1 dot 1.0 = 128.0" (result.toInt == 128 * 0x10000)

  let allNegWord : PackedWord := BitVec.ofNat 256 0  -- all 00 = -1
  let resultNeg := ternaryDotGroup allNegWord activations
  check "all -1 dot 1.0 = -128.0" (resultNeg.toInt == -128 * 0x10000)

  let allZeroWord : PackedWord := Id.run do
    let mut word : Nat := 0
    for i in [:128] do
      word := word ||| (1 <<< (i * 2))  -- code 01 = 0
    pure (BitVec.ofNat 256 word)

  let resultZero := ternaryDotGroup allZeroWord activations
  check "all 0 dot 1.0 = 0" (resultZero.toInt == 0)

-- ============================================================================
-- Config tests (kept from original)
-- ============================================================================

def testConfig : IO Unit := do
  IO.println "--- Config Tests ---"

  check "groupsPerRow(2048) = 16" (groupsPerRow 2048 == 16)
  check "groupsPerRow(5632) = 44" (groupsPerRow 5632 == 44)

  check "ceilLog2(1) = 1"   (ceilLog2 1 == 1)
  check "ceilLog2(16) = 4"  (ceilLog2 16 == 4)
  check "ceilLog2(128) = 7" (ceilLog2 128 == 7)
  check "ceilLog2(44) = 6"  (ceilLog2 44 == 6)

  let cfg := ffnDown  -- 5632 → 2048
  check "ffnDown.groupsPerRow = 44" (cfg.groupsPerRow == 44)
  check "ffnDown.romDepth = 90112" (cfg.romDepth == 90112)

-- ============================================================================
-- Memory map tests (kept from original)
-- ============================================================================

def testMemoryMap : IO Unit := do
  IO.println "--- Memory Map Tests ---"

  let cfg := attnQKV  -- 2048 → 2048, groupsPerRow = 16
  check "addr(0,0) = 0"   (weightRomAddr cfg 0 0 == 0)
  check "addr(0,15) = 15"  (weightRomAddr cfg 0 15 == 15)
  check "addr(1,0) = 16"   (weightRomAddr cfg 1 0 == 16)
  check "addr(2,3) = 35"   (weightRomAddr cfg 2 3 == 35)

  check "valid(0,0)"     (validWeightAddr cfg 0 0 == true)
  check "valid(2047,15)" (validWeightAddr cfg 2047 15 == true)
  check "invalid row"    (validWeightAddr cfg 2048 0 == false)
  check "invalid group"  (validWeightAddr cfg 0 16 == false)

-- ============================================================================
-- BitLinear Signal DSL Functional Tests
-- ============================================================================

def testBitLinearSignal : IO Unit := do
  IO.println "--- BitLinear Signal Tests ---"

  -- All +1 weights: sum of all activations
  let weights1 : Array Int := #[1, 1, 1, 1]
  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000)]
  let result1 := bitLinearSignal weights1 acts
  -- 4 × 1.0 = 4.0 (Q16.16: 0x40000)
  check "signal: all +1 × 1.0 = 4.0" (result1.atTime 0 == BitVec.ofNat 32 0x40000)

  -- All -1 weights: negate and sum
  let weightsNeg : Array Int := #[-1, -1, -1, -1]
  let resultNeg := bitLinearSignal weightsNeg acts
  check "signal: all -1 × 1.0 = -4.0" (resultNeg.atTime 0 == BitVec.ofInt 32 (-0x40000))

  -- Mixed weights with zeros (pruning)
  let weightsMixed : Array Int := #[1, 0, -1, 0]
  let actsMixed : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x20000),  -- 2.0
      Signal.pure (BitVec.ofNat 32 0x30000),  -- 3.0 (pruned)
      Signal.pure (BitVec.ofNat 32 0x10000),  -- 1.0
      Signal.pure (BitVec.ofNat 32 0x40000)]  -- 4.0 (pruned)
  let resultMixed := bitLinearSignal weightsMixed actsMixed
  -- 1×2.0 + 0 + (-1)×1.0 + 0 = 2.0 - 1.0 = 1.0
  check "signal: mixed weights" (resultMixed.atTime 0 == BitVec.ofNat 32 0x10000)

  -- All zero weights: constant 0
  let weightsZero : Array Int := #[0, 0, 0, 0]
  let resultZero := bitLinearSignal weightsZero acts
  check "signal: all-zero weights = 0" (resultZero.atTime 0 == BitVec.ofNat 32 0)

  -- Single +1 weight: pass-through
  let weightsSingle : Array Int := #[1]
  let actsSingle : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x50000)]  -- 5.0
  let resultSingle := bitLinearSignal weightsSingle actsSingle
  check "signal: single +1 = pass-through" (resultSingle.atTime 0 == BitVec.ofNat 32 0x50000)

def testDynamicBitLinearSignal : IO Unit := do
  IO.println "--- Dynamic BitLinear Signal Tests ---"

  -- Dynamic weights: +1, -1, 0, +1
  let wCodes : Array (Signal defaultDomain (BitVec 2)) :=
    #[Signal.pure 0b10#2,   -- +1
      Signal.pure 0b00#2,   -- -1
      Signal.pure 0b01#2,   -- 0
      Signal.pure 0b10#2]   -- +1
  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x10000),  -- 1.0
      Signal.pure (BitVec.ofNat 32 0x20000),  -- 2.0
      Signal.pure (BitVec.ofNat 32 0x30000),  -- 3.0
      Signal.pure (BitVec.ofNat 32 0x10000)]  -- 1.0

  let result := dynamicBitLinearSignal wCodes acts
  -- 1×1.0 + (-1)×2.0 + 0×3.0 + 1×1.0 = 1.0 - 2.0 + 0.0 + 1.0 = 0.0
  check "dynamic: +1,-1,0,+1 = 0.0" (result.atTime 0 == BitVec.ofNat 32 0)

def runAll : IO Unit := do
  IO.println "=== BitLinear Tests ==="
  testTernaryEncoding
  testSignExtension
  testFixedPointScale
  testDotProduct
  testConfig
  testMemoryMap
  testBitLinearSignal
  testDynamicBitLinearSignal
  IO.println "=== Tests complete ==="

end Sparkle.Examples.BitNet.Tests.BitLinear
