/-
  Hespera BitLinear Tests

  Tests for the pipelined dataflow BitLinear engine.
  Verifies zero-weight pruning, adder tree structure, bit-width propagation,
  and pipeline register insertion.
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Examples.BitNet.MemoryMap
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.Verilog
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Top

namespace Sparkle.Examples.BitNet.Tests.BitLinear

open Sparkle.Examples.BitNet
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

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
-- Pipelined BitLinear tests (NEW)
-- ============================================================================

def testPipelinedBitLinear : IO Unit := do
  IO.println "--- Pipelined BitLinear Tests ---"

  -- Define test weights: 16 elements, 10 active (6 zeros pruned)
  let weights : Array Int := #[-1, 1, 0, 1, -1, 0, 0, 1, 1, -1, 0, 0, 1, -1, 1, 0]
  let cfg : GeneratorConfig := {
    baseBitWidth := 8
    pipelineEvery := 2
  }

  -- Count active/zero weights
  let activeCount := weights.foldl (fun acc w => if w != 0 then acc + 1 else acc) 0
  let zeroCount := weights.size - activeCount
  check "16 total weights" (weights.size == 16)
  check "10 active weights" (activeCount == 10)
  check "6 pruned zeros" (zeroCount == 6)

  -- Generate the pipelined module
  let m := BitLinear.buildTop weights cfg

  -- Verify input count: clk + rst + 10 activation inputs = 12
  check "12 inputs (clk + rst + 10 act)" (m.inputs.length == 12)

  -- Verify the activation inputs are only for non-zero weights
  let actInputNames := m.inputs.filter (fun p => p.name.startsWith "act_")
  check "10 activation inputs" (actInputNames.length == 10)

  -- Verify activation input names match non-zero weight indices
  let expectedActNames := ["act_0", "act_1", "act_3", "act_4", "act_7",
                           "act_8", "act_9", "act_12", "act_13", "act_14"]
  let actualActNames := actInputNames.map (·.name)
  check "correct activation input names" (actualActNames == expectedActNames)

  -- Verify all activation inputs are baseBitWidth
  let allCorrectWidth := actInputNames.all (fun p => p.ty == .bitVector 8)
  check "all act inputs are 8-bit" allCorrectWidth

  -- Verify output exists and has correct width
  -- Adder tree: 10 inputs, 8-bit each
  -- Level 0 (10→5): 9-bit sums
  -- Level 1 (5→3): 10-bit (+ pipeline)
  -- Level 2 (3→2): 11-bit
  -- Level 3 (2→1): 12-bit (+ pipeline)
  -- Expected output width: 12 bits
  check "1 output port" (m.outputs.length == 1)
  check "output named 'result'" (m.outputs.head?.map (·.name) == some "result")
  check "output is 12-bit" (m.outputs.head?.map (·.ty) == some (.bitVector 12))

  -- Count pipeline registers (register statements in body)
  let regCount := m.body.foldl (fun acc s =>
    match s with
    | .register .. => acc + 1
    | _ => acc) 0
  -- Pipeline at level 1 (3 elements) + level 3 (1 element) = 4 registers
  -- Plus the initial pipeline registers if any
  check "pipeline registers present" (regCount > 0)

  -- Verify no FSM states (no state register, no state_next wire)
  let hasStateMachine := m.wires.any (fun p => p.name.find? "state" |>.isSome)
  check "no FSM state machine" (!hasStateMachine)

  -- Print generated Verilog for manual inspection
  IO.println ""
  IO.println "--- Generated Verilog (for inspection) ---"
  let verilog := toVerilog m
  IO.println verilog

-- ============================================================================
-- Edge case tests
-- ============================================================================

def testEdgeCases : IO Unit := do
  IO.println "--- Edge Case Tests ---"

  -- All zeros: should produce constant 0 output
  let allZeroWeights : Array Int := #[0, 0, 0, 0]
  let cfg : GeneratorConfig := { baseBitWidth := 8, pipelineEvery := 2 }
  let m := BitLinear.buildTop allZeroWeights cfg
  check "all-zero: 2 inputs (clk+rst only)" (m.inputs.length == 2)
  check "all-zero: 1 output" (m.outputs.length == 1)

  -- Single +1 weight: output should be 8-bit pass-through
  let singleWeight : Array Int := #[1]
  let m2 := BitLinear.buildTop singleWeight cfg
  check "single +1: 3 inputs (clk+rst+act_0)" (m2.inputs.length == 3)
  check "single +1: output is 8-bit" (m2.outputs.head?.map (·.ty) == some (.bitVector 8))

  -- Two weights: single addition
  let twoWeights : Array Int := #[1, -1]
  let m3 := BitLinear.buildTop twoWeights cfg
  check "two weights: 4 inputs" (m3.inputs.length == 4)
  check "two weights: output is 9-bit" (m3.outputs.head?.map (·.ty) == some (.bitVector 9))

  -- All +1: no negation wires needed
  let allPosWeights : Array Int := #[1, 1, 1, 1]
  let m4 := BitLinear.buildTop allPosWeights cfg
  check "all +1: 6 inputs" (m4.inputs.length == 6)
  -- 4 inputs → 2 sums (9-bit) → 1 sum (10-bit), pipeline at level 1
  check "all +1: output is 10-bit" (m4.outputs.head?.map (·.ty) == some (.bitVector 10))

def runAll : IO Unit := do
  IO.println "=== BitLinear Tests ==="
  testTernaryEncoding
  testSignExtension
  testFixedPointScale
  testDotProduct
  testConfig
  testMemoryMap
  testPipelinedBitLinear
  testEdgeCases
  IO.println "=== Tests complete ==="

end Sparkle.Examples.BitNet.Tests.BitLinear
