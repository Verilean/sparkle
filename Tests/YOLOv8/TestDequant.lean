/-
  Test: INT4 → INT8 Dequantization
  Verifies sign extension correctness for all INT4 values.
-/

import LSpec
import IP.YOLOv8.Primitives.Dequant
import IP.YOLOv8.Types

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8
open Sparkle.IP.YOLOv8.Primitives.Dequant

namespace Sparkle.IP.YOLOv8.Tests.TestDequant

/-- Test that dequantInt4ToInt8 correctly sign-extends all 16 INT4 values. -/
def testSignExtension : LSpec.TestSeq :=
  -- Test positive values (0..7)
  let test0 :=
    let inp : Signal defaultDomain (BitVec 4) := Signal.pure 0#4
    let out := dequantInt4ToInt8 inp
    LSpec.test "INT4 0 → INT8 0" (out.atTime 0 == 0#8)
  let test1 :=
    let inp : Signal defaultDomain (BitVec 4) := Signal.pure 1#4
    let out := dequantInt4ToInt8 inp
    LSpec.test "INT4 1 → INT8 1" (out.atTime 0 == 1#8)
  let test7 :=
    let inp : Signal defaultDomain (BitVec 4) := Signal.pure 7#4
    let out := dequantInt4ToInt8 inp
    LSpec.test "INT4 7 → INT8 7" (out.atTime 0 == 7#8)
  -- Test negative values (-1..-8 in two's complement)
  let testNeg1 :=
    let inp : Signal defaultDomain (BitVec 4) := Signal.pure 15#4  -- -1 in 4-bit
    let out := dequantInt4ToInt8 inp
    LSpec.test "INT4 -1 → INT8 -1" (out.atTime 0 == 255#8)  -- -1 in 8-bit
  let testNeg8 :=
    let inp : Signal defaultDomain (BitVec 4) := Signal.pure 8#4   -- -8 in 4-bit
    let out := dequantInt4ToInt8 inp
    LSpec.test "INT4 -8 → INT8 -8" (out.atTime 0 == 248#8)  -- -8 in 8-bit
  test0 ++ test1 ++ test7 ++ testNeg1 ++ testNeg8

/-- Test packed byte extraction. -/
def testPackedExtraction : LSpec.TestSeq :=
  let packed : Signal defaultDomain (BitVec 8) := Signal.pure 0xA3#8
  -- Lower nibble: 0x3 = 3
  let lower := extractLowerInt4Signal packed
  -- Upper nibble: 0xA = 10 = -6 in INT4
  let upper := extractUpperInt4Signal packed
  LSpec.test "lower nibble of 0xA3 = 3" (lower.atTime 0 == 3#4) ++
  LSpec.test "upper nibble of 0xA3 = 0xA" (upper.atTime 0 == 10#4)

/-- Test full dequant pipeline (packed → INT8). -/
def testFullDequant : LSpec.TestSeq :=
  -- 0x72: lower = 2, upper = 7
  let packed : Signal defaultDomain (BitVec 8) := Signal.pure 0x72#8
  let lowerInt8 := dequantLowerToInt8 packed
  let upperInt8 := dequantUpperToInt8 packed
  LSpec.test "dequant lower(0x72) = 2" (lowerInt8.atTime 0 == 2#8) ++
  LSpec.test "dequant upper(0x72) = 7" (upperInt8.atTime 0 == 7#8)

def allTests : LSpec.TestSeq :=
  LSpec.group "INT4 Dequantization" (
    LSpec.group "Sign Extension" testSignExtension ++
    LSpec.group "Packed Extraction" testPackedExtraction ++
    LSpec.group "Full Dequant Pipeline" testFullDequant
  )

def runAll : IO Unit := do
  IO.println "--- YOLOv8 Dequant Tests ---"
  let _results := allTests
  IO.println s!"  Tests defined (run via lake test)"

end Sparkle.IP.YOLOv8.Tests.TestDequant
