/-
  Test: INT32 → INT8 Requantization
  Verifies multiply-shift-clamp for various accumulator values.
-/

import LSpec
import Examples.YOLOv8.Primitives.Requantize
import Examples.YOLOv8.Types

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8.Primitives.Requantize

namespace Sparkle.Examples.YOLOv8.Tests.TestRequantize

/-- Test basic requantization: positive accumulator. -/
def testPositiveRequant : LSpec.TestSeq :=
  -- acc=1024, scale=8, shift=3 → (1024 * 8) >> 3 = 8192 >> 3 = 1024 → clamped to 127
  let acc : Signal defaultDomain (BitVec 32) := Signal.pure 1024#32
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 8#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 3#5
  let result := requantize acc scale shift
  LSpec.test "requant(1024, 8, 3) clamps to 127" (result.atTime 0 == 127#8)

/-- Test requantization: small positive value. -/
def testSmallPositive : LSpec.TestSeq :=
  -- acc=100, scale=1, shift=0 → (100 * 1) >> 0 = 100
  let acc : Signal defaultDomain (BitVec 32) := Signal.pure 100#32
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 0#5
  let result := requantize acc scale shift
  LSpec.test "requant(100, 1, 0) = 100" (result.atTime 0 == 100#8)

/-- Test requantization: negative value. -/
def testNegativeRequant : LSpec.TestSeq :=
  -- acc=-256, scale=1, shift=1 → (-256 * 1) >> 1 = -128
  let acc : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofInt 32 (-256))
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 1#5
  let result := requantize acc scale shift
  LSpec.test "requant(-256, 1, 1) = -128" (result.atTime 0 == BitVec.ofInt 8 (-128))

/-- Test requantization: zero accumulator. -/
def testZeroRequant : LSpec.TestSeq :=
  let acc : Signal defaultDomain (BitVec 32) := Signal.pure 0#32
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 42#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 10#5
  let result := requantize acc scale shift
  LSpec.test "requant(0, *, *) = 0" (result.atTime 0 == 0#8)

def allTests : LSpec.TestSeq :=
  LSpec.group "Requantization" (
    testPositiveRequant ++
    testSmallPositive ++
    testNegativeRequant ++
    testZeroRequant
  )

end Sparkle.Examples.YOLOv8.Tests.TestRequantize
