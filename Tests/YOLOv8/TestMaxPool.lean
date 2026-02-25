/-
  Test: 2x2 Max Pooling
-/

import LSpec
import Examples.YOLOv8.Primitives.MaxPool

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8.Primitives.MaxPool

namespace Sparkle.Examples.YOLOv8.Tests.TestMaxPool

/-- Test max pool with all positive values. -/
def testAllPositive : LSpec.TestSeq :=
  let a : Signal defaultDomain (BitVec 8) := Signal.pure 10#8
  let b : Signal defaultDomain (BitVec 8) := Signal.pure 20#8
  let c : Signal defaultDomain (BitVec 8) := Signal.pure 30#8
  let d : Signal defaultDomain (BitVec 8) := Signal.pure 40#8
  let result := maxPool2x2 a b c d
  LSpec.test "max(10,20,30,40) = 40" (result.atTime 0 == 40#8)

/-- Test max pool with mixed positive/negative values. -/
def testMixed : LSpec.TestSeq :=
  let a : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-5))
  let b : Signal defaultDomain (BitVec 8) := Signal.pure 3#8
  let c : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-10))
  let d : Signal defaultDomain (BitVec 8) := Signal.pure 7#8
  let result := maxPool2x2 a b c d
  LSpec.test "max(-5,3,-10,7) = 7" (result.atTime 0 == 7#8)

/-- Test max pool with all negative values. -/
def testAllNegative : LSpec.TestSeq :=
  let a : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-100))
  let b : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-50))
  let c : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-30))
  let d : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-80))
  let result := maxPool2x2 a b c d
  LSpec.test "max(-100,-50,-30,-80) = -30" (result.atTime 0 == BitVec.ofInt 8 (-30))

/-- Test max pool with identical values. -/
def testIdentical : LSpec.TestSeq :=
  let v : Signal defaultDomain (BitVec 8) := Signal.pure 42#8
  let result := maxPool2x2 v v v v
  LSpec.test "max(42,42,42,42) = 42" (result.atTime 0 == 42#8)

def allTests : LSpec.TestSeq :=
  LSpec.group "Max Pooling 2x2" (
    testAllPositive ++
    testMixed ++
    testAllNegative ++
    testIdentical
  )

end Sparkle.Examples.YOLOv8.Tests.TestMaxPool
