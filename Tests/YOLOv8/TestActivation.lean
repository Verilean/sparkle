/-
  Test: Activation Functions (ReLU, SiLU)
-/

import LSpec
import IP.YOLOv8.Primitives.Activation

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8.Primitives.Activation

namespace Sparkle.IP.YOLOv8.Tests.TestActivation

/-- Test ReLU: positive values pass through. -/
def testReluPositive : LSpec.TestSeq :=
  let x : Signal defaultDomain (BitVec 8) := Signal.pure 42#8
  let result := relu x
  LSpec.test "relu(42) = 42" (result.atTime 0 == 42#8)

/-- Test ReLU: negative values become zero. -/
def testReluNegative : LSpec.TestSeq :=
  let x : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 (-10))
  let result := relu x
  LSpec.test "relu(-10) = 0" (result.atTime 0 == 0#8)

/-- Test ReLU: zero passes through. -/
def testReluZero : LSpec.TestSeq :=
  let x : Signal defaultDomain (BitVec 8) := Signal.pure 0#8
  let result := relu x
  LSpec.test "relu(0) = 0" (result.atTime 0 == 0#8)

/-- Test ReLU: max positive value. -/
def testReluMax : LSpec.TestSeq :=
  let x : Signal defaultDomain (BitVec 8) := Signal.pure 127#8
  let result := relu x
  LSpec.test "relu(127) = 127" (result.atTime 0 == 127#8)

/-- Test ReLU: most negative value. -/
def testReluMinNeg : LSpec.TestSeq :=
  let x : Signal defaultDomain (BitVec 8) := Signal.pure 128#8  -- -128 in signed
  let result := relu x
  LSpec.test "relu(-128) = 0" (result.atTime 0 == 0#8)

def allTests : LSpec.TestSeq :=
  LSpec.group "Activation Functions" (
    LSpec.group "ReLU" (
      testReluPositive ++
      testReluNegative ++
      testReluZero ++
      testReluMax ++
      testReluMinNeg
    )
  )

end Sparkle.IP.YOLOv8.Tests.TestActivation
