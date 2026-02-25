/-
  Test: Conv2D MAC Engine
  Verifies the sequential MAC engine with simple known inputs.
-/

import LSpec
import Examples.YOLOv8.Primitives.Conv2DEngine

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8.Primitives.Conv2DEngine

namespace Sparkle.Examples.YOLOv8.Tests.TestConv2D

/-- Test single MAC operation: w=2, a=3, bias=0 → dequant(2)=2, 2*3=6 → requant(6,1,0)=6. -/
def testSingleMAC : IO LSpec.TestSeq := do
  let weight : Signal defaultDomain (BitVec 4) := Signal.pure 2#4
  let act : Signal defaultDomain (BitVec 8) := Signal.pure 3#8
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 0#5
  let bias : Signal defaultDomain (BitVec 32) := Signal.pure 0#32
  let macCount : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let engine ← conv2DEngineSimulate weight act scale shift bias start macCount
  let result := Signal.fst engine
  let done := Signal.snd engine
  return LSpec.test "conv2d single MAC: done at t=4" (done.atTime 4 == true) ++
    LSpec.test "conv2d single MAC: result=6" (result.atTime 4 == 6#8)

/-- Test with bias: w=1, a=10, bias=5 → 1*10+5=15. -/
def testWithBias : IO LSpec.TestSeq := do
  let weight : Signal defaultDomain (BitVec 4) := Signal.pure 1#4
  let act : Signal defaultDomain (BitVec 8) := Signal.pure 10#8
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 0#5
  let bias : Signal defaultDomain (BitVec 32) := Signal.pure 5#32
  let macCount : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let engine ← conv2DEngineSimulate weight act scale shift bias start macCount
  let result := Signal.fst engine
  return LSpec.test "conv2d with bias: result=15" (result.atTime 4 == 15#8)

def allTests : IO LSpec.TestSeq := do
  let t1 ← testSingleMAC
  let t2 ← testWithBias
  return LSpec.group "Conv2D MAC Engine" (t1 ++ t2)

end Sparkle.Examples.YOLOv8.Tests.TestConv2D
