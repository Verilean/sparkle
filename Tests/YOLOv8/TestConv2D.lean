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

/-- Test single MAC operation: w=2, a=3, bias=0 → 2*3=6 → requant(6,1,0)=6.
    We set macCount=1 so the engine does exactly one MAC then requantizes. -/
def testSingleMAC : LSpec.TestSeq :=
  -- Weight = 2 (INT4), activation = 3 (INT8), bias = 0, scale = 1, shift = 0
  let weight : Signal defaultDomain (BitVec 4) := Signal.pure 2#4
  let act : Signal defaultDomain (BitVec 8) := Signal.pure 3#8
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 0#5
  let bias : Signal defaultDomain (BitVec 32) := Signal.pure 0#32
  let macCount : Signal defaultDomain (BitVec 16) := Signal.pure 1#16

  -- Start at t=0
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let engine := conv2DEngine weight act scale shift bias start macCount

  let result := Signal.fst engine
  let done := Signal.snd engine

  -- Engine FSM: t=0 start (IDLE→ACC), t=1 MAC (ACC→REQUANT), t=2 (REQUANT→OUTPUT), t=3 done
  -- Result should be available at t=3 (done pulse)
  LSpec.test "conv2d single MAC: done at t=3" (done.atTime 3 == true) ++
  LSpec.test "conv2d single MAC: result=6" (result.atTime 3 == 6#8)

/-- Test with bias: w=1, a=10, bias=5 → 1*10+5=15. -/
def testWithBias : LSpec.TestSeq :=
  let weight : Signal defaultDomain (BitVec 4) := Signal.pure 1#4
  let act : Signal defaultDomain (BitVec 8) := Signal.pure 10#8
  let scale : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let shift : Signal defaultDomain (BitVec 5) := Signal.pure 0#5
  let bias : Signal defaultDomain (BitVec 32) := Signal.pure 5#32
  let macCount : Signal defaultDomain (BitVec 16) := Signal.pure 1#16
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let engine := conv2DEngine weight act scale shift bias start macCount
  let result := Signal.fst engine

  LSpec.test "conv2d with bias: result=15" (result.atTime 3 == 15#8)

def allTests : LSpec.TestSeq :=
  LSpec.group "Conv2D MAC Engine" (
    testSingleMAC ++
    testWithBias
  )

end Sparkle.Examples.YOLOv8.Tests.TestConv2D
