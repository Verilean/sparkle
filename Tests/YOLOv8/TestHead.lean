/-
  Test: Head Controller FSM
  Verifies 3-scale detection head sequencing.
-/

import LSpec
import IP.YOLOv8.Head

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8.Head

namespace Sparkle.IP.YOLOv8.Tests.TestHead

/-- Test initial start: IDLE → BBOX_CONV. -/
def testStartTransition : IO LSpec.TestSeq := do
  let subOpDone : Signal defaultDomain Bool := Signal.pure false
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let ctrl ← headControllerSimulate subOpDone start
  let phase := Signal.fst ctrl
  let scaleIdx := Signal.fst (Signal.snd ctrl)
  return LSpec.group "Head Start" (
    LSpec.test "phase at t=0 is IDLE (0)" (phase.atTime 0 == 0#4) ++
    LSpec.test "phase at t=1 is BBOX_CONV (1)" (phase.atTime 1 == 1#4) ++
    LSpec.test "scaleIdx at t=1 is 0" (scaleIdx.atTime 1 == 0#2)
  )

/-- Test bbox conv sequencing (3 convs: 0,1,2). -/
def testBboxConvs : IO LSpec.TestSeq := do
  -- subOpDone pulses for 3 bbox convs: t=5, t=10, t=15
  let subOpDone : Signal defaultDomain Bool := ⟨fun t =>
    t == 5 || t == 10 || t == 15⟩
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let ctrl ← headControllerSimulate subOpDone start
  let phase := Signal.fst ctrl
  return LSpec.group "Head Bbox Convs" (
    LSpec.test "phase at t=1 is BBOX_CONV (1)" (phase.atTime 1 == 1#4) ++
    LSpec.test "phase at t=6 is BBOX_CONV (1) [2nd conv]" (phase.atTime 6 == 1#4) ++
    LSpec.test "phase at t=11 is BBOX_CONV (1) [3rd conv]" (phase.atTime 11 == 1#4) ++
    LSpec.test "phase at t=16 is CLS_CONV (2)" (phase.atTime 16 == 2#4)
  )

def allTests : IO LSpec.TestSeq := do
  let t1 ← testStartTransition
  let t2 ← testBboxConvs
  return LSpec.group "Head Controller" (t1 ++ t2)

end Sparkle.IP.YOLOv8.Tests.TestHead
