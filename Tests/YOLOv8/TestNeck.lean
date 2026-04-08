/-
  Test: Neck Controller FSM
  Verifies FPN top-down and PAN bottom-up sequencing.
-/

import LSpec
import IP.YOLOv8.Neck

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8.Neck

namespace Sparkle.IP.YOLOv8.Tests.TestNeck

/-- Test initial FPN start: IDLE → FPN_UPSAMPLE. -/
def testFPNStart : IO LSpec.TestSeq := do
  let subOpDone : Signal defaultDomain Bool := Signal.pure false
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let ctrl ← neckControllerSimulate subOpDone start
  let phase := Signal.fst ctrl  -- BitVec 4
  let pathIdx := Signal.fst (Signal.snd ctrl)  -- BitVec 3
  return LSpec.group "Neck FPN Start" (
    LSpec.test "phase at t=0 is IDLE (0)" (phase.atTime 0 == 0#4) ++
    LSpec.test "phase at t=1 is FPN_UPSAMPLE (1)" (phase.atTime 1 == 1#4) ++
    LSpec.test "pathIdx at t=1 is 0" (pathIdx.atTime 1 == 0#3)
  )

/-- Test FPN upsample→concat→c2f sequence. -/
def testFPNSequence : IO LSpec.TestSeq := do
  -- subOpDone pulses: t=5 (upsample done), t=10 (concat done), t=15 (c2f done)
  let subOpDone : Signal defaultDomain Bool := ⟨fun t =>
    t == 5 || t == 10 || t == 15⟩
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let ctrl ← neckControllerSimulate subOpDone start
  let phase := Signal.fst ctrl
  return LSpec.group "Neck FPN Sequence" (
    LSpec.test "phase at t=1 is FPN_UPSAMPLE (1)" (phase.atTime 1 == 1#4) ++
    LSpec.test "phase at t=6 is FPN_CONCAT (2)" (phase.atTime 6 == 2#4) ++
    LSpec.test "phase at t=11 is FPN_C2F (3)" (phase.atTime 11 == 3#4) ++
    LSpec.test "phase at t=16 is FPN_UPSAMPLE (1) [2nd FPN step]" (phase.atTime 16 == 1#4)
  )

def allTests : IO LSpec.TestSeq := do
  let t1 ← testFPNStart
  let t2 ← testFPNSequence
  return LSpec.group "Neck Controller" (t1 ++ t2)

end Sparkle.IP.YOLOv8.Tests.TestNeck
