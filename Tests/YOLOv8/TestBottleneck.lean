/-
  Test: Bottleneck Controller FSM
  Verifies state transitions: IDLE→CONV1→CONV2→DONE→IDLE
-/

import LSpec
import IP.YOLOv8.Blocks.Bottleneck

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8.Blocks.Bottleneck

namespace Sparkle.IP.YOLOv8.Tests.TestBottleneck

/-- Test FSM transitions with convDone pulses. -/
def testFSMTransitions : IO LSpec.TestSeq := do
  -- convDone pulses at t=5 (conv1 done) and t=10 (conv2 done)
  let convResult : Signal defaultDomain (BitVec 8) := Signal.pure 42#8
  let convDone : Signal defaultDomain Bool := ⟨fun t => t == 5 || t == 10⟩
  let inputVal : Signal defaultDomain (BitVec 8) := Signal.pure 10#8
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let addResidual : Signal defaultDomain Bool := Signal.pure true

  let ctrl ← bottleneckControllerSimulate convResult convDone inputVal start addResidual
  let phase := Signal.snd (Signal.snd ctrl)  -- BitVec 2

  -- t=0: start fires, FSM should be in IDLE (register hasn't updated yet)
  -- t=1: FSM transitions to CONV1 (1)
  -- t=6: convDone at t=5 causes transition to CONV2 (2)
  -- t=11: convDone at t=10 causes transition to DONE (3)
  -- t=12: DONE → IDLE (0)
  return LSpec.group "Bottleneck FSM" (
    LSpec.test "phase at t=0 is IDLE (0)" (phase.atTime 0 == 0#2) ++
    LSpec.test "phase at t=1 is CONV1 (1)" (phase.atTime 1 == 1#2) ++
    LSpec.test "phase at t=6 is CONV2 (2)" (phase.atTime 6 == 2#2) ++
    LSpec.test "phase at t=11 is DONE (3)" (phase.atTime 11 == 3#2) ++
    LSpec.test "phase at t=12 is IDLE (0)" (phase.atTime 12 == 0#2)
  )

def allTests : IO LSpec.TestSeq := do
  let t1 ← testFSMTransitions
  return LSpec.group "Bottleneck Controller" t1

end Sparkle.IP.YOLOv8.Tests.TestBottleneck
