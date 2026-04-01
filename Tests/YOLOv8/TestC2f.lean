/-
  Test: C2f Controller FSM
  Verifies state transitions: IDLE→SPLIT→BOTTLENECK(×N)→CONCAT→MERGE→DONE→IDLE
-/

import LSpec
import IP.YOLOv8.Blocks.C2f

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.YOLOv8.Blocks.C2f

namespace Sparkle.IP.YOLOv8.Tests.TestC2f

/-- Test FSM with 2 bottlenecks. -/
def testFSMWithTwoBottlenecks : IO LSpec.TestSeq := do
  -- subOpDone pulses at specific times to advance through phases
  -- t=5: split done, t=10: bn0 done, t=15: bn1 done, t=20: concat done, t=25: merge done
  let subOpDone : Signal defaultDomain Bool := ⟨fun t =>
    t == 5 || t == 10 || t == 15 || t == 20 || t == 25⟩
  let start : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let numBn : Signal defaultDomain (BitVec 4) := Signal.pure 2#4

  let ctrl ← c2fControllerSimulate subOpDone start numBn
  let phase := Signal.fst ctrl  -- BitVec 3

  -- t=0: IDLE, t=1: SPLIT(1), t=6: BOTTLENECK(2), t=11: still BOTTLENECK(2),
  -- t=16: CONCAT(3), t=21: MERGE(4), t=26: DONE(5), t=27: IDLE(0)
  return LSpec.group "C2f FSM" (
    LSpec.test "phase at t=0 is IDLE (0)" (phase.atTime 0 == 0#3) ++
    LSpec.test "phase at t=1 is SPLIT (1)" (phase.atTime 1 == 1#3) ++
    LSpec.test "phase at t=6 is BOTTLENECK (2)" (phase.atTime 6 == 2#3) ++
    LSpec.test "phase at t=16 is CONCAT (3)" (phase.atTime 16 == 3#3) ++
    LSpec.test "phase at t=21 is MERGE (4)" (phase.atTime 21 == 4#3) ++
    LSpec.test "phase at t=26 is DONE (5)" (phase.atTime 26 == 5#3)
  )

def allTests : IO LSpec.TestSeq := do
  let t1 ← testFSMWithTwoBottlenecks
  return LSpec.group "C2f Controller" t1

end Sparkle.IP.YOLOv8.Tests.TestC2f
