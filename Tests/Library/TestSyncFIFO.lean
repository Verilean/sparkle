/-
  SyncFIFO Tests — LSpec Tests

  Tests the synchronous FIFO behavior:
  - Enqueue phase: fill FIFO with 4 items, verify enqReady
  - Dequeue phase: drain FIFO, verify FIFO order and deqValid
  - Full/empty conditions
  - Simultaneous enqueue + dequeue

  Uses syncFIFOSim (loopMemo-backed) to avoid stack overflow.
-/

import Sparkle
import Sparkle.Library.Queue.SyncFIFO
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Library.Queue.SyncFIFO
open LSpec

namespace Sparkle.Tests.Library.TestSyncFIFO

/-- Helper: extract enqReady (first 32-bit field) -/
private def getEnqReady (output : Signal defaultDomain (BitVec 32 × BitVec 32 × BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  output.map (·.1)

/-- Helper: extract deqValid (second 32-bit field) -/
private def getDeqValid (output : Signal defaultDomain (BitVec 32 × BitVec 32 × BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  output.map (·.2.1)

/-- Helper: extract deqData (third 32-bit field) -/
private def getDeqData (output : Signal defaultDomain (BitVec 32 × BitVec 32 × BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  output.map (·.2.2)

/-!
## Test Scenario: Fill then Drain

Timeline (registers have 1-cycle delay from Signal.loop):
- t=0: enqValid=true, enqData=0xA0  → registers output initial state (count=0)
- t=1: enqValid=true, enqData=0xA1  → count=1 (enq at t=0 took effect)
- t=2: enqValid=true, enqData=0xA2  → count=2
- t=3: enqValid=true, enqData=0xA3  → count=3
- t=4: enqValid=false, deqReady=true → count=4 (full), enqReady=0
- t=5: deqReady=true                 → count=3, deqData=0xA0
- t=6: deqReady=true                 → count=2, deqData=0xA1
- t=7: deqReady=true                 → count=1, deqData=0xA2
- t=8: deqReady=false                → count=0 (empty), deqValid=0
-/

def syncFIFOTests : IO TestSeq := do
  -- Scenario 1: Fill then drain
  let enqValid1 : Signal defaultDomain Bool := ⟨fun t => t < 4⟩
  let enqData1 : Signal defaultDomain (BitVec 32) :=
    ⟨fun t => BitVec.ofNat 32 (0xA0 + t)⟩
  let deqReady1 : Signal defaultDomain Bool := ⟨fun t => t ≥ 4⟩

  let output1 ← syncFIFOSim enqValid1 enqData1 deqReady1
  let enqReady1 := getEnqReady output1
  let deqValid1 := getDeqValid output1
  let deqData1 := getDeqData output1

  -- Scenario 2: Simultaneous enqueue and dequeue (steady state)
  let enqValid2 : Signal defaultDomain Bool := ⟨fun _ => true⟩
  let enqData2 : Signal defaultDomain (BitVec 32) :=
    ⟨fun t => BitVec.ofNat 32 (0xB0 + t)⟩
  let deqReady2 : Signal defaultDomain Bool := ⟨fun t => t ≥ 2⟩

  let output2 ← syncFIFOSim enqValid2 enqData2 deqReady2
  let enqReady2 := getEnqReady output2
  let deqValid2 := getDeqValid output2

  pure $
    group "SyncFIFO" (
      group "Initial State" (
        test "enqReady=1 at t=0 (empty FIFO)" (enqReady1.atTime 0 == 1#32) $
        test "deqValid=0 at t=0 (empty FIFO)" (deqValid1.atTime 0 == 0#32)
      ) ++
      group "Enqueue Phase" (
        test "enqReady=1 at t=1 (count=1)" (enqReady1.atTime 1 == 1#32) $
        test "enqReady=1 at t=2 (count=2)" (enqReady1.atTime 2 == 1#32) $
        test "enqReady=1 at t=3 (count=3)" (enqReady1.atTime 3 == 1#32)
      ) ++
      group "Full Condition" (
        test "enqReady=0 at t=4 (full)" (enqReady1.atTime 4 == 0#32) $
        test "deqValid=1 at t=4 (has data)" (deqValid1.atTime 4 == 1#32)
      ) ++
      group "Dequeue Phase — FIFO Order" (
        test "deqData=0xA0 at t=4 (first in)" (deqData1.atTime 4 == 0xA0#32) $
        test "deqData=0xA1 at t=5" (deqData1.atTime 5 == 0xA1#32) $
        test "deqData=0xA2 at t=6" (deqData1.atTime 6 == 0xA2#32) $
        test "deqData=0xA3 at t=7 (last in)" (deqData1.atTime 7 == 0xA3#32)
      ) ++
      group "Empty After Drain" (
        test "deqValid=0 at t=8 (empty)" (deqValid1.atTime 8 == 0#32) $
        test "enqReady=1 at t=8 (room)" (enqReady1.atTime 8 == 1#32)
      ) ++
      group "Simultaneous Enq+Deq" (
        test "enqReady=1 during simultaneous ops (t=3)" (enqReady2.atTime 3 == 1#32) $
        test "deqValid=1 during simultaneous ops (t=3)" (deqValid2.atTime 3 == 1#32)
      )
    )

end Sparkle.Tests.Library.TestSyncFIFO
