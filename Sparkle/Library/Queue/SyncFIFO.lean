/-
  Synchronous FIFO — Signal DSL Implementation

  Synthesizable depth-4 FIFO with Valid/Ready (Decoupled) interface,
  mirroring the proven spec in Sparkle.Library.Queue.QueueProps.

  Parameters:
  - Depth: 4 (addrWidth = 2)
  - Data width: 32 bits
  - Read: combinational (memoryComboRead)

  Properties proven on the spec:
  - No overflow / underflow (Safety)
  - Full blocks enqueue (Safety)
  - Empty blocks dequeue (Safety)
  - Simultaneous enq+deq preserves count (Correctness)
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

namespace Sparkle.Library.Queue.SyncFIFO

-- Depth-4 FIFO: addrWidth = 2, countWidth = 3
declare_signal_state SyncFIFOState
  | wrPtr : BitVec 2 := 0#2
  | rdPtr : BitVec 2 := 0#2
  | count : BitVec 3 := 0#3

/-- Loop body extracted for reuse by both synthesis and simulation paths -/
private def syncFIFOBody {dom : DomainConfig}
    (enqValid : Signal dom Bool)
    (deqReady : Signal dom Bool)
    (state : Signal dom SyncFIFOState)
    : Signal dom SyncFIFOState :=
  let wrPtr := SyncFIFOState.wrPtr state
  let rdPtr := SyncFIFOState.rdPtr state
  let count := SyncFIFOState.count state

  -- Full/empty conditions
  let full  := count === (4#3 : Signal dom _)
  let empty := count === (0#3 : Signal dom _)
  let enqReady := (fun x => !x) <$> full
  let deqValid := (fun x => !x) <$> empty
  let doEnq := enqValid &&& enqReady
  let doDeq := deqReady &&& deqValid

  -- Next pointers (wrap via 2-bit truncation)
  let wrPtrInc := (· + ·) <$> wrPtr <*> Signal.pure 1#2
  let rdPtrInc := (· + ·) <$> rdPtr <*> Signal.pure 1#2
  let nextWrPtr := Signal.mux doEnq wrPtrInc wrPtr
  let nextRdPtr := Signal.mux doDeq rdPtrInc rdPtr

  -- Next count: +1 for enq, -1 for deq, net 0 for simultaneous
  let countPlusOne  := (· + ·) <$> count <*> Signal.pure 1#3
  let countMinusOne := (· - ·) <$> count <*> Signal.pure 1#3
  let nextCount := hw_cond count
    | doEnq &&& ((fun x => !x) <$> doDeq) => countPlusOne
    | ((fun x => !x) <$> doEnq) &&& doDeq => countMinusOne

  bundleAll! [
    Signal.register 0#2 nextWrPtr,
    Signal.register 0#2 nextRdPtr,
    Signal.register 0#3 nextCount
  ]

/-- Build output from state signal (shared between synth and sim paths) -/
private def syncFIFOOutput {dom : DomainConfig}
    (enqValid : Signal dom Bool)
    (enqData : Signal dom (BitVec 32))
    (state : Signal dom SyncFIFOState)
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let wrPtr := SyncFIFOState.wrPtr state
  let rdPtr := SyncFIFOState.rdPtr state
  let count := SyncFIFOState.count state

  -- FIFO data buffer (combo read for same-cycle dequeue data)
  let full  := count === (4#3 : Signal dom _)
  let enqReady := (fun x => !x) <$> full
  let doEnq := enqValid &&& enqReady
  let deqData := Signal.memoryComboRead wrPtr enqData doEnq rdPtr

  -- Output: (enqReady, deqValid, deqData) encoded as 32-bit each
  let empty := count === (0#3 : Signal dom _)
  let deqValid := (fun x => !x) <$> empty
  let enqReadyBV := Signal.mux enqReady (Signal.pure 1#32) (Signal.pure 0#32)
  let deqValidBV := Signal.mux deqValid (Signal.pure 1#32) (Signal.pure 0#32)
  bundleAll! [enqReadyBV, deqValidBV, deqData]

def syncFIFO {dom : DomainConfig}
    (enqValid : Signal dom Bool)
    (enqData : Signal dom (BitVec 32))
    (deqReady : Signal dom Bool)
    : Signal dom (BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop (syncFIFOBody enqValid deqReady)
  syncFIFOOutput enqValid enqData state

-- Verify synthesis
#synthesizeVerilog syncFIFO

/-- Simulation version using loopMemo to avoid stack overflow -/
def syncFIFOSim
    (enqValid : Signal defaultDomain Bool)
    (enqData : Signal defaultDomain (BitVec 32))
    (deqReady : Signal defaultDomain Bool)
    : IO (Signal defaultDomain (BitVec 32 × BitVec 32 × BitVec 32)) := do
  let state ← Signal.loopMemo (syncFIFOBody enqValid deqReady)
  pure (syncFIFOOutput enqValid enqData state)

end Sparkle.Library.Queue.SyncFIFO
