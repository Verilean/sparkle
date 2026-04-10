/-
  BitNet BitLinear — Time-Multiplexed Core — Signal DSL

  Sequential ternary BitLinear: processes one weight-activation pair per clock.
  Uses Signal.loop FSM + BRAM for weight storage.

  FSM states:
    IDLE (0): waiting for `start` pulse
    ACCUMULATE (1): processing one element per clock, dim cycles total
    DONE (2): result ready, stays until next `start`

  Interface:
    start      : Signal dom Bool          -- pulse to begin computation
    activations: Signal dom (BitVec 32)   -- input activation (changes each cycle)
    actAddr    : Signal dom (BitVec addrW) -- address to read activation from external memory
    result     : Signal dom (BitVec 32)   -- accumulated output (valid when done)
    done       : Signal dom Bool          -- high when computation complete
    busy       : Signal dom Bool          -- high during accumulation

  Weight storage:
    Weights are stored in BRAM as 2-bit codes:
      0b10 = +1, 0b00 = -1, 0b01 = 0
    The FSM reads one weight per clock and accumulates.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.BitNet.BitLinear

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Time-multiplexed BitLinear core.
    `dim` is the number of elements to accumulate.
    `weightWriteAddr/Data/Enable` are used to load weights into BRAM before computation.
    `activation` is the current activation value (caller must supply one per clock during ACCUMULATE).
    Returns (result, done, busy, counter) as a bundled signal. -/
def bitLinearTimeMux
    (dim : Nat)
    -- Weight BRAM write port (for initialization)
    (weightWriteAddr : Signal dom (BitVec 16))
    (weightWriteData : Signal dom (BitVec 2))
    (weightWriteEn : Signal dom Bool)
    -- Computation control
    (start : Signal dom Bool)
    (activation : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) ×  -- result
      Signal dom Bool ×          -- done
      Signal dom Bool ×          -- busy
      Signal dom (BitVec 16)     -- current counter (= activation address)
    :=
  -- Shorthand for typed constant signals
  let p2 (v : BitVec 2) : Signal dom (BitVec 2) := Signal.pure v
  let p16 (v : BitVec 16) : Signal dom (BitVec 16) := Signal.pure v
  let p32 (v : BitVec 32) : Signal dom (BitVec 32) := Signal.pure v
  let pf : Signal dom Bool := Signal.pure false
  -- Bool AND as mux: a && b = mux a b false
  let boolAnd (a b : Signal dom Bool) : Signal dom Bool := Signal.mux a b pf

  -- State via Signal.loop: (phase, counter, accumulator, result_latch)
  let state := Signal.loop (α := BitVec 2 × (BitVec 16 × (BitVec 32 × BitVec 32))) fun self =>
    hw_let (phase, rest1) := self;
    hw_let (counter, rest2) := rest1;
    hw_let (acc, resultLatch) := rest2;

    -- Weight BRAM: written externally, read by FSM at `counter` address
    let weightCode := Signal.memoryComboRead weightWriteAddr weightWriteData weightWriteEn counter

    -- Decode ternary weight
    let isPlus1  : Signal dom Bool := weightCode === p2 0b10#2
    let isMinus1 : Signal dom Bool := weightCode === p2 0b00#2

    -- MAC: w × activation (ternary: just add/sub/skip)
    let macResult : Signal dom (BitVec 32) :=
      Signal.mux isPlus1 (acc + activation)
        (Signal.mux isMinus1 (acc - activation) acc)

    -- Dimension limit
    let dimLimit : Signal dom (BitVec 16) := p16 (BitVec.ofNat 16 (dim - 1))
    let atEnd : Signal dom Bool := counter === dimLimit

    -- FSM next-state logic (phase: 0=IDLE, 1=ACCUMULATE, 2=DONE)
    let isIdle : Signal dom Bool := phase === p2 0#2
    let isAccum : Signal dom Bool := phase === p2 1#2
    let isDone : Signal dom Bool := phase === p2 2#2

    let startIdle := boolAnd isIdle start
    let endAccum := boolAnd isAccum atEnd
    let restartDone := boolAnd isDone start

    let nextPhase : Signal dom (BitVec 2) :=
      Signal.mux startIdle (p2 1#2)
        (Signal.mux endAccum (p2 2#2)
          (Signal.mux restartDone (p2 1#2) phase))

    let counterInc : Signal dom (BitVec 16) := counter + p16 1#16
    let nextCounter : Signal dom (BitVec 16) :=
      Signal.mux startIdle (p16 0#16)
        (Signal.mux isAccum counterInc
          (Signal.mux restartDone (p16 0#16) counter))

    let nextAcc : Signal dom (BitVec 32) :=
      Signal.mux startIdle (p32 0#32)
        (Signal.mux isAccum macResult
          (Signal.mux restartDone (p32 0#32) acc))

    let nextResult : Signal dom (BitVec 32) :=
      Signal.mux endAccum macResult resultLatch

    bundleAll! [
      Signal.register 0#2 nextPhase,
      Signal.register 0#16 nextCounter,
      Signal.register 0#32 nextAcc,
      Signal.register 0#32 nextResult
    ]

  -- Extract outputs from state
  hw_let (phase, rest1) := state;
  hw_let (counter, rest2) := rest1;
  hw_let (_acc, resultLatch) := rest2;

  let done := phase === Signal.pure 2#2
  let busy := phase === Signal.pure 1#2

  (resultLatch, done, busy, counter)

end Sparkle.IP.BitNet.BitLinear
